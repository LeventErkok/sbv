-----------------------------------------------------------------------------
-- |
-- Module    : Data.SBV.TP.Utils
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Various theorem-proving machinery.
-----------------------------------------------------------------------------

{-# LANGUAGE DataKinds                  #-}
{-# LANGUAGE DeriveAnyClass             #-}
{-# LANGUAGE DeriveGeneric              #-}
{-# LANGUAGE DerivingStrategies         #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE NamedFieldPuns             #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE TupleSections              #-}
{-# LANGUAGE TypeAbstractions           #-}
{-# LANGUAGE TypeApplications           #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module Data.SBV.TP.Utils (
         TP, runTP, runTPWith, Proof(..), ProofObj(..), assumptionFromProof, sorry, quickCheckProof, noTermCheckProof
       , startTP, finishTP, getTPState, getTPConfig, setTPConfig, tpGetNextUnique, TPState(..), TPStats(..), RootOfTrust(..)
       , TPProofContext(..), message, updStats, rootOfTrust, concludeModulo
       , ProofTree(..), TPUnique(..), showProofTree, showProofTreeHTML
       , addToProofCache, lookupProofCache, returnCachedProof
       , tpQuiet, tpRibbon, tpAsms, tpStats
       , measureLemma, measureLemmaWith
       ) where

import Control.Monad        (unless)
import Control.Monad.Reader (ReaderT, runReaderT, MonadReader, ask, liftIO)
import Control.Monad.Trans  (MonadIO)

import Data.Generics (everywhere, mkT)

import Data.Time (NominalDiffTime)

import Data.Tree
import Data.Tree.View

import Data.Proxy
import Data.Typeable (typeOf, TypeRep)

import Data.Char (isSpace)
import Data.List (intercalate, isPrefixOf, isSuffixOf, isInfixOf, nub, nubBy, sort, dropWhileEnd)
import Data.Int  (Int64)

import Data.SBV.Utils.Lib (unQuote)

import System.IO     (hFlush, stdout)
import System.Random (randomIO)

import Data.SBV.Core.Data      (SBool, sTrue, Forall(..), QuantifiedBool, quantifiedBool, SBV(..), SV(..), NodeId(..), SBVExpr(..), SBVPgm(..), Op(..), CV(..))
import Data.SBV.Core.Model     (label, MeasureHelper(..))
import Data.SBV.Core.Symbolic  (SMTConfig, TPOptions(..), State(..), mkNewState, svToSV, SBVRunMode(..), globalSBVContext)
import Data.SBV.Provers.Prover (defaultSMTCfg, SMTConfig(..))

import Data.SBV.Utils.TDiff (showTDiff, timeIf)
import Control.DeepSeq (NFData(rnf))

import Data.Foldable (toList)
import Data.IORef

import GHC.Generics
import Data.Dynamic

import qualified Data.Map as Map
import Data.Map (Map)

import qualified Data.Set as Set
import Data.Set (Set)

-- | Various statistics we collect
data TPStats = TPStats { noOfCheckSats :: Int
                       , solverElapsed :: NominalDiffTime
                       , qcElapsed     :: NominalDiffTime
                       }

-- | Extra state we carry in a TP context
data TPState = TPState { stats               :: IORef TPStats
                       , proofCache          :: IORef (Map (PropFingerprint, TypeRep) [ProofObj])
                       , config              :: IORef SMTConfig
                       , inRecallContext     :: IORef Int
                       , measuresVerified    :: IORef (Set String)
                       , productiveVerified  :: IORef (Set String)
                       , measuresEncountered :: IORef (Set String)
                       }

-- | Monad for running TP proofs in.
newtype TP a = TP (ReaderT TPState IO a)
            deriving newtype (Applicative, Functor, Monad, MonadIO, MonadReader TPState, MonadFail)

-- | Extract the integer node ID from an SV.
svIntId :: SV -> Int
svIntId (SV _ (NodeId (_, _, i))) = i

-- | Zero out the SBVContext in an SV, keeping only the kind and integer node ID.
-- Used to normalize 'Op' values for fingerprinting.
zeroSV :: SV -> SV
zeroSV (SV k (NodeId (_, mb, i))) = SV k (NodeId (globalSBVContext, mb, i))

-- | Zero out all embedded SBVContext values inside an 'Op' using SYB generic traversal.
-- This automatically handles all current and future Op constructors that embed SV's.
zeroContextInOp :: Op -> Op
zeroContextInOp = everywhere (mkT zeroSV)

-- | Fingerprint of a proposition's symbolic expression DAG.
-- Computed by evaluating 'quantifiedBool' in a fresh State and extracting
-- the expression program (with embedded SV contexts zeroed out via SYB),
-- the constant map (mapping constant values to their SV int IDs), and the final result SV.
-- Two identical propositions evaluated in identically-initialized States produce
-- identical fingerprints. Different propositions diverge somewhere in variable creation,
-- expression construction, or hash-consing, producing different fingerprints.
newtype PropFingerprint = PropFingerprint ([(CV, Int)], [(Int, Op, [Int])], Int)
  deriving (Eq, Ord)

-- | Compute the fingerprint of a proposition by evaluating it in a fresh
-- lightweight State (no solver connection needed). The State is created via
-- 'mkNewState' with 'LambdaGen' mode, which initializes all counters identically
-- without starting a solver process.
propFingerprint :: QuantifiedBool a => a -> IO PropFingerprint
propFingerprint prop = do
  st  <- mkNewState defaultSMTCfg (LambdaGen Nothing)
  sv  <- svToSV st (unSBV (quantifiedBool prop))
  pgm <- readIORef (spgm st)
  cm  <- readIORef (rconstMap st)
  let entries = [ (svIntId target, zeroContextInOp op, map svIntId args)
                | (target, SBVApp op args) <- toList (pgmAssignments pgm)
                ]
      consts  = [(c, svIntId s) | (c, s) <- Map.toAscList cm]
  pure $ PropFingerprint (consts, entries, svIntId sv)

-- | After proving a proposition, add the proof to the cache for future recall lookups.
addToProofCache :: forall a. (Typeable a, QuantifiedBool a) => a -> ProofObj -> TP ()
addToProofCache prop prf = do
  TPState{proofCache} <- getTPState
  fp <- liftIO $ propFingerprint prop
  let key = (fp, typeOf (Proxy @a))
  liftIO $ modifyIORef' proofCache $ Map.insertWith (\_ old -> old ++ [prf]) key [prf]

-- | Look up a cached proof for the given proposition. Only succeeds when in recall context
-- (i.e., called from within a recall wrapper). On cache hit, the returned ProofObj has
-- its 'aliases' field populated with the names of other proofs of the same proposition.
lookupProofCache :: forall a. (Typeable a, QuantifiedBool a) => a -> TP (Maybe ProofObj)
lookupProofCache prop = do
  TPState{proofCache, inRecallContext} <- getTPState
  inRecall <- liftIO $ readIORef inRecallContext
  if inRecall == 0
     then pure Nothing
     else do fp <- liftIO $ propFingerprint prop
             let key = (fp, typeOf (Proxy @a))
             cache <- liftIO $ readIORef proofCache
             pure $ case Map.lookup key cache of
               Nothing     -> Nothing
               Just []     -> Nothing
               Just (p:ps) -> Just p { aliases = [proofName q | q <- ps] }

-- | Return a cached proof, printing a brief "Q.E.D." line with optional "a.k.a." annotation.
returnCachedProof :: SMTConfig -> String -> ProofObj -> TP (Proof a)
returnCachedProof cfg nm prf = do
   let aka    = filter (/= nm) $ nub $ proofName prf : aliases prf
       prf'   = prf { proofName = nm, wasCached = True, aliases = aka }
       akaStr | null aka  = ""
              | True      = " (a.k.a. " ++ intercalate ", " aka ++ ")"
   tab <- liftIO $ startTP cfg False "Cached" 0 (TPProofOneShot nm [])
   liftIO $ finishTP cfg ("Q.E.D." ++ concludeModulo (dependencies prf) ++ akaStr) (tab, Nothing) []
   pure $ Proof prf'

-- | The context in which we make a check-sat call
data TPProofContext = TPProofOneShot String      -- ^ A one shot proof, with string containing its name
                                     [ProofObj]  -- ^ Helpers used (latter only used for cex generation)
                    | TPProofStep    Bool        -- ^ A proof step. If Bool is true, then these are the assumptions for that step
                                     String      -- ^ Name of original goal
                                     [String]    -- ^ The helper "strings" given by the user
                                     [String]    -- ^ The step name, i.e., the name of the branch in the proof tree

-- | Run a TP proof, using the default configuration.
runTP :: TP a -> IO a
runTP = runTPWith defaultSMTCfg

-- | Run a TP proof, using the given configuration.
runTPWith :: SMTConfig -> TP a -> IO a
runTPWith cfg@SMTConfig{tpOptions = TPOptions{printStats}} (TP f) = do
   rStats       <- newIORef $ TPStats { noOfCheckSats = 0, solverElapsed = 0, qcElapsed = 0 }
   rCache       <- newIORef Map.empty
   rCfg         <- newIORef cfg
   rRecall      <- newIORef (0 :: Int)
   rMeasures    <- newIORef Set.empty
   rProductive  <- newIORef Set.empty
   rEncountered <- newIORef Set.empty
   (mbT, r) <- timeIf printStats $ runReaderT f TPState { config               = rCfg
                                                         , stats               = rStats
                                                         , proofCache          = rCache
                                                         , inRecallContext     = rRecall
                                                         , measuresVerified    = rMeasures
                                                         , productiveVerified  = rProductive
                                                         , measuresEncountered = rEncountered
                                                         }

   -- Print verified measures and productive functions
   verified    <- readIORef rMeasures
   productive  <- readIORef rProductive
   encountered <- readIORef rEncountered

   unless (Set.null verified)   $ printMeasures   cfg (Set.toAscList verified)
   unless (Set.null productive) $ printProductive cfg (Set.toAscList productive)

   -- Belt-and-suspenders: make sure all encountered measures have been verified.
   -- Exclude functions in measuresBeingVerified: those are being verified by an outer caller
   -- (e.g., when a measureLemma proof uses the function whose measure is being checked).
   let beingVerified = measuresBeingVerified (tpOptions cfg)
       missed = encountered `Set.difference` verified `Set.difference` productive `Set.difference` beingVerified

   unless (Set.null missed) $
     error $ "SBV.runTP: Internal error: The following functions have termination measures that were encountered but not verified: "
           ++ intercalate ", " (Set.toAscList missed)

   case mbT of
     Nothing -> pure ()
     Just t  -> do TPStats noOfCheckSats solverTime qcElapsed <- readIORef rStats

                   let stats = [ ("SBV",       showTDiff (t - solverTime - qcElapsed))
                               , ("Solver",    showTDiff solverTime)
                               , ("QC",        showTDiff qcElapsed)
                               , ("Total",     showTDiff t)
                               , ("Decisions", show noOfCheckSats)
                               ]

                   message cfg $ '[' : intercalate ", " [k ++ ": " ++ v | (k, v) <- stats] ++ "]\n"
   pure r

-- | get the state
getTPState :: TP TPState
getTPState = ask

-- | Make a unique number in this TP run. We combine that context with the proof-count
tpGetNextUnique :: TP TPUnique
tpGetNextUnique = TPUser <$> liftIO randomIO

-- | get the configuration
getTPConfig :: TP SMTConfig
getTPConfig = do rCfg <- config <$> getTPState
                 liftIO (readIORef rCfg)

-- | set the configuration
setTPConfig :: SMTConfig -> TP ()
setTPConfig cfg = do st <- getTPState
                     liftIO (writeIORef (config st) cfg)

-- | Update stats
updStats :: MonadIO m => TPState -> (TPStats -> TPStats) -> m ()
updStats TPState{stats} u = liftIO $ modifyIORef' stats u

-- | Display the message if not quiet. Note that we don't print a newline; so the message must have it if needed.
message :: MonadIO m => SMTConfig -> String -> m ()
message SMTConfig{tpOptions = TPOptions{quiet}, redirectVerbose} s
  | quiet
  = pure ()
  | Just f <- redirectVerbose
  = liftIO $ appendFile f s
  | True
  = liftIO $ putStr s

-- | Print the list of functions whose termination measures have been verified.
printMeasures :: SMTConfig -> [String] -> IO ()
printMeasures = printFunctions "Functions proven terminating"

-- | Print the list of functions whose productivity (guardedness) has been verified.
printProductive :: SMTConfig -> [String] -> IO ()
printProductive = printFunctions "Functions proven productive"

-- | Print a list of function names under a header, wrapping lines to avoid excessively long output.
-- If the list fits on one line, it follows the header directly. Otherwise, it starts on a new line.
printFunctions :: String -> SMTConfig -> [String] -> IO ()
printFunctions header cfg names
  | length oneLine <= limit = message cfg $ header ++ ": " ++ oneLine ++ "\n"
  | True                    = message cfg $ header ++ ":\n  " ++ wrapped ++ "\n"
  where cleaned = nub (sort (map strip names))
        strip   = dropWhileEnd (== ' ') . takeWhile (/= '@')

        limit = 90

        oneLine = intercalate ", " cleaned

        wrapped = go limit cleaned

        go _ []     = ""
        go _ [n]    = n
        go r (n:ns) = let len  = length n + 2  -- account for ", "
                          rest = go (r - len) ns
                      in if r - len < 0 && r /= limit
                         then "\n  " ++ go limit (n:ns)
                         else case rest of
                                '\n':_ -> n ++ "," ++ rest
                                _      -> n ++ ", " ++ rest

-- | Start a proof. We return the number of characters we printed, so the finisher can align the result.
startTP :: SMTConfig -> Bool -> String -> Int -> TPProofContext -> IO Int
startTP cfg newLine what level ctx = do message cfg $ line ++ if newLine then "\n" else ""
                                        hFlush stdout
                                        return (length line)
  where nm = case ctx of
               TPProofOneShot n _       -> n
               TPProofStep    _ _ hs ss -> intercalate "." ss ++ userHints hs

        tab = 2 * level

        line = replicate tab ' ' ++ what ++ ": " ++ nm

        userHints [] = ""
        userHints ss = " (" ++ intercalate ", " ss ++ ")"

-- | Finish a proof. First argument is what we got from the call of 'startTP' above.
finishTP :: SMTConfig -> String -> (Int, Maybe NominalDiffTime) -> [NominalDiffTime] -> IO ()
finishTP cfg@SMTConfig{tpOptions = TPOptions{ribbonLength}} what (skip, mbT) extraTiming =
   message cfg $ replicate (ribbonLength - skip) ' ' ++ what ++ timing ++ extras ++ "\n"
 where timing = maybe "" ((' ' :) . mkTiming) mbT
       extras = concatMap mkTiming extraTiming

       mkTiming t = '[' : showTDiff t ++ "]"

-- | Unique identifier for each proof.
data TPUnique = TPInternal        -- IH's
              | TPSorry           -- sorry
              | TPQC              -- qc (quick-check)
              | TPNoTermCheck     -- no termination check (smtFunctionNoTermination)
              | TPUser Int64      -- user given
              deriving (NFData, Generic, Eq)

-- | Proof for a property. This type is left abstract, i.e., the only way to create on is via a
-- call to lemma/theorem etc., ensuring soundness. (Note that the trusted-code base here
-- is still large: The underlying solver, SBV, and TP kernel itself. But this
-- mechanism ensures we can't create proven things out of thin air, following the standard LCF
-- methodology.)
newtype Proof a = Proof { proofOf :: ProofObj -- ^ Get the underlying proof object
                        }

-- | Grab the underlying boolean in a proof. Useful in assumption contexts where we need a boolean
assumptionFromProof :: Proof a -> SBool
assumptionFromProof = getObjProof . proofOf

-- | The actual proof container
data ProofObj = ProofObj { dependencies :: [ProofObj]     -- ^ Immediate dependencies of this proof. (Not transitive)
                         , isUserAxiom  :: Bool           -- ^ Was this an axiom given by the user?
                         , getObjProof  :: SBool          -- ^ Get the underlying boolean
                         , getProp      :: Dynamic        -- ^ The actual proposition
                         , proofName    :: String         -- ^ User given name
                         , uniqId       :: TPUnique       -- ^ Unique identifier
                         , aliases      :: [String]       -- ^ Other names for proofs of the same proposition (populated on cache hit)
                         , wasCached    :: Bool           -- ^ Was this proof retrieved from the cache?
                         }

-- | Drop the instantiation part
shortProofName :: ProofObj -> String
shortProofName p | " @ " `isInfixOf` s = reverse . dropWhile isSpace . reverse . takeWhile (/= '@') $ s
                 | True                = s
   where s = proofName p

-- | Nicely format a bunch of proof-names, shortened and uniquified. Note that if we get a dependency
-- via multiple routes, they can get different uniqid's; so we do a bit of compression here.
shortProofNames :: [ProofObj] -> String
shortProofNames = intercalate ", " . map merge . compress . sort . map shortProofName . nubBy (\a b -> uniqId a == uniqId b)
 where compress []     = []
       compress (a:as) = case span (a ==) as of
                           (same, other) -> (a, length same + 1) : compress other
       merge (n, 1) = n
       merge (n, x) = n ++ " (x" ++ show x ++ ")"

-- | Keeping track of where the sorry originates from. Used in displaying dependencies.
newtype RootOfTrust = RootOfTrust (Maybe [ProofObj])

-- | Show instance for t'RootOfTrust'
instance Show RootOfTrust where
  show (RootOfTrust mbp) = case mbp of
                             Nothing -> "Nothing"
                             Just ps -> "Just [" ++ shortProofNames ps ++ "]"

-- | Trust forms a semigroup
instance Semigroup RootOfTrust where
   RootOfTrust as <> RootOfTrust bs = RootOfTrust $ nubBy (\a b -> uniqId a == uniqId b) <$> (as <> bs)

-- | Trust forms a monoid
instance Monoid RootOfTrust where
  mempty = RootOfTrust Nothing

-- | NFData ignores the getProp field
instance NFData ProofObj where
  rnf (ProofObj dependencies isUserAxiom getObjProof _getProp proofName uniqId aliases wasCached) =     rnf dependencies
                                                                                                 `seq` rnf isUserAxiom
                                                                                                 `seq` rnf getObjProof
                                                                                                 `seq` rnf proofName
                                                                                                 `seq` rnf uniqId
                                                                                                 `seq` rnf aliases
                                                                                                 `seq` rnf wasCached

-- | Dependencies of a proof, in a tree format.
data ProofTree = ProofTree ProofObj [ProofTree]

-- | Return all the proofs this particular proof depends on, transitively
getProofTree :: ProofObj -> ProofTree
getProofTree p = ProofTree p $ map getProofTree (dependencies p)

-- | Turn dependencies to a container tree, for display purposes
depsToTree :: Bool -> [TPUnique] -> (String -> Int -> Int -> a) -> (Int, ProofTree) -> ([TPUnique], Tree a)
depsToTree shouldCompress visited xform (cnt, ProofTree top ds) = (nVisited, Node (xform nTop cnt (length chlds)) chlds)
  where nTop = shortProofName top
        uniq = uniqId top

        (nVisited, chlds)
           | shouldCompress && uniq `elem` visited = (visited, [])
           | shouldCompress                        = walk (uniq : visited) (compress (filter interesting ds))
           | True                                  = walk         visited  (map (1,) (filter interesting ds))

        walk v []     = (v, [])
        walk v (c:cs) = let (v',  t)  = depsToTree shouldCompress v xform c
                            (v'', ts) = walk v' cs
                        in (v'', t : ts)

        -- Don't show internal axioms, not interesting
        interesting (ProofTree p _) = case uniqId p of
                                        TPInternal    -> False
                                        TPSorry       -> True
                                        TPQC          -> True
                                        TPNoTermCheck -> True
                                        TPUser{}      -> True

        -- If a proof is used twice in the same proof, compress it
        compress :: [ProofTree] -> [(Int, ProofTree)]
        compress []       = []
        compress (p : ps) = (1 + length [() | (_, True) <- filtered], p) : compress [d | (d, False) <- filtered]
          where filtered = [(d, uniqId p' == curUniq) | d@(ProofTree p' _) <- ps]
                curUniq  = case p of
                             ProofTree curProof _ -> uniqId curProof

-- | Display the proof tree as ASCII text. The first argument is if we should compress the tree, showing only the first
-- use of any sublemma.
showProofTree :: Bool -> Proof a -> String
showProofTree compress d = showTree $ snd $ depsToTree compress [] sh (1, getProofTree (proofOf d))
    where sh nm 1 _ = nm
          sh nm x _= nm ++ " (x" ++ show x ++ ")"

-- | Display the tree as an html doc for rendering purposes.
-- The first argument is if we should compress the tree, showing only the first
-- use of any sublemma. Second is the path (or URL) to external CSS file, if needed.
showProofTreeHTML :: Bool -> Maybe FilePath -> Proof a -> String
showProofTreeHTML compress mbCSS p = htmlTree mbCSS $ snd $ depsToTree compress [] nodify (1, getProofTree (proofOf p))
  where nodify :: String -> Int -> Int -> NodeInfo
        nodify nm cnt dc = NodeInfo { nodeBehavior = InitiallyExpanded
                                    , nodeName     = nm
                                    , nodeInfo     = spc (used cnt) ++ depCount dc
                                    }
        used 1 = ""
        used n = "Used " ++ show n ++ " times."

        spc "" = ""
        spc s  = s ++ " "

        depCount 0 = ""
        depCount 1 = "Has one dependency."
        depCount n = "Has " ++ show n ++ " dependencies."

-- | Show instance for t'Proof'
instance Typeable a => Show (Proof a) where
  show p@(Proof ProofObj{proofName = nm}) = '[' : sh (rootOfTrust p) ++ "] " ++ nm ++ " :: " ++ pretty (show (typeOf p))
    where sh (RootOfTrust Nothing)   = "Proven"
          sh (RootOfTrust (Just ps)) = "Modulo: " ++ shortProofNames ps

          -- More mathematical notation for types.
          pretty :: String -> String
          pretty = charToString . compress . unwords . walk . words . concatMap (\c -> if c == ',' then " , " else [c]) . clean
            where fa v = ['Ɐ' : unQuote v, "∷"]
                  ex v = ['∃' : unQuote v, "∷"]

                  -- Remove spaces before commas: "foo , bar" -> "foo, bar"
                  compress (' ' : ',' : rest) = compress (',' : rest)
                  compress (c : rest)         = c : compress rest
                  compress []                 = []

                  -- Replace [Char] with String everywhere
                  charToString ('[':'C':'h':'a':'r':']':rest) = "String" ++ charToString rest
                  charToString (c:rest)                       = c : charToString rest
                  charToString []                             = []

                  walk ("SBV"    : "Bool" : rest) = walk $ "Bool" :  rest
                  walk ("Forall" : xs     : rest) = walk $ fa xs  ++ rest
                  walk ("Exists" : xs     : rest) = walk $ ex xs  ++ rest
                  walk ("->"              : rest) = walk $ "→"    :  rest

                  -- handle the double case. This isn't quite solid, but it does the trick.
                  walk ("((Forall" : xs : t1 : "," : "(Forall" : ys : t2 : rest) = ap (fa xs) ++ [np t1 ++ ","] ++ fa ys ++ [np t2] ++ walk rest
                     where -- remove a closing paren from the end if it's there
                           np s | ")" `isSuffixOf` s = init s
                                | True               = s
                           -- add open paren to the first word
                           ap (t : ts) = ('(':t) : ts
                           ap []       = []

                  -- Otherwise, pass along
                  walk (c : cs) = c : walk cs
                  walk []       = []

          -- Strip of Proof (...)
          clean :: String -> String
          clean s | pre `isPrefixOf` s && suf `isSuffixOf` s
                  = reverse . drop (length suf) . reverse . drop (length pre) $ s
                  | True
                  = s
            where pre = "Proof ("
                  suf = ")"

-- | A manifestly false theorem. This is useful when we want to prove a theorem that the underlying solver
-- cannot deal with, or if we want to postpone the proof for the time being. TP will keep
-- track of the uses of 'sorry' and will print them appropriately while printing proofs.
-- NB. We keep this as a t'ProofObj' as opposed to a t'Proof' as it is then easier to use it as a lemma helper.
sorry :: ProofObj
sorry = ProofObj { dependencies = []
                 , isUserAxiom  = False
                 , getObjProof  = label "sorry" (quantifiedBool p)
                 , getProp      = toDyn p
                 , proofName    = "sorry"
                 , uniqId       = TPSorry
                 , aliases      = []
                 , wasCached    = False
                 }
  where -- ideally, I'd rather just use
        --   p = sFalse
        -- but then SBV constant folds the boolean, and the generated script
        -- doesn't contain the actual contents, as SBV determines unsatisfiability
        -- itself. By using the following proposition (which is easy for the backend
        -- solver to determine as false, we avoid the constant folding.
        p (Forall @"__sbvTP_sorry" (x :: SBool)) = label "SORRY: TP, proof uses \"sorry\"" x

-- | Quick-check uses this proof. It's equivalent to sorry, really; except for its name
quickCheckProof :: ProofObj
quickCheckProof = ProofObj { dependencies = []
                           , isUserAxiom  = False
                           , getObjProof  = label "quickCheck" (quantifiedBool p)
                           , getProp      = toDyn p
                           , proofName    = "quickCheck"
                           , uniqId       = TPQC
                           , aliases      = []
                           , wasCached    = False
                           }
  where -- ideally, I'd rather just use
        --   p = sFalse
        -- but then SBV constant folds the boolean, and the generated script
        -- doesn't contain the actual contents, as SBV determines unsatisfiability
        -- itself. By using the following proposition (which is easy for the backend
        -- solver to determine as false, we avoid the constant folding.
        p (Forall @"__sbvTP_quickCheck" (x :: SBool)) = label "QUICKCHECK: TP, proof uses \"qc\"" x

-- | A proof object representing a function whose termination was not checked.
-- When a function is defined with 'Data.SBV.smtFunctionNoTermination', its termination
-- is assumed but not proven. Any proof that depends on such a function will be
-- marked as modulo this assumption in its root of trust.
noTermCheckProof :: String -> ProofObj
noTermCheckProof nm = ProofObj { dependencies = []
                               , isUserAxiom  = False
                               , getObjProof  = sTrue
                               , getProp      = toDyn True
                               , proofName    = nm ++ " termination"
                               , uniqId       = TPNoTermCheck
                               , aliases      = []
                               , wasCached    = False
                               }

-- | Calculate the root of trust. The returned list of proofs, if any, will need to be sorry and quickcheck free to
-- have the given proof to be sorry-free.
rootOfTrust :: Proof a -> RootOfTrust
rootOfTrust = rot True . proofOf
  where rot atTop p@ProofObj{uniqId = curUniq, dependencies} = compress res
          where res = case curUniq of
                        TPInternal    -> RootOfTrust Nothing
                        TPQC          -> RootOfTrust $ Just [quickCheckProof]
                        TPSorry       -> RootOfTrust $ Just [sorry]
                        TPNoTermCheck -> RootOfTrust $ Just [p]
                        TPUser {}     -> self <> foldMap (rot False) dependencies

                -- if sorry or quickcheck is one of our direct dependencies, then we trust this proof.
                -- Note that we skip this at the top. Why? at that level, we want to see the direct
                -- dependency. But if we're down at a lower level, we just want to pick up
                self | atTop                     = mempty
                     | any isUnsafe dependencies = RootOfTrust $ Just [p]
                     | True                      = mempty

                isUnsafe ProofObj{uniqId = u} = u `elem` [TPSorry, TPQC]

                -- If sorry is present, it dominates everything else. Otherwise keep all.
                compress (RootOfTrust mbps) = RootOfTrust $ reduce <$> mbps
                  where reduce ps
                          | any (\o -> uniqId o == TPSorry) ps = [sorry]
                          | True                               = ps

-- | Calculate the modulo string for dependencies
concludeModulo :: [ProofObj] -> String
concludeModulo by = case foldMap (rootOfTrust . Proof) by of
                      RootOfTrust Nothing   -> ""
                      RootOfTrust (Just ps) -> " [Modulo: " ++ shortProofNames ps ++ "]"

-- | Make TP proofs quiet. Note that this setting will be effective with the
-- call to 'runTP'\/'runTPWith', i.e., if you change the solver in a call to 'Data.SBV.TP.lemmaWith'\/'Data.SBV.TP.theoremWith', we
-- will inherit the quiet settings from the surrounding environment.
tpQuiet :: Bool -> SMTConfig -> SMTConfig
tpQuiet b cfg = cfg{tpOptions = (tpOptions cfg) { quiet = b }}

-- | Change the size of the ribbon for TP proofs. Note that this setting will be effective with the
-- call to 'runTP'\/'runTPWith', i.e., if you change the solver in a call to 'Data.SBV.TP.lemmaWith'\/'Data.SBV.TP.theoremWith', we
-- will inherit the ribbon settings from the surrounding environment.
tpRibbon :: Int -> SMTConfig -> SMTConfig
tpRibbon i cfg = cfg{tpOptions = (tpOptions cfg) { ribbonLength = i }}

-- | Make TP proofs produce statistics. Note that this setting will be effective with the
-- call to 'runTP'\/'runTPWith', i.e., if you change the solver in a call to 'Data.SBV.TP.lemmaWith'\/'Data.SBV.TP.theoremWith', we
-- will inherit the statistics settings from the surrounding environment.
tpStats :: SMTConfig -> SMTConfig
tpStats cfg = cfg{tpOptions = (tpOptions cfg) { printStats = True }}


-- | When proving assumptions for each step, print them as well. Normally, SBV doesn't
-- print assumptions in each proof step, though it does prove them as they are typically trivial.
-- But in certain cases seeing them would be helpful.
tpAsms :: SMTConfig -> SMTConfig
tpAsms cfg = cfg{tpOptions = (tpOptions cfg) { printAsms = True }}

-- | Create a t'MeasureHelper' from a TP proof action. During measure verification,
-- the proof is run to confirm the property holds, and the proven property is extracted
-- and asserted as an axiom in the measure verification session. The solver configuration
-- is inherited from the measure verification context, with output suppressed.
--
-- Example usage with 'Data.SBV.smtFunctionWithMeasure':
--
-- @
-- normalize = smtFunctionWithMeasure "normalize"
--               (\\f -> tuple (ifComplexity f, ifDepth f)
--               , [measureLemma ifDepthNonNeg, measureLemma ifComplexityPos]
--               )
--             $ \\f -> ...
-- @
measureLemma :: forall a. (QuantifiedBool a, Typeable a) => TP (Proof a) -> MeasureHelper
measureLemma tp = MeasureHelper $ \cfg -> do
  proof <- runTPWith (tpQuiet True cfg) tp
  case fromDynamic @a (getProp (proofOf proof)) of
    Just prop -> pure (quantifiedBool prop)
    Nothing   -> error "Data.SBV.measureLemma: impossible type mismatch in measure helper"

-- | Like 'measureLemma', but using the given solver configuration, ignoring the
-- one from the measure verification context.
measureLemmaWith :: forall a. (QuantifiedBool a, Typeable a) => SMTConfig -> TP (Proof a) -> MeasureHelper
measureLemmaWith userCfg tp = MeasureHelper $ \_cfg -> do
  proof <- runTPWith (tpQuiet True userCfg) tp
  case fromDynamic @a (getProp (proofOf proof)) of
    Just prop -> pure (quantifiedBool prop)
    Nothing   -> error "Data.SBV.measureLemmaWith: impossible type mismatch in measure helper"
