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
         TP, runTP, runTPWith, Proof(..), ProofObj(..), assumptionFromProof, sorry
       , startTP, finishTP, getTPState, getTPConfig, tpGetNextUnique, TPState(..), TPStats(..), RootOfTrust(..)
       , TPProofContext(..), message, updStats, rootOfTrust, concludeModulo
       , ProofTree(..), TPUnique(..), showProofTree, showProofTreeHTML, shortProofName
       , withProofCache
       , atProxy, tpQuiet, tpRibbon, tpStats, tpCache
       ) where

import Control.Monad.Reader (ReaderT, runReaderT, MonadReader, ask, liftIO)
import Control.Monad.Trans  (MonadIO)

import Data.Time (NominalDiffTime)

import Data.Tree
import Data.Tree.View

import Data.Proxy
import Data.Typeable (typeOf, TypeRep)

import Data.Char (isSpace)
import Data.List (intercalate, isInfixOf, nubBy, partition, sort)
import Data.Int  (Int64)

import Data.SBV.Utils.Lib (atProxy)

import System.IO     (hFlush, stdout)
import System.Random (randomIO)

import Data.SBV.Core.Data      (SBool, Forall(..), quantifiedBool)
import Data.SBV.Core.Model     (label)
import Data.SBV.Core.Symbolic  (SMTConfig, TPOptions(..))
import Data.SBV.Provers.Prover (defaultSMTCfg, SMTConfig(..))

import Data.SBV.Utils.TDiff (showTDiff, timeIf)
import Control.DeepSeq (NFData(rnf))

import Data.IORef

import GHC.Generics
import Data.Dynamic

import qualified Data.Map as Map
import Data.Map (Map)

-- | Various statistics we collect
data TPStats = TPStats { noOfCheckSats :: Int
                       , solverElapsed :: NominalDiffTime
                       }

-- | Extra state we carry in a TP context
data TPState = TPState { stats      :: IORef TPStats
                       , proofCache :: IORef (Map (String, TypeRep) ProofObj)
                       , config     :: SMTConfig
                       }

-- | Monad for running TP proofs in.
newtype TP a = TP (ReaderT TPState IO a)
            deriving newtype (Applicative, Functor, Monad, MonadIO, MonadReader TPState, MonadFail)

-- | If caches are enabled, see if we cached this proof and return it; otherwise generate it, cache it, and return it
withProofCache :: forall a. Typeable a => String -> TP (Proof a) -> TP (Proof a)
withProofCache nm genProof = do
  TPState{proofCache, config = cfg@SMTConfig {tpOptions = TPOptions {cacheProofs}}} <- getTPState

  let key = (nm, typeOf (Proxy @a))

  if not cacheProofs
     then genProof
     else do cache <- liftIO $ readIORef proofCache
             case key `Map.lookup` cache of
               Just prf -> do liftIO $ do tab <- startTP cfg False "Cached" 0 (TPProofOneShot nm [])
                                          finishTP cfg "Q.E.D." (tab, Nothing) []
                              pure $ Proof prf{isCached = True}
               Nothing  -> do p <- genProof
                              liftIO $ modifyIORef' proofCache (Map.insert key (proofOf p))
                              pure p

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
   rStats <- newIORef $ TPStats { noOfCheckSats = 0, solverElapsed = 0 }
   rCache <- newIORef Map.empty
   (mbT, r) <- timeIf printStats $ runReaderT f TPState {config = cfg, stats = rStats, proofCache = rCache}
   case mbT of
     Nothing -> pure ()
     Just t  -> do TPStats noOfCheckSats solverTime <- readIORef rStats

                   let stats = [ ("SBV",       showTDiff (t - solverTime))
                               , ("Solver",    showTDiff solverTime)
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
getTPConfig = config <$> getTPState

-- | Update stats
updStats :: MonadIO m => TPState -> (TPStats -> TPStats) -> m ()
updStats TPState{stats} u = liftIO $ modifyIORef' stats u

-- | Display the message if not quiet. Note that we don't print a newline; so the message must have it if needed.
message :: MonadIO m => SMTConfig -> String -> m ()
message SMTConfig{tpOptions = TPOptions{quiet}} s
  | quiet = pure ()
  | True  = liftIO $ putStr s

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
data TPUnique = TPInternal
              | TPSorry
              | TPUser Int64
              deriving (NFData, Generic, Eq)

-- | Proof for a property. This type is left abstract, i.e., the only way to create on is via a
-- call to lemma/theorem etc., ensuring soundness. (Note that the trusted-code base here
-- is still large: The underlying solver, SBV, and TP kernel itself. But this
-- mechanism ensures we can't create proven things out of thin air, following the standard LCF
-- methodology.)
data Proof a = Proof { proofOf :: ProofObj }

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
                         , isCached     :: Bool           -- ^ Was this a cached proof?
                         }

-- | Drop the instantiation part
shortProofName :: ProofObj -> String
shortProofName p | " @ " `isInfixOf` s = reverse . dropWhile isSpace . reverse . takeWhile (/= '@') $ s
                 | True                = s
   where s = proofName p

-- | Keeping track of where the sorry originates from. Used in displaying dependencies.
newtype RootOfTrust = RootOfTrust (Maybe [ProofObj])

-- | Show instance for t'RootOfTrust'
instance Show RootOfTrust where
  show (RootOfTrust mbp) = case mbp of
                             Nothing -> "Nothing"
                             Just ps -> "Just [" ++ intercalate ", " (map shortProofName ps) ++ "]"

-- | Trust forms a semigroup
instance Semigroup RootOfTrust where
   RootOfTrust as <> RootOfTrust bs = RootOfTrust $ nubBy (\a b -> uniqId a == uniqId b) <$> (as <> bs)

-- | Trust forms a monoid
instance Monoid RootOfTrust where
  mempty = RootOfTrust Nothing

-- | NFData ignores the getProp field
instance NFData ProofObj where
  rnf (ProofObj dependencies isUserAxiom getObjProof _getProp proofName uniqId isCached) =     rnf dependencies
                                                                                         `seq` rnf isUserAxiom
                                                                                         `seq` rnf getObjProof
                                                                                         `seq` rnf proofName
                                                                                         `seq` rnf uniqId
                                                                                         `seq` rnf isCached

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
                                        TPSorry    -> True
                                        TPInternal -> False
                                        TPUser{}   -> True

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
  show p@(Proof po@ProofObj{proofName = nm}) = '[' : sh (rootOfTrust p) ++ "] " ++ nm ++ " :: " ++ show (typeOf p)
    where sh (RootOfTrust Nothing)   = "Proven" ++ cacheInfo
          sh (RootOfTrust (Just ps)) = "Modulo: " ++ join ps ++ cacheInfo

          join = intercalate ", " . sort . map shortProofName

          cacheInfo = case cachedProofs po of
                        [] -> ""
                        cs -> ". Cached: " ++ join (nubBy (\p1 p2 -> uniqId p1 == uniqId p2) cs)

          cachedProofs prf@ProofObj{isCached} = if isCached then prf : rest else rest
            where rest = concatMap cachedProofs (dependencies prf)

-- | A manifestly false theorem. This is useful when we want to prove a theorem that the underlying solver
-- cannot deal with, or if we want to postpone the proof for the time being. TP will keep
-- track of the uses of 'sorry' and will print them appropriately while printing proofs.
sorry :: Proof a
sorry = Proof $ ProofObj { dependencies = []
                         , isUserAxiom  = False
                         , getObjProof  = label "sorry" (quantifiedBool p)
                         , getProp      = toDyn p
                         , proofName    = "sorry"
                         , uniqId       = TPSorry
                         , isCached     = False
                         }
  where -- ideally, I'd rather just use
        --   p = sFalse
        -- but then SBV constant folds the boolean, and the generated script
        -- doesn't contain the actual contents, as SBV determines unsatisfiability
        -- itself. By using the following proposition (which is easy for the backend
        -- solver to determine as false, we avoid the constant folding.
        p (Forall @"__sbvTP_sorry" (x :: SBool)) = label "SORRY: TP, proof uses \"sorry\"" x

-- | Calculate the root of trust. The returned list of proofs, if any, will need to be sorry-free to
-- have the given proof to be sorry-free.
rootOfTrust :: Proof a -> RootOfTrust
rootOfTrust = rot . proofOf
  where rot p@ProofObj{uniqId, dependencies} = compress res
          where res = case uniqId of
                        TPInternal -> RootOfTrust Nothing
                        TPSorry    -> RootOfTrust $ Just [proofOf sorry]
                        TPUser {}  -> self <> foldMap rot dependencies

                -- if sorry is one of our direct dependencies, then we trust this proof
                self | any isSorry dependencies = RootOfTrust $ Just [p]
                     | True                     = mempty

                isSorry ProofObj{uniqId = u} = u == TPSorry

                -- If we have any dependency that is not sorry itself, then we can skip all the sorries.
                -- Why? Because "sorry" will implicitly be coming from one of these anyhow. (In other
                -- words, we do not need to (or want to) distinguish between different uses of sorry.
                compress (RootOfTrust mbps) = RootOfTrust $ reduce <$> mbps
                  where reduce ps = case partition isSorry ps of
                                      (_, []) -> [proofOf sorry]
                                      (_, os) -> os

-- | Calculate the modulo string for dependencies
concludeModulo :: [ProofObj] -> String
concludeModulo by = case foldMap rootOfTrust (map Proof by) of
                      RootOfTrust Nothing   -> ""
                      RootOfTrust (Just ps) -> " [Modulo: " ++ intercalate ", " (map shortProofName ps) ++ "]"

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

-- | Make TP proofs use proof-cache. Note that if you use this option then
-- you are obligated to ensure all lemma\/theorem names you use are unique for the whole run.
-- Otherwise the results are not guaranteed to be sound. A good tip is to run the proof at
-- least once to completion, and use cache for regression purposes to avoid re-runs.
-- Again, this setting will be effective with the call to 'runTP'\/'runTPWith', i.e., if you
-- change the solver in a call to 'Data.SBV.TP.lemmaWith'\/'Data.SBV.TP.theoremWith', we will inherit the caching behavior
-- settings from the surrounding environment.
tpCache :: SMTConfig -> SMTConfig
tpCache cfg = cfg{tpOptions = (tpOptions cfg) { cacheProofs = True }}
