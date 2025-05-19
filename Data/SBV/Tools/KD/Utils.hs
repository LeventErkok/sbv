-----------------------------------------------------------------------------
-- |
-- Module    : Data.SBV.Tools.KD.Utils
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Various KnuckleDrugger machinery.
-----------------------------------------------------------------------------

{-# LANGUAGE DataKinds                  #-}
{-# LANGUAGE DeriveAnyClass             #-}
{-# LANGUAGE DeriveGeneric              #-}
{-# LANGUAGE DerivingStrategies         #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE NamedFieldPuns             #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE TypeAbstractions           #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module Data.SBV.Tools.KD.Utils (
         KD, runKD, runKDWith, Proof(..), sorry
       , startKD, finishKD, getKDState, getKDConfig, kdGetNextUnique, KDState(..), KDStats(..), RootOfTrust(..)
       , KDProofContext(..), message, updStats, rootOfTrust, trustsModulo
       , ProofTree(..), KDUnique(..), getProofTree, showProofTree, showProofTreeHTML, shortProofName
       ) where

import Control.Monad.Reader (ReaderT, runReaderT, MonadReader, ask, liftIO)
import Control.Monad.Trans  (MonadIO)

import Data.Time (NominalDiffTime)

import Data.Tree
import Data.Tree.View

import Data.Char (isSpace)
import Data.List (intercalate, isInfixOf, nubBy, partition)
import System.IO (hFlush, stdout)

import Data.SBV.Core.Data      (SBool, Forall(..), quantifiedBool)
import Data.SBV.Core.Model     (label)
import Data.SBV.Core.Symbolic  (SMTConfig, KDOptions(..))
import Data.SBV.Provers.Prover (defaultSMTCfg, SMTConfig(..))

import Data.SBV.Utils.TDiff (showTDiff, timeIf)
import Control.DeepSeq (NFData(rnf))

import Data.IORef

import GHC.Generics
import Data.Dynamic

-- | Various statistics we collect
data KDStats = KDStats { noOfCheckSats :: Int
                       , noOfProofs    :: Int
                       , solverElapsed :: NominalDiffTime
                       }

-- | Extra state we carry in a KD context
data KDState = KDState { stats  :: IORef KDStats
                       , config :: SMTConfig
                       }

-- | Monad for running KnuckleDragger proofs in.
newtype KD a = KD (ReaderT KDState IO a)
            deriving newtype (Applicative, Functor, Monad, MonadIO, MonadReader KDState, MonadFail)

-- | The context in which we make a check-sat call
data KDProofContext = KDProofOneShot String   -- ^ A one shot proof, with string containing its name
                                     [Proof]  -- ^ Helpers used (latter only used for cex generation)
                    | KDProofStep    Bool     -- ^ A proof step. If Bool is true, then these are the assumptions for that step
                                     String   -- ^ Name of original goal
                                     [String] -- ^ The helper "strings" given by the user
                                     [String] -- ^ The step name, i.e., the name of the branch in the proof tree

-- | Run a KD proof, using the default configuration.
runKD :: KD a -> IO a
runKD = runKDWith defaultSMTCfg

-- | Run a KD proof, using the given configuration.
runKDWith :: SMTConfig -> KD a -> IO a
runKDWith cfg@SMTConfig{kdOptions = KDOptions{measureTime}} (KD f) = do
   rStats <- newIORef $ KDStats { noOfCheckSats = 0, noOfProofs = 0, solverElapsed = 0 }
   (mbT, r) <- timeIf measureTime $ runReaderT f KDState {config = cfg, stats = rStats}
   case mbT of
     Nothing -> pure ()
     Just t  -> do KDStats noOfCheckSats pc solverTime <- readIORef rStats

                   let stats = [ ("SBV",       showTDiff (t - solverTime))
                               , ("Solver",    showTDiff solverTime)
                               , ("Total",     showTDiff t)
                               , ("Proofs",    show pc)
                               , ("Decisions", show noOfCheckSats)
                               ]

                   message cfg $ '[' : intercalate ", " [k ++ ": " ++ v | (k, v) <- stats] ++ "]\n"
   pure r

-- | get the state
getKDState :: KD KDState
getKDState = ask

kdGetNextUnique :: KD KDUnique
kdGetNextUnique = do st@KDState{stats} <- getKDState
                     c <- liftIO (noOfProofs <$> readIORef stats)
                     updStats st (\s -> s {noOfProofs = c + 1})
                     pure $ KDUser c

-- | get the configuration
getKDConfig :: KD SMTConfig
getKDConfig = config <$> getKDState

-- | Update stats
updStats :: MonadIO m => KDState -> (KDStats -> KDStats) -> m ()
updStats KDState{stats} u = liftIO $ modifyIORef' stats u

-- | Display the message if not quiet. Note that we don't print a newline; so the message must have it if needed.
message :: MonadIO m => SMTConfig -> String -> m ()
message SMTConfig{kdOptions = KDOptions{quiet}} s
  | quiet = pure ()
  | True  = liftIO $ putStr s

-- | Start a proof. We return the number of characters we printed, so the finisher can align the result.
startKD :: SMTConfig -> Bool -> String -> Int -> KDProofContext -> IO Int
startKD cfg newLine what level ctx = do message cfg $ line ++ if newLine then "\n" else ""
                                        hFlush stdout
                                        return (length line)
  where nm = case ctx of
               KDProofOneShot n _       -> n
               KDProofStep    _ _ hs ss -> intercalate "." ss ++ userHints hs

        tab = 2 * level

        line = replicate tab ' ' ++ what ++ ": " ++ nm

        userHints [] = ""
        userHints ss = " (" ++ intercalate ", " ss ++ ")"

-- | Finish a proof. First argument is what we got from the call of 'startKD' above.
finishKD :: SMTConfig -> String -> (Int, Maybe NominalDiffTime) -> [NominalDiffTime] -> IO ()
finishKD cfg@SMTConfig{kdOptions = KDOptions{ribbonLength}} what (skip, mbT) extraTiming =
   message cfg $ replicate (ribbonLength - skip) ' ' ++ what ++ timing ++ extras ++ "\n"
 where timing = maybe "" ((' ' :) . mkTiming) mbT
       extras = concatMap mkTiming extraTiming

       mkTiming t = '[' : showTDiff t ++ "]"

-- | Unique identifier for each proof.
data KDUnique = KDInternal
              | KDSorry
              | KDUser Int
              deriving (NFData, Generic, Eq)

-- | Proof for a property. This type is left abstract, i.e., the only way to create on is via a
-- call to lemma/theorem etc., ensuring soundness. (Note that the trusted-code base here
-- is still large: The underlying solver, SBV, and KnuckleDragger kernel itself. But this
-- mechanism ensures we can't create proven things out of thin air, following the standard LCF
-- methodology.)
data Proof = Proof { dependencies :: [Proof]     -- ^ Immediate dependencies of this proof. (Not transitive)
                   , isUserAxiom  :: Bool        -- ^ Was this an axiom given by the user?
                   , getProof     :: SBool       -- ^ Get the underlying boolean
                   , getProp      :: Dynamic     -- ^ The actual proposition
                   , proofName    :: String      -- ^ User given name
                   , uniqId       :: KDUnique    -- ^ Unique identified
                   }

-- | Drop the instantiation part
shortProofName :: Proof -> String
shortProofName p | "@" `isInfixOf` s = reverse . dropWhile isSpace . reverse . takeWhile (/= '@') $ s
                 | True              = s
   where s = proofName p

-- | Keeping track of where the sorry originates from. Used in displaying dependencies.
newtype RootOfTrust = RootOfTrust (Maybe [Proof])

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
instance NFData Proof where
  rnf (Proof dependencies isUserAxiom getProof _getProp proofName uniqId) =     rnf dependencies
                                                                          `seq` rnf isUserAxiom
                                                                          `seq` rnf getProof
                                                                          `seq` rnf proofName
                                                                          `seq` rnf uniqId

-- | Dependencies of a proof, in a tree format.
data ProofTree = ProofTree Proof [ProofTree]

-- | Return all the proofs this particular proof depends on, transitively
getProofTree :: Proof -> ProofTree
getProofTree p = ProofTree p $ map getProofTree (dependencies p)

-- | Turn dependencies to a container tree, for display purposes
depsToTree :: Bool -> [KDUnique] -> (String -> Int -> Int -> a) -> (Int, ProofTree) -> ([KDUnique], Tree a)
depsToTree shouldCompress visited xform (cnt, ProofTree top ds) = (nVisited, Node (xform nTop cnt (length chlds)) chlds)
  where nTop = shortProofName top
        uniq = uniqId top

        (nVisited, chlds)
           | shouldCompress && uniq `elem` visited = (visited, [])
           | shouldCompress                        = walk (uniq : visited) (compress       (filter interesting ds))
           | True                                  = walk         visited  (zip (repeat 1) (filter interesting ds))

        walk v []     = (v, [])
        walk v (c:cs) = let (v',  t)  = depsToTree shouldCompress v xform c
                            (v'', ts) = walk v' cs
                        in (v'', t : ts)

        -- Don't show internal axioms, not interesting
        interesting (ProofTree p _) = case uniqId p of
                                        KDSorry    -> True
                                        KDInternal -> False
                                        KDUser{}   -> True

        -- If a proof is used twice in the same proof, compress it
        compress :: [ProofTree] -> [(Int, ProofTree)]
        compress []       = []
        compress (p : ps) = (1 + length [() | (_, True) <- filtered], p) : compress [d | (d, False) <- filtered]
          where filtered = [(d, uniqId p' == curUniq) | d@(ProofTree p' _) <- ps]
                curUniq  = case p of
                             ProofTree curProof _ -> uniqId curProof

-- | Display the proof tree as ASCII text. The first argument is if we should compress the tree, showing only the first
-- use of any sublemma.
showProofTree :: Bool -> ProofTree -> String
showProofTree compress d = showTree $ snd $ depsToTree compress [] sh (1, d)
    where sh nm 1 _ = nm
          sh nm x _= nm ++ " (x" ++ show x ++ ")"

-- | Display the tree as an html doc for rendering purposes.
-- The first argument is if we should compress the tree, showing only the first
-- use of any sublemma. Second is the path (or URL) to external CSS file, if needed.
showProofTreeHTML :: Bool -> Maybe FilePath -> ProofTree -> String
showProofTreeHTML compress mbCSS deps = htmlTree mbCSS $ snd $ depsToTree compress [] nodify (1, deps)
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
instance Show Proof where
  show p@Proof{proofName = nm} = '[' : sh (rootOfTrust p) ++ "] " ++ nm
    where sh (RootOfTrust Nothing)   = "Proven"
          sh (RootOfTrust (Just ps)) = "Modulo: " ++ intercalate ", " (map shortProofName ps)

-- | A manifestly false theorem. This is useful when we want to prove a theorem that the underlying solver
-- cannot deal with, or if we want to postpone the proof for the time being. KnuckleDragger will keep
-- track of the uses of 'sorry' and will print them appropriately while printing proofs.
sorry :: Proof
sorry = Proof { dependencies = []
              , isUserAxiom  = False
              , getProof     = label "sorry" (quantifiedBool p)
              , getProp      = toDyn p
              , proofName    = "sorry"
              , uniqId       = KDSorry
              }
  where -- ideally, I'd rather just use
        --   p = sFalse
        -- but then SBV constant folds the boolean, and the generated script
        -- doesn't contain the actual contents, as SBV determines unsatisfiability
        -- itself. By using the following proposition (which is easy for the backend
        -- solver to determine as false, we avoid the constant folding.
        p (Forall @"__sbvKD_sorry" (x :: SBool)) = label "SORRY: KnuckleDragger, proof uses \"sorry\"" x

-- | Calculate the root of trust. The returned list of proofs, if any, will need to be sorry-free to
-- have the given proof to be sorry-free.
rootOfTrust :: Proof -> RootOfTrust
rootOfTrust p@Proof{uniqId, dependencies} = compress res
  where res = case uniqId of
                KDInternal -> RootOfTrust Nothing
                KDSorry    -> RootOfTrust $ Just [sorry]
                KDUser {}  -> self <> foldMap rootOfTrust dependencies

        -- if sorry is one of our direct dependencies, then we trust this proof
        self | any isSorry dependencies = RootOfTrust $ Just [p]
             | True                     = mempty

        isSorry Proof{uniqId = u} = u == KDSorry

        -- If we have any dependency that is not sorry itself, then we can skip all the sorries.
        -- Why? Because "sorry" will implicitly be coming from one of these anyhow. (In other
        -- words, we do not need to (or want to) distinguish between different uses of sorry.
        compress (RootOfTrust mbps) = RootOfTrust $ reduce <$> mbps
          where reduce ps = case partition isSorry ps of
                              (_, []) -> [sorry]
                              (_, os) -> os

-- | Calculate the modulo string for dependencies
trustsModulo :: [Proof] -> String
trustsModulo by = case foldMap rootOfTrust by of
                    RootOfTrust Nothing   -> ""
                    RootOfTrust (Just ps) -> " [" ++ intercalate ", " (map (shortProofName) ps) ++ "]"
