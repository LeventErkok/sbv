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

{-# LANGUAGE DeriveAnyClass             #-}
{-# LANGUAGE DeriveGeneric              #-}
{-# LANGUAGE DerivingStrategies         #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE NamedFieldPuns             #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module Data.SBV.Tools.KD.Utils (
         KD, runKD, runKDWith, Proof(..)
       , startKD, finishKD, getKDState, getKDConfig, KDState(..), KDStats(..)
       , RootOfTrust(..), KDProofContext(..), calculateRootOfTrust, message, updStats
       , KDProofDeps(..), getProofTree
       ) where

import Control.Monad.Reader (ReaderT, runReaderT, MonadReader, ask, liftIO)
import Control.Monad.Trans  (MonadIO)

import Data.Time (NominalDiffTime)

import Data.Char (isSpace)
import Data.List (intercalate, nub, sort, isInfixOf)
import System.IO (hFlush, stdout)

import Data.SBV.Core.Data (SBool)
import Data.SBV.Core.Symbolic  (SMTConfig, KDOptions(..))
import Data.SBV.Provers.Prover (defaultSMTCfg, SMTConfig(..))

import Data.SBV.Utils.TDiff (showTDiff, timeIf)
import Control.DeepSeq (NFData(rnf))

import Data.IORef

import GHC.Generics
import Data.Dynamic

-- | Various statistics we collect
data KDStats = KDStats { noOfCheckSats :: Int
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
   rStats <- newIORef $ KDStats { noOfCheckSats = 0, solverElapsed = 0 }
   (mbT, r) <- timeIf measureTime $ runReaderT f KDState {config = cfg, stats = rStats}
   case mbT of
     Nothing -> pure ()
     Just t  -> do KDStats noOfCheckSats solverTime <- readIORef rStats

                   let stats = [ ("SBV",       showTDiff (t - solverTime))
                               , ("Solver",    showTDiff solverTime)
                               , ("Total",     showTDiff t)
                               , ("Decisions", show noOfCheckSats)
                               ]

                   message cfg $ '[' : intercalate ", " [k ++ ": " ++ v | (k, v) <- stats] ++ "]\n"
   pure r

-- | get the state
getKDState :: KD KDState
getKDState = ask

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

-- | Keeping track of where the sorry originates from. Used in displaying dependencies.
data RootOfTrust = None        -- ^ Trusts nothing (aside from SBV, underlying solver etc.)
                 | Self        -- ^ Trusts itself, i.e., established by a call to sorry
                 | Prop String -- ^ Trusts a parent that itself trusts something else. Note the name here is the
                               --   name of the proposition itself, not the parent that's trusted.
                deriving (NFData, Generic)

-- | Proof for a property. This type is left abstract, i.e., the only way to create on is via a
-- call to lemma/theorem etc., ensuring soundness. (Note that the trusted-code base here
-- is still large: The underlying solver, SBV, and KnuckleDragger kernel itself. But this
-- mechanism ensures we can't create proven things out of thin air, following the standard LCF
-- methodology.)
data Proof = Proof { rootOfTrust  :: RootOfTrust -- ^ Root of trust, described above.
                   , dependencies :: [Proof]     -- ^ Immediate dependencies of this proof. (Not transitive)
                   , isUserAxiom  :: Bool        -- ^ Was this an axiom given by the user?
                   , getProof     :: SBool       -- ^ Get the underlying boolean
                   , getProp      :: Dynamic     -- ^ The actual proposition
                   , proofName    :: String      -- ^ User given name
                   }

-- | NFData ignores the getProp field
instance NFData Proof where
  rnf (Proof rootOfTrust dependencies isUserAxiom getProof _getProp proofName) =     rnf rootOfTrust
                                                                               `seq` rnf dependencies
                                                                               `seq` rnf isUserAxiom
                                                                               `seq` rnf getProof
                                                                               `seq` rnf proofName

-- | Dependencies of a proof, in a tree format.
data KDProofDeps = KDProofDeps Proof [KDProofDeps]

-- | Return all the proofs this particular proof depends on, transitively
getProofTree :: Proof -> KDProofDeps
getProofTree p = KDProofDeps p $ map getProofTree (dependencies p)

-- | Display the dependencies as a tree
instance Show KDProofDeps where
  show deps = intercalate "\n" $ go 0 (1, deps)
   where go :: Int -> (Int, KDProofDeps) -> [String]
         go level (cnt, KDProofDeps p ds) = (tab level ++ shortName p ++ showCount cnt)
                                          : concatMap (go (level + 1)) (compress (filter interesting ds))

         showCount 1 = ""
         showCount x = " (x" ++ show x ++ ")"

         -- Don't show IH's, just not interesting
         interesting (KDProofDeps p _) = not ("IH" `isInfixOf` proofName p)

         -- If a proof is used twice in the same proof, compress it
         compress :: [KDProofDeps] -> [(Int, KDProofDeps)]
         compress []       = []
         compress (p : ps) = (1 + length [() | (_, True) <- filtered], p) : [(1, d) | (d, False) <- filtered]
           where filtered = [(d, shortName p' == curName) | d@(KDProofDeps p' _) <- ps]
                 curName  = case p of
                              KDProofDeps curProof _ -> shortName curProof

         -- Drop the instantiation part
         shortName :: Proof -> String
         shortName p | "@" `isInfixOf` s = reverse . dropWhile isSpace . reverse . takeWhile (/= '@') $ s
                     | True              = s
            where s = proofName p

         space = replicate 5 ' '
         sep   = "+-- "

         tab 0 = ""
         tab l = drop (length sep - 1) $ prefix l ++ sep

         prefix 0 = ""
         prefix 1 = space
         prefix l = space ++ "|" ++ prefix (l-1)

-- | Show instance for t'Proof'
instance Show Proof where
  show Proof{rootOfTrust, isUserAxiom, proofName} = '[' : tag ++ "] " ++ proofName
     where tag | isUserAxiom = "Axiom"
               | True        = case rootOfTrust of
                                 None   -> "Proven"
                                 Self   -> "Sorry"
                                 Prop s -> "Modulo: " ++ s

-- | Calculate the root of trust for a proof. The string is the modulo text, if any.
calculateRootOfTrust :: String -> [Proof] -> (RootOfTrust, String)
calculateRootOfTrust nm by | not hasSelf && null depNames = (None,    "")
                           | True                         = (Prop nm, " [Modulo: " ++ why ++ "]")
   where why | hasSelf = "sorry"
             | True    = intercalate ", " depNames

         -- What's the root-of-trust for this node?
         -- If there are no "sorry" parents, and no parent nodes
         -- that are marked with a root of trust, then we don't have it either.
         -- Otherwise, mark it accordingly.
         parentRoots = map rootOfTrust by
         hasSelf     = not $ null [() | Self   <- parentRoots]
         depNames    = nub $ sort [p  | Prop p <- parentRoots]
