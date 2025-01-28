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
       , RootOfTrust(..), calculateRootOfTrust, message, updStats
       ) where

import Control.Monad.Reader (ReaderT, runReaderT, MonadReader, ask, liftIO)
import Control.Monad.Trans  (MonadIO)

import Data.Time (NominalDiffTime)

import Data.List (intercalate, nub, sort)
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
startKD :: SMTConfig -> Bool -> String -> [String] -> IO Int
startKD cfg newLine what nms = do message cfg $ line ++ if newLine then "\n" else ""
                                  hFlush stdout
                                  return (length line)
  where tab    = 2 * length (drop 1 nms)
        indent = replicate tab ' '
        tag    = what ++ ": " ++ intercalate "." (filter (not . null) nms)
        line   = indent ++ tag

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
data Proof = Proof { rootOfTrust :: RootOfTrust  -- ^ Root of trust, described above.
                   , isUserAxiom :: Bool         -- ^ Was this an axiom given by the user?
                   , getProof    :: SBool        -- ^ Get the underlying boolean
                   , getProp     :: Dynamic      -- ^ The actual proposition
                   , proofName   :: String       -- ^ User given name
                   }

-- | NFData ignores the getProp field
instance NFData Proof where
  rnf (Proof rootOfTrust isUserAxiom getProof _getProp proofName) =     rnf rootOfTrust
                                                                  `seq` rnf isUserAxiom
                                                                  `seq` rnf getProof
                                                                  `seq` rnf proofName
                                                                  `seq` ()

-- | Show instance for 'Proof'
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
