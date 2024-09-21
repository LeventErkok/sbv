-----------------------------------------------------------------------------
-- |
-- Module    : Data.SBV.Tools.KDUtils
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Various KnuckleDrugger machinery.
-----------------------------------------------------------------------------

{-# LANGUAGE DerivingStrategies         #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE NamedFieldPuns             #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module Data.SBV.Tools.KDUtils (
         KD, runKD, runKDWith
       , start, finish
       , KDConfig(..), defaultKDConfig, z3KD, cvc5KD
       ) where

import Control.Monad.Reader (ReaderT, runReaderT, ask, MonadReader)
import Control.Monad.Trans  (MonadIO(liftIO))

import Data.List (intercalate)
import System.IO (hFlush, stdout)

import Data.SBV.Core.Symbolic  (SMTConfig)
import Data.SBV.Provers.Prover (defaultSMTCfg, z3, cvc5)

-- | Keeping track of KD options/state
data KDConfig = KDConfig { kdRibbonLength    :: Int        -- ^ Lenght of the line as we print the proof
                         , kdVerbose         :: Bool       -- ^ Run verbose
                         , kdExtraSolverArgs :: [String]   -- ^ Extra command line arguments to pass to the solver
                         , kdSolverConfig    :: SMTConfig  -- ^ The backend solver to use
                         }

-- | Default KD-config uses the default SBV config (which is z3)
defaultKDConfig :: KDConfig
defaultKDConfig = KDConfig { kdRibbonLength    = 40
                           , kdVerbose         = False
                           , kdExtraSolverArgs = []
                           , kdSolverConfig    = defaultSMTCfg
                           }

-- | Run KD proof with z3 configuration.
z3KD :: KDConfig
z3KD = defaultKDConfig{kdSolverConfig = z3}

-- | Run KD proof with z3 configuration.
cvc5KD :: KDConfig
cvc5KD = defaultKDConfig{kdSolverConfig = cvc5}

-- | Monad for running KnuckleDragger proofs in.
newtype KD a = KD (ReaderT KDConfig IO a)
            deriving newtype (Applicative, Functor, Monad, MonadIO, MonadReader KDConfig, MonadFail)

-- | Run a KD proof, using the default configuration.
runKD :: KD a -> IO a
runKD = runKDWith defaultKDConfig

-- | Run a KD proof, using the given configuration.
runKDWith :: KDConfig -> KD a -> IO a
runKDWith cfg (KD f) = runReaderT f cfg

-- | Start a proof. We return the number of characters we printed, so the finisher can align the result.
start :: Bool -> String -> [String] -> KD Int
start newLine what nms = liftIO $ do putStr $ line ++ if newLine then "\n" else ""
                                     hFlush stdout
                                     return (length line)
  where tab    = 2 * length (drop 1 nms)
        indent = replicate tab ' '
        tag    = what ++ ": " ++ intercalate "." nms
        line   = indent ++ tag

-- | Finish a proof. First argument is what we got from the call of 'start' above.
finish :: String -> Int -> KD ()
finish what skip = do KDConfig{kdRibbonLength} <- ask
                      liftIO $ putStrLn $ replicate (kdRibbonLength - skip) ' ' ++ what
