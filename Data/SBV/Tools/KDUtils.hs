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

{-# OPTIONS_GHC -Wall -Werror #-}

module Data.SBV.Tools.KDUtils (
         KD, runKD, runKDWith
       , start, finish
       ) where

import Control.Monad.Reader (ReaderT, runReaderT)
import Control.Monad.Trans  (MonadIO(liftIO))

import Data.List (intercalate)
import System.IO (hFlush, stdout)

-- | Keeping track of KD options/state
data KDConfig = KDConfig

-- | Default KD-config
defaultKDConfig :: KDConfig
defaultKDConfig = KDConfig

-- | Monad for running KnuckleDragger proofs in.
newtype KD a = KD (ReaderT KDConfig IO a)
            deriving newtype (Applicative, Functor, Monad, MonadIO, MonadFail)

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
finish what skip = liftIO $ putStrLn $ replicate (ribbonLength - skip) ' ' ++ what
  where -- Ideally an aestheticly pleasing length of the line. Perhaps this
        -- should be configurable, but this is good enough for now.
        ribbonLength :: Int
        ribbonLength = 40
