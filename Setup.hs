-----------------------------------------------------------------------------
-- |
-- Module      :  Main
-- Copyright   :  (c) Levent Erkok
-- License     :  BSD3
-- Maintainer  :  erkokl@gmail.com
-- Stability   :  experimental
-- Portability :  portable
--
-- Setup module for the sbv library
-----------------------------------------------------------------------------

{-# OPTIONS_GHC -Wall #-}
module Main(main) where

import Distribution.Simple (defaultMainWithHooks, simpleUserHooks, postInst)
import System.Directory    (findExecutable)
import System.Exit         (exitWith, ExitCode(..))

import Data.SBV.Provers.Prover (SMTSolver(..), yices)

main :: IO ()
main = defaultMainWithHooks simpleUserHooks{ postInst = checkDefSolver }
 where checkDefSolver _ _ _ _ = do
                mbP <- findExecutable ex
                case mbP of
                   Nothing -> do putStrLn $ "*** The sbv library requires the default solver " ++ nm ++ " to be installed."
                                 putStrLn $ "*** The executable " ++ show ex ++ " must be in your path."
                                 putStrLn $ "*** Do not forget to install " ++ nm ++ "!"
                   Just _  -> return ()
                exitWith ExitSuccess
       ex = executable yices
       nm = name yices
