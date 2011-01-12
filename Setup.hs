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

import Control.Monad(when)
import Distribution.PackageDescription
import Distribution.Simple
import Distribution.Simple.LocalBuildInfo(LocalBuildInfo(..))
import Distribution.Text(display)
import System.Directory(findExecutable)
import System.Process(system)
import System.Exit
import Data.SBV.Provers.Prover(SMTSolver(..), SMTConfig(..), defaultSMTCfg)

main :: IO ()
main = defaultMainWithHooks simpleUserHooks{ runTests = unittest True, postInst = unittest False}
 where checkDefSolver = do
                let ex = executable $ solver $ defaultSMTCfg
                    nm = name $ solver $ defaultSMTCfg
                mbP <- findExecutable ex
                case mbP of
                  Nothing -> do putStrLn $ "*** The sbv library requires the default solver " ++ nm ++ " to be installed."
                                putStrLn $ "*** The executable " ++ show ex ++ " must be in your path."
                                putStrLn $ "*** Do not forget to install " ++ nm ++ "!"
                  Just _  -> return ()
       unittest forced _ _ _ lbi = do
         let testers = [ex | ex <- executables pkgDesc, modulePath ex == "SBVUnitTest/SBVUnitTest.hs"]
         case testers of
           [tp] -> runTester tp
           _    -> bailOut
         where pkgDesc  = localPkgDescr lbi
               sbvName  = display $ package pkgDesc
               report  = putStrLn $ "*** Please report to the maintainer: " ++ maintainer pkgDesc
               bailOut = do putStrLn "*** Cannot find SBV unit-tester program!"
                            report
                            exitWith $ ExitFailure 1
               runTester tp = do
                        when (not forced) $
                                case lookup "x-run-unittests" (customFieldsBI (buildInfo tp)) of
                                        Just "False" -> do checkDefSolver
                                                           putStrLn "*** Please run \"SBVUnitTests\" executable to perform unit-tests."
                                                           putStrLn $ "*** Package " ++ sbvName ++ " installed successfully. Enjoy!"
                                                           putStrLn $ "*** Further info: " ++ homepage pkgDesc
                                                           exitWith ExitSuccess
                                        _            -> return ()
                        mbP <- findExecutable $ exeName tp
                        case mbP of
                          Nothing -> bailOut
                          Just p  -> do ec <- system p
                                        case ec of
                                          ExitSuccess   -> putStrLn $ sbvName ++ " installed and unit-tests successfully run. Enjoy!"
                                          ExitFailure n -> if n == 1 --  couldn't run test cases..
                                                           then putStrLn "*** SBV unit-tests failed! Bailing out."
                                                           else putStrLn "*** Some SBV unit-tests failed!" >> report
                                        exitWith ec
