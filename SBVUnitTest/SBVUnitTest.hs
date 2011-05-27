-----------------------------------------------------------------------------
-- |
-- Module      :  Main
-- Copyright   :  (c) Levent Erkok
-- License     :  BSD3
-- Maintainer  :  erkokl@gmail.com
-- Stability   :  experimental
-- Portability :  portable
--
-- SBV library unit-test program
-----------------------------------------------------------------------------

module Main(main, createGolds) where

import Control.Monad           (when)
import System.Directory        (doesDirectoryExist, findExecutable)
import System.Environment      (getArgs, getEnv)
import System.Exit             (exitWith, ExitCode(..))
import System.FilePath         ((</>))
import System.Process          (readProcessWithExitCode)
import Test.HUnit              (Test(..), Counts(..), runTestTT)

import Data.SBV                (yices, SMTSolver(..))
import Data.SBV.Utils.SBVTest  (SBVTestSuite(..), generateGoldCheck)
import Paths_sbv               (getDataDir)

-- To add a new collection of tests, import below and add to testCollection variable
import qualified Data.SBV.TestSuite.Arrays.Memory                  as T01_01(testSuite)
import qualified Data.SBV.TestSuite.Basics.Arithmetic              as T02_01(testSuite)
import qualified Data.SBV.TestSuite.Basics.BasicTests              as T02_02(testSuite)
import qualified Data.SBV.TestSuite.Basics.Higher                  as T02_03(testSuite)
import qualified Data.SBV.TestSuite.Basics.Index                   as T02_04(testSuite)
import qualified Data.SBV.TestSuite.Basics.ProofTests              as T02_05(testSuite)
import qualified Data.SBV.TestSuite.Basics.QRem                    as T02_06(testSuite)
import qualified Data.SBV.TestSuite.BitPrecise.BitTricks           as T03_01(testSuite)
import qualified Data.SBV.TestSuite.BitPrecise.Legato              as T03_02(testSuite)
import qualified Data.SBV.TestSuite.BitPrecise.PrefixSum           as T03_03(testSuite)
import qualified Data.SBV.TestSuite.CRC.CCITT                      as T04_01(testSuite)
import qualified Data.SBV.TestSuite.CRC.CCITT_Unidir               as T04_02(testSuite)
import qualified Data.SBV.TestSuite.CRC.GenPoly                    as T04_03(testSuite)
import qualified Data.SBV.TestSuite.CRC.Parity                     as T04_04(testSuite)
import qualified Data.SBV.TestSuite.CRC.USB5                       as T04_05(testSuite)
import qualified Data.SBV.TestSuite.CodeGeneration.AddSub          as T05_01(testSuite)
import qualified Data.SBV.TestSuite.CodeGeneration.CgTests         as T05_02(testSuite)
import qualified Data.SBV.TestSuite.CodeGeneration.Fibonacci       as T05_03(testSuite)
import qualified Data.SBV.TestSuite.CodeGeneration.GCD             as T05_04(testSuite)
import qualified Data.SBV.TestSuite.CodeGeneration.PopulationCount as T05_05(testSuite)
import qualified Data.SBV.TestSuite.Crypto.AES                     as T06_01(testSuite)
import qualified Data.SBV.TestSuite.Crypto.RC4                     as T06_02(testSuite)
import qualified Data.SBV.TestSuite.Polynomials.Polynomials        as T07_01(testSuite)
import qualified Data.SBV.TestSuite.Puzzles.Counts                 as T08_01(testSuite)
import qualified Data.SBV.TestSuite.Puzzles.DogCatMouse            as T08_02(testSuite)
import qualified Data.SBV.TestSuite.Puzzles.Euler185               as T08_03(testSuite)
import qualified Data.SBV.TestSuite.Puzzles.MagicSquare            as T08_04(testSuite)
import qualified Data.SBV.TestSuite.Puzzles.NQueens                as T08_05(testSuite)
import qualified Data.SBV.TestSuite.Puzzles.PowerSet               as T08_06(testSuite)
import qualified Data.SBV.TestSuite.Puzzles.Sudoku                 as T08_07(testSuite)
import qualified Data.SBV.TestSuite.Puzzles.Temperature            as T08_08(testSuite)
import qualified Data.SBV.TestSuite.Puzzles.U2Bridge               as T08_09(testSuite)
import qualified Data.SBV.TestSuite.Uninterpreted.AUF              as T09_01(testSuite)
import qualified Data.SBV.TestSuite.Uninterpreted.Function         as T09_02(testSuite)
import qualified Data.SBV.TestSuite.Uninterpreted.Uninterpreted    as T09_03(testSuite)

testCollection :: [(String, SBVTestSuite)]
testCollection = [
       ("mem",         T01_01.testSuite)
     , ("arith",       T02_01.testSuite)
     , ("basic",       T02_02.testSuite)
     , ("higher",      T02_03.testSuite)
     , ("index",       T02_04.testSuite)
     , ("proof",       T02_05.testSuite)
     , ("qrem",        T02_06.testSuite)
     , ("bitTricks",   T03_01.testSuite)
     , ("legato",      T03_02.testSuite)
     , ("prefixSum",   T03_03.testSuite)
     , ("ccitt",       T04_01.testSuite)
     , ("ccitt2",      T04_02.testSuite)
     , ("genPoly",     T04_03.testSuite)
     , ("parity",      T04_04.testSuite)
     , ("usb5",        T04_05.testSuite)
     , ("addSub",      T05_01.testSuite)
     , ("cgtest",      T05_02.testSuite)
     , ("fib",         T05_03.testSuite)
     , ("gcd",         T05_04.testSuite)
     , ("popCount",    T05_05.testSuite)
     , ("aes",         T06_01.testSuite)
     , ("rc4",         T06_02.testSuite)
     , ("poly",        T07_01.testSuite)
     , ("counts",      T08_01.testSuite)
     , ("dogCatMouse", T08_02.testSuite)
     , ("euler185",    T08_03.testSuite)
     , ("magicSquare", T08_04.testSuite)
     , ("nQueens",     T08_05.testSuite)
     , ("powerset",    T08_06.testSuite)
     , ("sudoku",      T08_07.testSuite)
     , ("temperature", T08_08.testSuite)
     , ("u2bridge",    T08_09.testSuite)
     , ("auf1",        T09_01.testSuite)
     , ("auf2",        T09_02.testSuite)
     , ("unint",       T09_03.testSuite)
     ]

-- No user serviceable parts below..

main :: IO ()
main = do tgts <- getArgs
          run tgts False []

createGolds :: String -> IO ()
createGolds tgts = run (words tgts) True ["SBVUnitTest/GoldFiles"]

checkGoldDir :: FilePath -> IO ()
checkGoldDir gd = do e <- doesDirectoryExist gd
                     when (not e) $
                             do putStrLn $ "*** Cannot locate gold file repository!"
                                putStrLn $ "*** Please call with one argument, the directory name of the gold files."
                                putStrLn $ "*** Cannot run test cases, exiting."
                                exitWith $ ExitFailure 1

checkYices :: IO ()
checkYices = do ex <- getEnv "SBV_YICES" `catch` (\_ -> return (executable yices))
                mbP <- findExecutable ex
                case mbP of
                  Nothing -> do putStrLn $ "*** Cannot find default SMT solver executable for " ++ nm
                                putStrLn $ "*** Please make sure the executable " ++ show ex
                                putStrLn $ "*** is installed and is in your path."
                                putStrLn $ "*** Cannot run test cases, exiting."
                                exitWith $ ExitFailure 1
                  Just p  -> do putStrLn $ "*** Using solver : " ++ nm ++ " (" ++ show p ++ ")"
                                checkYicesVersion p
 where nm = name yices

checkYicesVersion :: FilePath -> IO ()
checkYicesVersion p =
        do (ec, yOut, _yErr) <- readProcessWithExitCode p ["-V"] ""
           case ec of
             ExitFailure _ -> do putStrLn $ "*** Cannot determine Yices version. Please install Yices version 2.X first."
                                 exitWith $ ExitFailure 1
             ExitSuccess   -> do let isYices1 = take 2 yOut == "1." -- crude test; might fail..
                                 when isYices1 $ putStrLn $ "*** Yices version 1.X is detected. Version 2.X is strongly recommended!"
                                 opts <- getEnv "SBV_YICES_OPTIONS" `catch` (\_ -> return (unwords (options yices)))
                                 when (isYices1 && opts /= "-tc -smt -e") $ do
                                           putStrLn $ "*** Either install Yices 2.X, or set the environment variable:"
                                           putStrLn $ "***     SBV_YICES_OPTIONS=\"-tc -smt -e\""
                                           putStrLn $ "*** To use Yices 1.X with SBV."
                                           putStrLn $ "*** However, upgrading to Yices 2.X is highly recommended!"
                                           exitWith $ ExitFailure 1

run :: [String] -> Bool -> [String] -> IO ()
run targets shouldCreate [gd] =
        do mapM_ checkTgt targets
           putStrLn $ "*** Starting SBV unit tests..\n*** Gold files at: " ++ show gd
           checkGoldDir gd
           checkYices
           cts <- runTestTT $ TestList $ map mkTst [c | (tc, c) <- testCollection, select tc]
           decide shouldCreate cts
  where mkTst (SBVTestSuite f) = f $ generateGoldCheck gd shouldCreate
        select tc = null targets || tc `elem` targets
        checkTgt t | t `elem` allTargets = return ()
                   | True                = do putStrLn $ "*** Unknown test target: " ++ show t
                                              exitWith $ ExitFailure 1
        allTargets = map fst testCollection
run targets shouldCreate [] = getDataDir >>= \d -> run targets shouldCreate [d </> "SBVUnitTest" </> "GoldFiles"]
run _       _            _  = error "SBVUnitTests.run: impossible happened!"

decide :: Bool -> Counts -> IO ()
decide shouldCreate cts@(Counts c t e f) = do
        when (c /= t) $ putStrLn $ "*** Not all test cases were tried. (Only tested " ++ show t ++ " of " ++ show c ++ ")"
        when (e /= 0) $ putStrLn $ "*** " ++ show e ++ " (of " ++ show c ++ ") test cases in error."
        when (f /= 0) $ putStrLn $ "*** " ++ show f ++ " (of " ++ show c ++ ") test cases failed."
        if (c == t && e == 0 && f == 0)
           then do if shouldCreate
                      then putStrLn $ "All " ++ show c ++ " test cases executed in gold-file generation mode."
                      else putStrLn $ "All " ++ show c ++ " test cases successfully passed."
                   exitWith $ ExitSuccess
           else exitWith $ ExitFailure 2
