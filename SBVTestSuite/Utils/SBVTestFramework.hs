-----------------------------------------------------------------------------
-- |
-- Module      :  Utils.SBVTestFramework
-- Copyright   :  (c) Levent Erkok
-- License     :  BSD3
-- Maintainer  :  erkokl@gmail.com
-- Stability   :  experimental
--
-- Various goodies for testing SBV
-----------------------------------------------------------------------------

{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Utils.SBVTestFramework (
          showsAs
        , runSAT, numberOfModels
        , assert, assertIsThm, assertIsntThm, assertIsSat, assertIsntSat
        , goldenString
        , goldenVsStringShow
        , goldenCapturedIO
        , CIOS(..), TestEnvironment(..), getTestEnvironment
        , qc1, qc2
        , pickTests
        -- module exports to simplify life
        , module Test.Tasty
        , module Test.Tasty.HUnit
        , module Data.SBV
        ) where

import qualified Control.Exception as C

import Control.Monad.Trans (liftIO)

import qualified Data.ByteString.Lazy.Char8 as LBC
import qualified Data.ByteString as BS

import System.Directory   (removeFile)
import System.Environment (lookupEnv)

import Test.Tasty            (testGroup, TestTree, TestName)
import Test.Tasty.HUnit      ((@?), Assertion, testCase, AssertionPredicable)

import Test.Tasty.Golden           (goldenVsString)
import Test.Tasty.Golden.Advanced  (goldenTest)

import qualified Test.Tasty.QuickCheck   as QC
import qualified Test.QuickCheck.Monadic as QC

import Test.Tasty.Runners hiding (Result)
import System.Random (randomRIO)

import Data.SBV
import Data.SBV.Control

import Data.Char (chr, ord, isDigit)

import Data.Maybe(fromMaybe, catMaybes)

import System.FilePath ((</>), (<.>))

import Data.SBV.Internals (runSymbolic, Symbolic, Result, SBVRunMode(..), IStage(..), SBV(..), SVal(..), showModel, SMTModel(..))

---------------------------------------------------------------------------------------
-- Test environment; continuous integration
data CIOS = CILinux
          | CIOSX
          | CIWindows
          deriving (Show, Eq)

data TestEnvironment = TestEnvLocal
                     | TestEnvCI CIOS
                     | TestEnvUnknown
                     deriving Show

getTestEnvironment :: IO (TestEnvironment, Int)
getTestEnvironment = do mbTestEnv  <- lookupEnv "SBV_TEST_ENVIRONMENT"
                        mbTestPerc <- lookupEnv "SBV_HEAVYTEST_PERCENTAGE"

                        env <- case mbTestEnv of
                                 Just "local" -> return   TestEnvLocal
                                 Just "linux" -> return $ TestEnvCI CILinux
                                 Just "osx"   -> return $ TestEnvCI CIOSX
                                 Just "win"   -> return $ TestEnvCI CIWindows
                                 Just other   -> do putStrLn $ "Ignoring unexpected test env value: " ++ show other
                                                    return TestEnvUnknown
                                 Nothing      -> return TestEnvUnknown

                        perc <- case mbTestPerc of
                                 Just n | all isDigit n -> return (read n)
                                 Just n                 -> do putStrLn $ "Ignoring unexpected test percentage value: " ++ show n
                                                              return 100
                                 Nothing                -> return 100

                        return (env, perc)

-- | Generic assertion. This is less safe than usual, but will do.
assert :: AssertionPredicable t => t -> Assertion
assert t = t @? "assertion-failure"

-- | Checks that a particular result shows as @s@
showsAs :: Show a => a -> String -> Assertion
showsAs r s = assert $ show r == s

goldFile :: FilePath -> FilePath
goldFile nm = "SBVTestSuite" </> "GoldFiles" </> nm <.> "gold"

goldenString :: TestName -> IO String -> TestTree
goldenString n res = goldenVsString n (goldFile n) (fmap LBC.pack res)

goldenVsStringShow :: Show a => TestName -> IO a -> TestTree
goldenVsStringShow n res = goldenVsString n (goldFile n) (fmap (LBC.pack . show) res)

goldenCapturedIO :: TestName -> (FilePath -> IO ()) -> TestTree
goldenCapturedIO n res = doTheDiff n gf gfTmp (rm gfTmp >> res gfTmp)
  where gf    = goldFile n
        gfTmp = gf ++ "_temp"

        rm f = removeFile f `C.catch` (\(_ :: C.SomeException) -> return ())

-- | When comparing ignore \r's for windows's sake
doTheDiff :: TestName -> FilePath -> FilePath -> IO () -> TestTree
doTheDiff nm ref new act = goldenTest nm (BS.readFile ref) (act >> BS.readFile new) cmp upd
   where upd = BS.writeFile ref

         cmp :: BS.ByteString -> BS.ByteString -> IO (Maybe String)
         cmp x y
          | cleanUp x == cleanUp y = return Nothing
          | True                   = return $ Just $ unlines $ [ "Discrepancy found. Expected: " ++ ref
                                                                 , "============================================"
                                                                 ]
                                                              ++ lines xs
                                                              ++ [ "Got: " ++ new
                                                                 , "============================================"
                                                                 ]
                                                              ++ lines ys
          where xs = map (chr . fromIntegral) $ BS.unpack x
                ys = map (chr . fromIntegral) $ BS.unpack y

         -- deal with insane Windows \r stuff
         cleanUp = BS.filter (/= slashr)
         slashr  = fromIntegral (ord '\r')

-- | Count the number of models
numberOfModels :: Provable a => a -> IO Int
numberOfModels p = do AllSatResult (_, _, rs) <- allSat p
                      return $ length rs

-- | Symbolicly run a SAT instance using the default config
runSAT :: Symbolic a -> IO Result
runSAT cmp = snd <$> runSymbolic (SMTMode ISetup True defaultSMTCfg) cmp

-- | Turn provable to an assertion, theorem case
assertIsThm :: Provable a => a -> Assertion
assertIsThm t = assert (isTheorem t)

-- | Turn provable to a negative assertion, theorem case
assertIsntThm :: Provable a => a -> Assertion
assertIsntThm t = assert (fmap not (isTheorem t))

-- | Turn provable to an assertion, satisfiability case
assertIsSat :: Provable a => a -> Assertion
assertIsSat p = assert (isSatisfiable p)

-- | Turn provable to a negative assertion, satisfiability case
assertIsntSat :: Provable a => a -> Assertion
assertIsntSat p = assert (fmap not (isSatisfiable p))

-- | Quick-check a unary function, creating one version for constant folding, and another for solver
qc1 :: (SymWord a, SymWord b, Show a, QC.Arbitrary a, SMTValue b) => String -> (a -> b) -> (SBV a -> SBV b) -> [TestTree]
qc1 nm opC opS = [cf, sm]
   where cf = QC.testProperty (nm ++ ".constantFold") $ do
                        i <- free "i"

                        let extract n = fromMaybe (error $ "qc1." ++ nm ++ ": Cannot extract value for: " ++ n) . unliteral

                            v = extract "i" i

                            expected = literal $ opC v
                            result   = opS i

                        observe "Expected" expected
                        observe "Result"   result

                        case (unliteral expected, unliteral result) of
                           (Just _, Just _) -> return $ expected .== result
                           _                -> return false

         sm = QC.testProperty (nm ++ ".symbolic") $ QC.monadicIO $ do
                        ((i, expected), result) <- QC.run $ runSMT $ do v   <- liftIO $ QC.generate QC.arbitrary
                                                                        i   <- free_
                                                                        res <- free_

                                                                        constrain $ i   .== literal v
                                                                        constrain $ res .== opS i

                                                                        let pre = (v, opC v)

                                                                        query $ do cs <- checkSat
                                                                                   case cs of
                                                                                     Unk   -> return (pre, Left "Unexpected: Solver responded Unknown!")
                                                                                     Unsat -> return (pre, Left "Unexpected: Solver responded Unsatisfiable!")
                                                                                     Sat   -> do r <- getValue res
                                                                                                 return (pre, Right r)

                        let getCW vnm (SBV (SVal _ (Left c))) = (vnm, c)
                            getCW vnm (SBV (SVal k _       )) = error $ "qc2.getCW: Impossible happened, non-CW value while extracting: " ++ show (vnm, k)

                            vals = [ getCW "i"        (literal i)
                                   , getCW "Expected" (literal expected)
                                   ]

                            model = case result of
                                      Right v -> showModel defaultSMTCfg (SMTModel [] (vals ++ [getCW "Result" (literal v)]))
                                      Left  e -> showModel defaultSMTCfg (SMTModel [] vals) ++ "\n" ++ e

                        QC.monitor (QC.counterexample model)

                        case result of
                           Right a -> QC.assert $ expected == a
                           _       -> QC.assert False


-- | Quick-check a binary function, creating one version for constant folding, and another for solver
qc2 :: (SymWord a, SymWord b, SymWord c, Show a, Show b, QC.Arbitrary a, QC.Arbitrary b, SMTValue c) => String -> (a -> b -> c) -> (SBV a -> SBV b -> SBV c) -> [TestTree]
qc2 nm opC opS = [cf, sm]
   where cf = QC.testProperty (nm ++ ".constantFold") $ do
                        i1 <- free "i1"
                        i2 <- free "i2"

                        let extract n = fromMaybe (error $ "qc2." ++ nm ++ ": Cannot extract value for: " ++ n) . unliteral

                            v1 = extract "i1" i1
                            v2 = extract "i2" i2

                            expected = literal $ opC v1 v2
                            result   = opS i1 i2

                        observe "Expected" expected
                        observe "Result"   result

                        case (unliteral expected, unliteral result) of
                           (Just _, Just _) -> return $ expected .== result
                           _                -> return false

         sm = QC.testProperty (nm ++ ".symbolic") $ QC.monadicIO $ do
                        ((i1, i2, expected), result) <- QC.run $ runSMT $ do v1  <- liftIO $ QC.generate QC.arbitrary
                                                                             v2  <- liftIO $ QC.generate QC.arbitrary
                                                                             i1  <- free_
                                                                             i2  <- free_
                                                                             res <- free_

                                                                             constrain $ i1  .== literal v1
                                                                             constrain $ i2  .== literal v2
                                                                             constrain $ res .== i1 `opS` i2

                                                                             let pre = (v1, v2, v1 `opC` v2)

                                                                             query $ do cs <- checkSat
                                                                                        case cs of
                                                                                          Unk   -> return (pre, Left "Unexpected: Solver responded Unknown!")
                                                                                          Unsat -> return (pre, Left "Unexpected: Solver responded Unsatisfiable!")
                                                                                          Sat   -> do r <- getValue res
                                                                                                      return (pre, Right r)

                        let getCW vnm (SBV (SVal _ (Left c))) = (vnm, c)
                            getCW vnm (SBV (SVal k _       )) = error $ "qc2.getCW: Impossible happened, non-CW value while extracting: " ++ show (vnm, k)

                            vals = [ getCW "i1"       (literal i1)
                                   , getCW "i2"       (literal i2)
                                   , getCW "Expected" (literal expected)
                                   ]

                            model = case result of
                                      Right v -> showModel defaultSMTCfg (SMTModel [] (vals ++ [getCW "Result" (literal v)]))
                                      Left  e -> showModel defaultSMTCfg (SMTModel [] vals) ++ "\n" ++ e

                        QC.monitor (QC.counterexample model)

                        case result of
                           Right a -> QC.assert $ expected == a
                           _       -> QC.assert False

-- | Picking a certain percent of tests.
pickTests :: Int -> TestTree -> IO TestTree
pickTests d origTests = fromMaybe noTestsSelected <$> walk origTests
   where noTestsSelected = TestGroup "pickTests.NoTestsSelected" []

         walk PlusTestOptions{} = error "pickTests: Unexpected PlusTestOptions"
         walk WithResource{}    = error "pickTests: Unexpected WithResource"
         walk AskOptions{}      = error "pickTests: Unexpected AskOptions"
         walk t@SingleTest{}    = do c <- randomRIO (0, 99)
                                     if c < d
                                        then return $ Just t
                                        else return Nothing
         walk (TestGroup tn ts) = do cs <- catMaybes <$> mapM walk ts
                                     case cs of
                                       [] -> return Nothing
                                       _  -> return $ Just $ TestGroup tn cs

{-# ANN module ("HLint: ignore Reduce duplication" :: String) #-}
