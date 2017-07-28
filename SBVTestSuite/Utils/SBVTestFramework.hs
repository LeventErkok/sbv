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
        , assertIsThm, assertIsntThm, assertIsSat, assertIsntSat
        , goldenString
        , goldenVsStringShow
        , goldenCapturedIO
        , TravisOS(..), TestEnvironment(..), getTestEnvironment
        , pickTests
        -- module exports to simplify life
        , module Test.Tasty
        , module Test.Tasty.HUnit
        , module Data.SBV
        ) where

import qualified Control.Exception as C

import qualified Data.ByteString.Lazy.Char8 as LBC

import System.Directory   (removeFile)
import System.Environment (lookupEnv)

import Test.Tasty         (testGroup, TestTree, TestName)
import Test.Tasty.Golden  (goldenVsString, goldenVsFile)
import Test.Tasty.HUnit   (assert, Assertion, testCase)

import Test.Tasty.Runners hiding (Result)
import System.Random (randomRIO)

import Data.SBV

import System.FilePath ((</>), (<.>))

import Data.SBV.Internals (runSymbolic, Symbolic, Result, SBVRunMode(..), IStage(..))

---------------------------------------------------------------------------------------
-- Test environment
data TravisOS = TravisLinux
              | TravisOSX
              | TravisWindows    -- Travis actually doesn't support windows yet. This is "reserved" for future
              deriving Show

data TestEnvironment = TestEnvLocal
                     | TestEnvTravis TravisOS
                     | TestEnvUnknown
                     deriving Show

getTestEnvironment :: IO TestEnvironment
getTestEnvironment = do mbTestEnv <- lookupEnv "SBV_TEST_ENVIRONMENT"

                        case mbTestEnv of
                          Just "local" -> return   TestEnvLocal
                          Just "linux" -> return $ TestEnvTravis TravisLinux
                          Just "osx"   -> return $ TestEnvTravis TravisOSX
                          Just "win"   -> return $ TestEnvTravis TravisWindows
                          Just other   -> do putStrLn $ "Ignoring unexpected test env value: " ++ show other
                                             return TestEnvUnknown
                          Nothing      -> return TestEnvUnknown

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
goldenCapturedIO n res = goldenVsFile n gf gfTmp (rm gfTmp >> res gfTmp)
  where gf    = goldFile n
        gfTmp = gf ++ "_temp"

        rm f = removeFile f `C.catch` (\(_ :: C.SomeException) -> return ())

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

-- | Picking a certain percent of tests.
data Picker = Picker (IO (Maybe TestTree))
instance Monoid Picker where
   mempty = Picker (return Nothing)
   Picker t1 `mappend` Picker t2 = Picker $ merge <$> t1 <*> t2
     where merge Nothing  b         = b
           merge a        Nothing   = a
           merge (Just t) (Just t') = case (t, t') of
                                        (a@SingleTest{}, b@SingleTest{})   -> Just $ TestGroup "pickTests.combined" [a, b]
                                        (a@SingleTest{}, TestGroup n g)    -> Just $ TestGroup n (a:g)
                                        (TestGroup n g,   a@SingleTest{})  -> Just $ TestGroup n (g ++ [a])
                                        (TestGroup n1 g1, TestGroup n2 g2) -> Just $ if n1 == n2 then TestGroup n1 (g1 ++ g2)
                                                                                                 else TestGroup "pickTests.combined" [t, t']
                                        _ -> error "pickTests: Unexpected case!"

-- | Given a percentage of tests to run, pickTests returns approximately that many percent of tests, randomly picked.
pickTests :: Integer -> TestTree -> IO TestTree
pickTests d origTests
   | d ==   0 = return noTestSelected
   | d == 100 = return origTests
   | True     = fromPicker <$> foldTestTree trivialFold{foldSingle = fs, foldGroup = fg} mempty $ origTests
  where fs _ n t = Picker $ do c <- randomRIO (0, 99)
                               if c < d
                               then return (Just (SingleTest n t))
                               else return Nothing

        fg tn (Picker iot) = Picker $ do mbt <- iot
                                         case mbt of
                                           Nothing -> return Nothing
                                           Just t  -> case t of
                                                        SingleTest{}      -> return $ Just $ TestGroup tn [t]
                                                        TestGroup _ g     -> return $ Just $ TestGroup tn (concatMap getTests g)
                                                        PlusTestOptions{} -> error "pickTests: Unexpected PlusTestOptions"
                                                        WithResource{}    -> error "pickTests: Unexpected WithResource"
                                                        AskOptions{}      -> error "pickTests: Unexpected AskOptions"
                              where getTests (TestGroup "pickTests.combined" ts) = concatMap getTests ts
                                    getTests t                                   = [t]

        fromPicker (Picker iot) = do mbt <- iot
                                     case mbt of
                                       Nothing -> return noTestSelected
                                       Just t  -> return t

        noTestSelected = TestGroup "pickTests.NoTestsSelected" []
