-----------------------------------------------------------------------------
-- |
-- Module    : TestSuite.Basics.UISat
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Testing UI function sat examples
-----------------------------------------------------------------------------

module TestSuite.Basics.UISat(tests)  where

import Utils.SBVTestFramework

-- Test suite
tests :: TestTree
tests =
  testGroup "Basics.UIAllSat" [
      goldenCapturedIO "uiSat_test1" $ \rf -> checkWith rf test1
    , goldenCapturedIO "uiSat_test2" $ \rf -> checkWith rf test2
    , goldenCapturedIO "uiSat_test3" $ \rf -> checkWith rf test3
    ]

cfg :: FilePath -> SMTConfig
cfg rf = z3 { verbose             = True
            , redirectVerbose     = Just rf
            , allSatMaxModelCount = Just 80
            , isNonModelVar       = (`elem` ["nx", "ny", "nz"])
            }

checkWith :: FilePath -> Goal -> IO ()
checkWith rf prop = do r <- allSatWith (cfg rf) prop
                       appendFile rf $ "\nRESULT: " ++ show r

q1 :: SBool -> SBool
q1 = uninterpret "q1"

q2 :: SBool -> SBool -> SBool
q2 = uninterpret "q2"

test1 :: Goal
test1 = do setLogic Logic_ALL
           x <- free "nx"
           constrain $ q1 x .== q1 x

test2 :: Goal
test2 = do setLogic Logic_ALL
           x <- free "nx"
           y <- free "ny"
           constrain $ q2 x y .== q2 x y

test3 :: Goal
test3 = do setLogic Logic_ALL
           x <- free "nx"
           y <- free "ny"
           constrain $ q1 x   .== q1 x
           constrain $ q2 x y .== q2 x y
