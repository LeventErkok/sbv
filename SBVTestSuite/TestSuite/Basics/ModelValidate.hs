-----------------------------------------------------------------------------
-- |
-- Module    : TestSuite.Basics.ModelValidate
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Make sure the ABC bug is there, and a few other validate tests.
-----------------------------------------------------------------------------

module TestSuite.Basics.ModelValidate (testsABC, tests)  where

import Utils.SBVTestFramework

-- Test suite, this needs ABC
testsABC :: TestTree
testsABC = testGroup "Basics.ModelValidate.ABC" [
             goldenCapturedIO "abc_badValidate" badABC
           ]
    where badABC goldFile = do r <- satWith abc{verbose=True, redirectVerbose = Just goldFile, validateModel = True} $ forSome ["x"] $ \x -> x .< (10::SWord8)
                               appendFile goldFile ("\nFINAL OUTPUT:\n" ++ show r ++ "\n")

tests :: TestTree
tests = testGroup "Basics.ModelValidate" [
             goldenCapturedIO "validate_1" $ t satWith   t1
           , goldenCapturedIO "validate_2" $ t satWith   t2
           , goldenCapturedIO "validate_3" $ t satWith   t3
           , goldenCapturedIO "validate_4" $ t proveWith t3
           , goldenCapturedIO "validate_5" $ t satWith   t4
           , goldenCapturedIO "validate_6" $ t proveWith t4
           ]
    where t f test goldFile = do r <- f defaultSMTCfg{verbose=True, redirectVerbose = Just goldFile, validateModel = True} test
                                 appendFile goldFile ("\nFINAL OUTPUT:\n" ++ show r ++ "\n")

          t1 = forSome ["x"] $ \x -> fpAdd sRTZ x x   .== (x::SFloat)
          t2 = forSome ["x"] $ \x -> fpFMA sRNE x x x .== (x::SFloat)

          t3 = do x <- sInteger "x"
                  constrain $ x .> x

          t4 = do x <- sInteger "x"
                  y <- sInteger "y"
                  constrain $ x .> y
                  return $ x .== y+3
