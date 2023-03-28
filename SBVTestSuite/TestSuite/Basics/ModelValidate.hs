-----------------------------------------------------------------------------
-- |
-- Module    : TestSuite.Basics.ModelValidate
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Few validate tests
-----------------------------------------------------------------------------

{-# LANGUAGE ScopedTypeVariables #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module TestSuite.Basics.ModelValidate (testsABC, tests)  where

import qualified Control.Exception as C
import Data.List (isPrefixOf)

import Utils.SBVTestFramework

-- Test suite, this needs ABC
testsABC :: TestTree
testsABC = testGroup "Basics.ModelValidate.ABC" [
             goldenCapturedIO "validate_0" testABC
           ]
    where testABC goldFile = do r <- satWith abc{verbose=True, redirectVerbose = Just goldFile, validateModel = True} (free "x" >>= \x -> pure $ x .< (10::SWord8))
                                appendFile goldFile ("\nFINAL OUTPUT:\n" ++ show r ++ "\n")

tests :: TestTree
tests = testGroup "Basics.ModelValidate" [
             goldenCapturedIO "validate_1" $ t  satWith    t1
           , goldenCapturedIO "validate_2" $ t  satWith    t2
           , goldenCapturedIO "validate_3" $ t  satWith    t3
           , goldenCapturedIO "validate_4" $ t  proveWith  t3
           , goldenCapturedIO "validate_5" $ t  satWith    t4
           , goldenCapturedIO "validate_6" $ t  proveWith  t4
           , goldenCapturedIO "validate_7" $ tE satWith    t5
           ]
    where t f test goldFile = do r <- f defaultSMTCfg{verbose=True, redirectVerbose = Just goldFile, validateModel = True} test
                                 appendFile goldFile ("\nFINAL OUTPUT:\n" ++ show r ++ "\n")

          tE f test goldFile = do r <- f defaultSMTCfg{verbose=True, redirectVerbose = Just goldFile, validateModel = True} test
                                  appendFile goldFile ("\nFINAL OUTPUT:\n" ++ show r ++ "\n")
                               `C.catch` (\(e::C.SomeException) -> appendFile goldFile ("\nEXCEPTION RAISED:\n" ++ pick (show e) ++ "\n"))
              where pick s = unlines [l | l <- lines s, "***" `isPrefixOf` l]

          t1, t2 :: Predicate
          t1 = free "x" >>= \x -> pure $ fpAdd sRTZ x x   .== (x::SFloat)
          t2 = free "x" >>= \x -> pure $ fpFMA sRNE x x x .== (x::SFloat)

          t3 :: Predicate
          t3 = do x <- sInteger "x"
                  constrain $ x .> x   -- Constraining with False! i.e., any theorem will follow, and will be trivially unsat
                  pure sFalse

          t4 :: Predicate
          t4 = do x <- sInteger "x"
                  y <- sInteger "y"
                  constrain $ x .> y
                  constrain $ x .> 12
                  return $ x .== y+3

          t5 :: Predicate
          t5 = do x <- free "x"
                  pure $ quantifiedBool $ \(Forall y) -> fpIsPoint y .=> x .<= (y::SFloat)
