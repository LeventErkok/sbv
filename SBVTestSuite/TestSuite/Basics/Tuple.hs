-----------------------------------------------------------------------------
-- |
-- Module      :  TestSuite.Basics.Tuple
-- Copyright   :  (c) Levent Erkok
-- License     :  BSD3
-- Maintainer  :  erkokl@gmail.com
-- Stability   :  experimental
--
-- Test tuples.
-----------------------------------------------------------------------------

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeApplications #-}

module TestSuite.Basics.Tuple(tests)  where

import Data.SBV (HList)
import Data.SBV.Control
import Data.SBV.Tuple
import Utils.SBVTestFramework

import Control.Monad (unless)

-- Test suite
tests :: TestTree
tests =
  testGroup "Basics.Tuple" [
      goldenCapturedIO "tupleSwap"     $ \rf -> checkWith z3{redirectVerbose=Just rf} tupleSwapSat    Sat
    , goldenCapturedIO "twoTwoTuples"  $ \rf -> checkWith z3{redirectVerbose=Just rf} twoTwoTuples    Sat
    , goldenCapturedIO "hlist"         $ \rf -> checkWith z3{redirectVerbose=Just rf} hlist           Sat
    , goldenCapturedIO "nested"        $ \rf -> checkWith z3{redirectVerbose=Just rf} nested          Sat
    ]

checkWith :: SMTConfig -> Symbolic () -> CheckSatResult -> IO ()
checkWith cfg props csExpected = runSMTWith cfg{verbose=True} $ do
        _ <- props
        query $ do cs <- checkSat
                   unless (cs == csExpected) $
                     case cs of
                       Unsat -> error "Failed! Expected Sat, got UNSAT"
                       Sat   -> getModel         >>= \r -> error $ "Failed! Expected Unsat, got SAT:\n" ++ show (SatResult (Satisfiable cfg r))
                       Unk   -> getUnknownReason >>= \r -> error $ "Failed! Expected Unsat, got UNK:\n" ++ show r

tupleSwapSat :: Symbolic ()
tupleSwapSat = do
  [abx, bay] <- sTuples @(Integer, Integer, Integer) ["abx", "bay"]
  constrain $ field1 abx .== field2 bay
  constrain $ field2 abx .== field1 bay

twoTwoTuples :: Symbolic ()
twoTwoTuples = do
  ab <- sTuple @(Integer, String) "ab"
  cd <- sTuple @(Char,    Word8)  "cd"
  constrain $ field1 ab .== 1
  constrain $ field1 cd .== literal 'c'

hlist :: Symbolic ()
hlist = do
  abcd <- sTuple @(HList [Integer, String, Char, Word8]) "abcd"
  constrain $ field1 abcd .== 1
  constrain $ field2 abcd .== literal "foo"
  constrain $ field3 abcd .== literal 'c'
  constrain $ field4 abcd .== 0

nested :: Symbolic ()
nested = do
  abcd <- sTuple @((Integer, (String, Char)), Word8) "abcd"
  constrain $         field1 (field1 abcd)  .== 1
  constrain $ field1 (field2 (field1 abcd)) .== literal "foo"
  constrain $ field2 (field2 (field1 abcd)) .== literal 'c'
  constrain $                 field2 abcd   .== 0
