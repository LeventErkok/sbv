-----------------------------------------------------------------------------
-- |
-- Module    : TestSuite.Basics.Tuple
-- Author    : Joel Burget
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Test tuples.
-----------------------------------------------------------------------------

{-# LANGUAGE DataKinds        #-}
{-# LANGUAGE TypeApplications #-}

module TestSuite.Basics.Tuple (tests)  where

import Control.Monad (unless)

import Data.SBV.Control
import Data.SBV.List ((.!!))
import Data.SBV.Tuple

import Utils.SBVTestFramework

-- Test suite
tests :: TestTree
tests =
  testGroup "Basics.Tuple" [
      goldenCapturedIO "tupleSwap"     $ \rf -> checkWith z3{redirectVerbose=Just rf} tupleSwapSat    Sat
    , goldenCapturedIO "twoTwoTuples"  $ \rf -> checkWith z3{redirectVerbose=Just rf} twoTwoTuples    Sat
    , goldenCapturedIO "nested"        $ \rf -> checkWith z3{redirectVerbose=Just rf} nested          Sat
    , goldenCapturedIO "list"          $ \rf -> checkWith z3{redirectVerbose=Just rf} list            Sat
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
  constrain $ abx^._1 .== bay^._2
  constrain $ abx^._2 .== bay^._1

twoTwoTuples :: Symbolic ()
twoTwoTuples = do
  ab <- sTuple @(Integer, String) "ab"
  cd <- sTuple @(Char,    Word8)  "cd"
  constrain $ ab^._1 .== 1
  constrain $ cd^._1 .== literal 'c'

nested :: Symbolic ()
nested = do
  abcd <- sTuple @((Integer, (String, Char)), Word8) "abcd"
  constrain $     abcd^._1^._1 .== 1
  constrain $ abcd^._1^._2^._1 .== literal "foo"
  constrain $ abcd^._1^._2^._2 .== literal 'c'
  constrain $         abcd^._2 .== 0

list :: Symbolic ()
list = do
  lst <- sList @(Integer, [(Integer, String)]) "lst"
  constrain $ (lst .!! 0)^._1 .== 2
  constrain $ (((lst .!! 1)^._2) .!! 1)^._2 .== literal "foo"

{-# ANN module ("HLint: ignore Use ." :: String) #-}
