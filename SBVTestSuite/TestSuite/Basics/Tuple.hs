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

import           Control.Monad          (unless)

import           Data.SBV.Control
import qualified Data.SBV.List          as L
import           Data.SBV.Tuple
import           Utils.SBVTestFramework

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
  constrain $ _1 abx .== _2 bay
  constrain $ _2 abx .== _1 bay

twoTwoTuples :: Symbolic ()
twoTwoTuples = do
  ab <- sTuple @(Integer, String) "ab"
  cd <- sTuple @(Char,    Word8)  "cd"
  constrain $ _1 ab .== 1
  constrain $ _1 cd .== literal 'c'

nested :: Symbolic ()
nested = do
  abcd <- sTuple @((Integer, (String, Char)), Word8) "abcd"
  constrain $     _1 (_1 abcd)  .== 1
  constrain $ _1 (_2 (_1 abcd)) .== literal "foo"
  constrain $ _2 (_2 (_1 abcd)) .== literal 'c'
  constrain $         _2 abcd   .== 0

list :: Symbolic ()
list = do
  lst <- sList @(Integer, [(Integer, String)]) "lst"
  constrain $                   _1 (L.elemAt lst 0) .== 2
  constrain $ _2 (L.elemAt (_2 (L.elemAt lst 1)) 1) .== literal "foo"
