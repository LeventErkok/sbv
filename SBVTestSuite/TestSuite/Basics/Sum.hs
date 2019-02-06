{-# language TypeApplications #-}
-----------------------------------------------------------------------------
-- |
-- Module    : TestSuite.Basics.Sum
-- Author    : Joel Burget, Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Test the sum functions.
-----------------------------------------------------------------------------

module TestSuite.Basics.Sum(tests)  where

import Control.Monad (unless)

import Data.SBV.Control
import Utils.SBVTestFramework

import Data.SBV.Sum

-- Test suite
tests :: TestTree
tests =
  testGroup "Basics.Sum" [
      goldenCapturedIO "sumEitherSat" $ \rf -> checkWith z3{redirectVerbose=Just rf} sumEitherSat    Sat
    , goldenCapturedIO "sumBimapPlus" $ \rf -> checkWith z3{redirectVerbose=Just rf} sumBimapPlus    Sat
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

sumEitherSat :: Symbolic ()
sumEitherSat = do
  x <- sSum @Integer @Bool "x"
  constrain $ case_ x (.>0) sNot

sumBimapPlus :: Symbolic ()
sumBimapPlus = do
  x <- sSum @Integer @Integer "x"
  let x'    = bimap (+1) (+1) x
      xval  = case_ x  id id
      x'val = case_ x' id id
  constrain $ x'val .== xval + 1
