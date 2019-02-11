-----------------------------------------------------------------------------
-- |
-- Module    : TestSuite.Basics.Sum
-- Copyright : (c) Joel Burget
--                 Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Test the sum functions.
-----------------------------------------------------------------------------

{-# LANGUAGE TypeApplications #-}

module TestSuite.Basics.Sum(tests)  where

import Prelude hiding (either)
import Control.Monad (unless)

import Data.SBV.Control
import Utils.SBVTestFramework

import Data.SBV.Either
import Data.SBV.Maybe  as M

-- Test suite
tests :: TestTree
tests =
  testGroup "Basics.Sum" [
      goldenCapturedIO "sumEitherSat"  $ \rf -> checkWith z3{redirectVerbose=Just rf} sumEitherSat  Sat
    , goldenCapturedIO "sumBimapPlus"  $ \rf -> checkWith z3{redirectVerbose=Just rf} sumBimapPlus  Sat
    , goldenCapturedIO "sumLiftEither" $ \rf -> checkWith z3{redirectVerbose=Just rf} sumLiftEither Sat
    , goldenCapturedIO "sumMaybe"      $ \rf -> checkWith z3{redirectVerbose=Just rf} sumMaybe      Sat
    , goldenCapturedIO "sumLiftMaybe"  $ \rf -> checkWith z3{redirectVerbose=Just rf} sumLiftMaybe  Sat
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

-- Test 'either'
sumEitherSat :: Symbolic ()
sumEitherSat = do
  x <- sEither @Integer @Bool "x"
  constrain $ either (.> 0) sNot x

-- Test 'bimap' and 'either'
sumBimapPlus :: Symbolic ()
sumBimapPlus = do
  x <- sEither @Integer @Integer "x"
  let x'    = bimap (+1) (+1) x
      xval  = either id id x
      x'val = either id id x'
  constrain $ x'val .== xval + 1

-- Test 'liftEither', 'sLeft', 'right', 'isLeft', and 'isRight'
sumLiftEither :: Symbolic ()
sumLiftEither = do
  i <- sInteger "i"
  c <- sChar "c"

  constrain $ liftEither @Integer @Char (Left i) .== sLeft i
  constrain $ isLeft     @Integer @Char (sLeft i)

  constrain $ liftEither @Integer @Char (Right c) .== sRight c
  constrain $ isRight    @Integer @Char (sRight c)

-- Test 'sMaybe', 'map', 'isNothing', 'isJust', and 'maybe'
sumMaybe :: Symbolic ()
sumMaybe = do
  x <- sMaybe @Integer "x"
  let x' = M.map (+1) x
  constrain $ isNothing x .== isNothing x'
  constrain $ isJust x    .== isJust x'

  let extract = M.maybe 0 id
  constrain $ extract x .== extract x' - 1

-- Test 'liftMaybe' and 'just'
sumLiftMaybe :: Symbolic ()
sumLiftMaybe = do
  i <- sInteger "i"
  constrain $ liftMaybe (Just i) .== sJust i
  constrain $ sNothing ./= sJust i
