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

{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications    #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module TestSuite.Basics.Sum(tests)  where

import Prelude hiding (either)
import Control.Monad (unless, when)

import Data.SBV.Control
import Utils.SBVTestFramework

import Data.SBV.Either
import Data.SBV.Maybe  as M

-- Test suite
tests :: TestTree
tests =
  testGroup "Basics.Sum" [
      goldenCapturedIO "sumEitherSat"    $ \rf -> checkWith rf z3{redirectVerbose=Just rf} sumEitherSat    Sat
    , goldenCapturedIO "sumBimapPlus"    $ \rf -> checkWith rf z3{redirectVerbose=Just rf} sumBimapPlus    Sat
    , goldenCapturedIO "sumLiftEither"   $ \rf -> checkWith rf z3{redirectVerbose=Just rf} sumLiftEither   Sat
    , goldenCapturedIO "sumMaybe"        $ \rf -> checkWith rf z3{redirectVerbose=Just rf} sumMaybe        Sat
    , goldenCapturedIO "sumLiftMaybe"    $ \rf -> checkWith rf z3{redirectVerbose=Just rf} sumLiftMaybe    Sat
    , goldenCapturedIO "sumMaybeBoth"    $ \rf -> checkWith rf z3{redirectVerbose=Just rf} sumMaybeBoth    Sat
    , goldenCapturedIO "sumMergeMaybe1"  $ \rf -> checkWith rf z3{redirectVerbose=Just rf} sumMergeMaybe1  Sat
    , goldenCapturedIO "sumMergeMaybe2"  $ \rf -> checkWith rf z3{redirectVerbose=Just rf} sumMergeMaybe2  Sat
    , goldenCapturedIO "sumMergeEither1" $ \rf -> checkWith rf z3{redirectVerbose=Just rf} sumMergeEither1 Sat
    , goldenCapturedIO "sumMergeEither2" $ \rf -> checkWith rf z3{redirectVerbose=Just rf} sumMergeEither2 Sat
    ]

checkWith :: FilePath -> SMTConfig -> Symbolic () -> CheckSatResult -> IO ()
checkWith rf cfg props csExpected = runSMTWith cfg{verbose=True} $ do
        _ <- props
        query $ do cs <- checkSat
                   unless (cs == csExpected) $
                     case cs of
                       Unsat  -> error "Failed! Expected Sat, got UNSAT"
                       DSat{} -> error "Failed! Expected Sat, got delta-sat"
                       Sat    -> getModel         >>= \r -> error $ "Failed! Expected Unsat, got SAT:\n" ++ show (SatResult (Satisfiable cfg r))
                       Unk    -> getUnknownReason >>= \r -> error $ "Failed! Expected Unsat, got UNK:\n" ++ show r
                   when (cs == Sat) $
                       getModel >>= \m -> io $ appendFile rf $ "\nMODEL: " ++ show m ++ "\nDONE."


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

-- Test either/maybe together
sumMaybeBoth :: Symbolic ()
sumMaybeBoth = do
   (x :: SEither Integer Integer) <- sEither_
   (y :: SMaybe Integer)          <- sMaybe_

   constrain $ isLeft x
   constrain $ isJust y

sumMergeMaybe1 :: Symbolic ()
sumMergeMaybe1 = do
   (x :: SMaybe Integer) <- sMaybe_
   (y :: SMaybe Integer) <- sMaybe_
   b  <- sBool_

   constrain $ isNothing $ ite b x y

sumMergeMaybe2 :: Symbolic ()
sumMergeMaybe2 = do
   (x :: SMaybe Integer) <- sMaybe_
   (y :: SMaybe Integer) <- sMaybe_
   b  <- sBool_

   constrain $ isJust $ ite b x y

sumMergeEither1 :: Symbolic ()
sumMergeEither1 = do
   (x :: SEither Integer Bool) <- sEither_
   (y :: SEither Integer Bool) <- sEither_
   b  <- sBool_

   constrain $ isLeft $ ite b x y

sumMergeEither2 :: Symbolic ()
sumMergeEither2 = do
   (x :: SEither Integer Bool) <- sEither_
   (y :: SEither Integer Bool) <- sEither_
   b  <- sBool_

   constrain $ isRight $ ite b x y

{- HLint ignore module "Reduce duplication" -}
