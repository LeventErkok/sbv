-----------------------------------------------------------------------------
-- |
-- Module    : TestSuite.Basics.List
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Test the sequence/list functions.
-----------------------------------------------------------------------------

{-# LANGUAGE OverloadedLists     #-}
{-# LANGUAGE ScopedTypeVariables #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module TestSuite.Basics.List(tests)  where

import Data.SBV.Control
import Utils.SBVTestFramework

import           Prelude hiding ((++), (!!))
import qualified Prelude as P   ((++))

import Data.SBV.List ((!!), (++))
import qualified Data.SBV.List as L

import Control.Monad (unless)
import Data.Maybe (catMaybes)
import Data.List (sort)

-- Test suite
tests :: TestTree
tests =
  testGroup "Basics.List" [
      goldenCapturedIO "seqConcat"     $ \rf -> checkWith z3{redirectVerbose=Just rf} seqConcatSat    Sat
    , goldenCapturedIO "seqConcatBad"  $ \rf -> checkWith z3{redirectVerbose=Just rf} seqConcatUnsat  Unsat
    , goldenCapturedIO "seqIndexOf"    $ \rf -> checkWith z3{redirectVerbose=Just rf} seqIndexOfSat   Sat
    , goldenCapturedIO "seqIndexOfBad" $ \rf -> checkWith z3{redirectVerbose=Just rf} seqIndexOfUnsat Unsat
    , goldenCapturedIO "seqExamples1"  $ \rf -> checkWith z3{redirectVerbose=Just rf} seqExamples1    Sat
    , goldenCapturedIO "seqExamples2"  $ \rf -> checkWith z3{redirectVerbose=Just rf} seqExamples2    Unsat
    , goldenCapturedIO "seqExamples3"  $ \rf -> checkWith z3{redirectVerbose=Just rf} seqExamples3    Sat
    , goldenCapturedIO "seqExamples4"  $ \rf -> checkWith z3{redirectVerbose=Just rf} seqExamples4    Sat
    , goldenCapturedIO "seqExamples5"  $ \rf -> checkWith z3{redirectVerbose=Just rf} seqExamples5    Sat
    , goldenCapturedIO "seqExamples6"  $ \rf -> checkWith z3{redirectVerbose=Just rf} seqExamples6    Unsat
    , goldenCapturedIO "seqExamples7"  $ \rf -> checkWith z3{redirectVerbose=Just rf} seqExamples7    Sat
    , goldenCapturedIO "seqExamples8"  $ \rf -> checkWith z3{redirectVerbose=Just rf} seqExamples8    Unsat
    , testCase         "seqExamples9"  $ assert seqExamples9
    ]

checkWith :: SMTConfig -> Symbolic () -> CheckSatResult -> IO ()
checkWith cfg props csExpected = runSMTWith cfg{verbose=True} $ do
        _ <- props
        query $ do cs <- checkSat
                   unless (cs == csExpected) $
                     case cs of
                       Unsat  -> error "Failed! Expected Sat, got UNSAT"
                       DSat{} -> error "Failed! Expected Sat, got delta-sat"
                       Sat    -> getModel         >>= \r -> error $ "Failed! Expected Unsat, got SAT:\n" P.++ show (SatResult (Satisfiable cfg r))
                       Unk    -> getUnknownReason >>= \r -> error $ "Failed! Expected Unsat, got UNK:\n" P.++ show r

seqConcatSat :: Symbolic ()
seqConcatSat = constrain $ [1..3] ++ [4..6] .== ([1..6] :: SList Integer)

seqConcatUnsat :: Symbolic ()
seqConcatUnsat = constrain $ [1..3] ++ [4..6] .== ([1..7] :: SList Integer)

seqIndexOfSat :: Symbolic ()
seqIndexOfSat = constrain $ L.indexOf ([1,2,3,1,2,3] :: SList Integer) [1] .== 0

seqIndexOfUnsat :: Symbolic ()
seqIndexOfUnsat = constrain $ L.indexOf ([1,2,3,1,2,3] :: SList Integer) [1] ./= 0

-- Basic sequence operations
seqExamples1 :: Symbolic ()
seqExamples1 = constrain $ sAnd
  [ L.singleton (([1,2,3] :: SList Integer) !! 1) ++ L.singleton (([1,2,3] :: SList Integer) !! 0) .== [2,1]
  , ([1,2,3,1,2,3] :: SList Integer) `L.indexOf` [1]                                               .== 0
  , L.offsetIndexOf ([1,2,3,1,2,3] :: SList Integer) [1] 1                                         .== 3
  , L.subList ([4,4,1,2,3,5,5] :: SList Integer)     2 3                                           .== [1,2,3]
  ]

-- A list cannot overlap with two different elements
seqExamples2 :: Symbolic ()
seqExamples2 = do
  a :: SList Integer <- sList "a"
  constrain $ a ++ [2] .== [1] ++ a

-- Strings a, b, c can have a non-trivial overlap.
seqExamples3 :: Symbolic ()
seqExamples3 = do
  [a, b, c :: SList Integer] <- sLists ["a", "b", "c"]
  constrain $ a ++ b .== [1..4]
  constrain $ b ++ c .== [3..6]
  constrain $ sNot $ b .== []

-- There is a solution to a of length at most 2.
seqExamples4 :: Symbolic ()
seqExamples4 = do
  [a, b :: SList Integer] <- sLists ["a", "b"]
  constrain $ [1..3] ++ a .== b ++ [3..5]
  constrain $ L.length a .<= 2

-- There is a solution to a that is not a sequence of 1's.
seqExamples5 :: Symbolic ()
seqExamples5 = do
  [a, b, c :: SList Integer] <- sLists ["a", "b", "c"]
  constrain $ a ++ [1,2] ++ b .== b ++ [2,1] ++ c
  constrain $ c .== a ++ b
  constrain $ sNot $ a ++ [1] .== [1] ++ a

-- Contains is transitive.
seqExamples6 :: Symbolic ()
seqExamples6 = do
  [a, b, c :: SList Integer] <- sLists ["a", "b", "c"]
  constrain $ b `L.isInfixOf` a
  constrain $ c `L.isInfixOf` b
  constrain $ sNot $ c `L.isInfixOf` a

-- But containment is not a linear order.
seqExamples7 :: Symbolic ()
seqExamples7 = do
  [a, b, c :: SList Integer] <- sLists ["a", "b", "c"]
  constrain $ b `L.isInfixOf` a
  constrain $ c `L.isInfixOf` a
  constrain $ sNot $ c `L.isInfixOf` b
  constrain $ sNot $ b `L.isInfixOf` c

-- Any string is equal to the prefix and suffix that add up to a its length.
seqExamples8 :: Symbolic ()
seqExamples8 = do
  [a, b, c :: SList Integer] <- sLists ["a", "b", "c"]
  constrain $ b `L.isPrefixOf` a
  constrain $ c `L.isSuffixOf` a
  constrain $ L.length a .== L.length b + L.length c
  constrain $ sNot $ a .== b ++ c

-- Generate all length one sequences, to enumerate all and making sure we can parse correctly
seqExamples9 :: IO Bool
seqExamples9 = do m <- allSat $ do (s :: SList Word8) <- sList "s"
                                   return $ L.length s .== 1

                  let vals :: [Word8]
                      vals = sort $ concat (catMaybes (getModelValues "s" m) :: [[Word8]])

                  return $ vals == [0..255]
