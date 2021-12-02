-----------------------------------------------------------------------------
-- |
-- Module    : TestSuite.Basics.String
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Test the string functions.
-----------------------------------------------------------------------------

{-# LANGUAGE OverloadedStrings #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module TestSuite.Basics.String(tests)  where

import Data.SBV.Control
import Utils.SBVTestFramework

import Prelude hiding ((!!), (++))
import qualified Prelude as P ((++))

import Data.SBV.String ((!!), (++))
import qualified Data.SBV.String as S
import qualified Data.SBV.Char   as SC
import qualified Data.SBV.RegExp as R

import Control.Monad (unless)
import Data.List (sort)

import qualified Data.Map.Strict as M

import qualified Data.Char as C

-- Test suite
tests :: TestTree
tests =
  testGroup "Basics.String" [
      goldenCapturedIO "strConcat"     $ \rf -> checkWith z3{redirectVerbose=Just rf} strConcatSat    Sat
    , goldenCapturedIO "strConcatBad"  $ \rf -> checkWith z3{redirectVerbose=Just rf} strConcatUnsat  Unsat
    , goldenCapturedIO "strIndexOf"    $ \rf -> checkWith z3{redirectVerbose=Just rf} strIndexOfSat   Sat
    , goldenCapturedIO "strIndexOfBad" $ \rf -> checkWith z3{redirectVerbose=Just rf} strIndexOfUnsat Unsat
    , goldenCapturedIO "strExamples1"  $ \rf -> checkWith z3{redirectVerbose=Just rf} strExamples1    Sat
    , goldenCapturedIO "strExamples2"  $ \rf -> checkWith z3{redirectVerbose=Just rf} strExamples2    Unsat
    , goldenCapturedIO "strExamples3"  $ \rf -> checkWith z3{redirectVerbose=Just rf} strExamples3    Sat
    , goldenCapturedIO "strExamples4"  $ \rf -> checkWith z3{redirectVerbose=Just rf} strExamples4    Sat
    , goldenCapturedIO "strExamples5"  $ \rf -> checkWith z3{redirectVerbose=Just rf} strExamples5    Sat
    , goldenCapturedIO "strExamples6"  $ \rf -> checkWith z3{redirectVerbose=Just rf} strExamples6    Unsat
    , goldenCapturedIO "strExamples7"  $ \rf -> checkWith z3{redirectVerbose=Just rf} strExamples7    Sat
    , goldenCapturedIO "strExamples8"  $ \rf -> checkWith z3{redirectVerbose=Just rf} strExamples8    Unsat
    , goldenCapturedIO "strExamples9"  $ \rf -> checkWith z3{redirectVerbose=Just rf} strExamples9    Sat
    , goldenCapturedIO "strExamples10" $ \rf -> checkWith z3{redirectVerbose=Just rf} strExamples10   Unsat
    , goldenCapturedIO "strExamples11" $ \rf -> checkWith z3{redirectVerbose=Just rf} strExamples11   Unsat
    , goldenCapturedIO "strExamples12" $ \rf -> checkWith z3{redirectVerbose=Just rf} strExamples12   Unsat
    , goldenCapturedIO "strExamples13" $ \rf -> checkWith z3{redirectVerbose=Just rf} strExamples13   Unsat
    , testCase         "strExamples14" $ assert strExamples14
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

strConcatSat :: Symbolic ()
strConcatSat = constrain $ "abc" ++ "def" .== "abcdef"

strConcatUnsat :: Symbolic ()
strConcatUnsat = constrain $ "abc" ++ "def" .== "abcdefg"

strIndexOfSat :: Symbolic ()
strIndexOfSat = constrain $ S.indexOf "abcabc" "a" .== 0

strIndexOfUnsat :: Symbolic ()
strIndexOfUnsat = constrain $ S.indexOf "abcabc" "a" ./= 0

-- Basic string operations
strExamples1 :: Symbolic ()
strExamples1 = constrain $ sAnd
  [ S.singleton ("abc" !! 1) ++ S.singleton ("abc" !! 0) .== "ba"
  , "abcabc" `S.indexOf` "a"                              .== 0
  , S.offsetIndexOf "abcabc" "a" 1                        .== 3
  , S.subStr "xxabcyy" 2 3                                .== "abc"
  ]

-- A string cannot overlap with two different characters.
strExamples2 :: Symbolic ()
strExamples2 = do
  a <- sString "a"
  constrain $ a ++ "b" .== "a" ++ a

-- Strings a, b, c can have a non-trivial overlap.
strExamples3 :: Symbolic ()
strExamples3 = do
  [a, b, c] <- sStrings ["a", "b", "c"]
  constrain $ a ++ b .== "abcd"
  constrain $ b ++ c .== "cdef"
  constrain $ sNot $ b .== ""

-- There is a solution to a of length at most 2.
strExamples4 :: Symbolic ()
strExamples4 = do
  [a, b] <- sStrings ["a", "b"]
  constrain $ "abc" ++ a .== b ++ "cef"
  constrain $ S.length a .<= 2

-- There is a solution to a that is not a sequence of "a"'s.
strExamples5 :: Symbolic ()
strExamples5 = do
  [a, b, c] <- sStrings ["a", "b", "c"]
  constrain $ a ++ "ab" ++ b .== b ++ "ba" ++ c
  constrain $ c .== a ++ b
  constrain $ sNot $ a ++ "a" .== "a" ++ a

-- Contains is transitive.
strExamples6 :: Symbolic ()
strExamples6 = do
  [a, b, c] <- sStrings ["a", "b", "c"]
  constrain $ b `S.isInfixOf` a
  constrain $ c `S.isInfixOf` b
  constrain $ sNot $ c `S.isInfixOf` a

-- But containment is not a linear order.
strExamples7 :: Symbolic ()
strExamples7 = do
  [a, b, c] <- sStrings ["a", "b", "c"]
  constrain $ b `S.isInfixOf` a
  constrain $ c `S.isInfixOf` a
  constrain $ sNot $ c `S.isInfixOf` b
  constrain $ sNot $ b `S.isInfixOf` c

-- Any string is equal to the prefix and suffix that add up to a its length.
strExamples8 :: Symbolic ()
strExamples8 = do
  [a, b, c] <- sStrings ["a", "b", "c"]
  constrain $ b `S.isPrefixOf` a
  constrain $ c `S.isSuffixOf` a
  constrain $ S.length a .== S.length b + S.length c
  constrain $ sNot $ a .== b ++ c

-- The maximal length is 6 for a string of length 2 repeated at most 3 times
strExamples9 :: Symbolic ()
strExamples9 = do
   a <- sString "a"
   constrain $ R.match a (R.Loop 1 3 "ab")
   constrain $ S.length a .== 6

-- The maximal length is 6 for a string of length 2 repeated at most 3 times
strExamples10 :: Symbolic ()
strExamples10 = do
   a <- sString "a"
   constrain $ R.match a (R.Loop 1 3 "ab")
   constrain $ S.length a .> 6

-- Conversion from nat to string, only ground terms
strExamples11 :: Symbolic ()
strExamples11 = do
   i <- sInteger "i"
   constrain $ i .== 11
   constrain $ sNot $ S.natToStr i .== "11"

-- Conversion from nat to string, negative values produce empty string
strExamples12 :: Symbolic ()
strExamples12 = do
   i <- sInteger "i"
   constrain $ i .== -2
   constrain $ sNot $ S.natToStr i .== ""

-- Conversion from string to nat, only ground terms
strExamples13 :: Symbolic ()
strExamples13 = do
   s <- sString "s"
   constrain $ s .== "13"
   constrain $ sNot $ S.strToNat s .== 13

-- Generate all length one strings consisting of letters A-Z, to enumerate all and making sure we can parse correctly
strExamples14 :: IO Bool
strExamples14 = do m <- allSat $ do s <- sString "s"
                                    let c = SC.ord (S.head s)
                                    constrain $ c .>= SC.ord (literal 'A')
                                    constrain $ c .<= SC.ord (literal 'Z')
                                    return $ S.length s .== 1
                   let dicts = getModelDictionaries m

                       vals :: [Int]
                       vals = map C.ord $ concat $ sort $ map (fromCV . snd) (concatMap M.assocs dicts)

                   case length dicts of
                     26 -> return $ vals == map C.ord ['A' .. 'Z']
                     _   -> return False
