{-# LANGUAGE OverloadedStrings #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  TestSuite.Basics.String
-- Copyright   :  (c) Levent Erkok
-- License     :  BSD3
-- Maintainer  :  erkokl@gmail.com
-- Stability   :  experimental
--
-- Test the string functions.
-- Most of these tests are adopted from <https://rise4fun.com/z3/tutorialcontent/sequences>
-----------------------------------------------------------------------------

module TestSuite.Basics.String(tests)  where

import Data.SBV.Control
import Utils.SBVTestFramework

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
    ]

-- to test interactively, use:
--    checkWith z3 propPbAtLeast

checkWith :: SMTConfig -> Symbolic () -> CheckSatResult -> IO ()
checkWith cfg props csExpected = runSMTWith cfg{verbose=True} $ do
        _ <- props
        query $ do cs <- checkSat
                   if cs == csExpected
                   then return ()
                   else case cs of
                     Unsat -> error "Failed! Expected Sat, got UNSAT"
                     Sat   -> getModel         >>= \r -> error $ "Failed! Expected Unsat, got SAT:\n" ++ show (SatResult (Satisfiable cfg r))
                     Unk   -> getUnknownReason >>= \r -> error $ "Failed! Expected Unsat, got UNK:\n" ++ show r

strConcatSat :: Symbolic ()
strConcatSat = constrain $ strConcat "abc" "def" .== "abcdef"

strConcatUnsat :: Symbolic ()
strConcatUnsat = constrain $ strConcat "abc" "def" .== "abcdefg"

strIndexOfSat :: Symbolic ()
strIndexOfSat = constrain $ strIndexOf "abcabc" "a" .== 0

strIndexOfUnsat :: Symbolic ()
strIndexOfUnsat = constrain $ strIndexOf "abcabc" "a" ./= 0

-- Basic string operations
strExamples1 :: Symbolic ()
strExamples1 = constrain $ bAnd
  [ strAt "abc" 1 .++ strAt "abc" 0 .== "ba"
  , strIndexOf "abcabc" "a"         .== 0
  , strOffsetIndexOf "abcabc" "a" 1 .== 3
  , strSubstr "xxabcyy" 2 3         .== "abc"
  ]

-- A string cannot overlap with two different characters.
strExamples2 :: Symbolic ()
strExamples2 = do
  a <- sString "a"
  constrain $ a .++ "b" .== "a" .++ a

-- Strings a, b, c can have a non-trivial overlap.
strExamples3 :: Symbolic ()
strExamples3 = do
  [a, b, c] <- sStrings ["a", "b", "c"]
  constrain $ a .++ b .== "abcd"
  constrain $ b .++ c .== "cdef"
  constrain $ bnot $ b .== ""

-- There is a solution to a of length at most 2.
strExamples4 :: Symbolic ()
strExamples4 = do
  [a, b] <- sStrings ["a", "b"]
  constrain $ "abc" .++ a .== b .++ "cef"
  constrain $ strLen a .<= 2

-- There is a solution to a that is not a sequence of "a"'s.
strExamples5 :: Symbolic ()
strExamples5 = do
  [a, b, c] <- sStrings ["a", "b", "c"]
  constrain $ a .++ "ab" .++ b .== b .++ "ba" .++ c
  constrain $ c .== a .++ b
  constrain $ bnot $ a.++ "a" .== "a" .++ a

-- Contains is transitive.
strExamples6 :: Symbolic ()
strExamples6 = do
  [a, b, c] <- sStrings ["a", "b", "c"]
  constrain $ a `strContains` b
  constrain $ b `strContains` c
  constrain $ bnot $ a `strContains` c

-- But containment is not a linear order.
strExamples7 :: Symbolic ()
strExamples7 = do
  [a, b, c] <- sStrings ["a", "b", "c"]
  constrain $ a `strContains` b
  constrain $ a `strContains` c
  constrain $ bnot $ b `strContains` c
  constrain $ bnot $ c `strContains` b

-- Any string is equal to the prefix and suffix that add up to a its length.
strExamples8 :: Symbolic ()
strExamples8 = do
  [a, b, c] <- sStrings ["a", "b", "c"]
  constrain $ strPrefixOf b a
  constrain $ strSuffixOf c a
  constrain $ strLen a .== strLen b + strLen c
  constrain $ bnot $ a .== b .++ c
