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
    , goldenCapturedIO "strExamples9"  $ \rf -> checkWith z3{redirectVerbose=Just rf} strExamples9    Sat
    , goldenCapturedIO "strExamples10" $ \rf -> checkWith z3{redirectVerbose=Just rf} strExamples10   Unsat
    , goldenCapturedIO "strExamples11" $ \rf -> checkWith z3{redirectVerbose=Just rf} strExamples11   Unsat
    , goldenCapturedIO "strExamples12" $ \rf -> checkWith z3{redirectVerbose=Just rf} strExamples12   Unsat
    , goldenCapturedIO "strExamples13" $ \rf -> checkWith z3{redirectVerbose=Just rf} strExamples13   Unsat
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
  constrain $ b `strIsInfixOf` a
  constrain $ c `strIsInfixOf` b
  constrain $ bnot $ c `strIsInfixOf` a

-- But containment is not a linear order.
strExamples7 :: Symbolic ()
strExamples7 = do
  [a, b, c] <- sStrings ["a", "b", "c"]
  constrain $ b `strIsInfixOf` a
  constrain $ c `strIsInfixOf` a
  constrain $ bnot $ c `strIsInfixOf` b
  constrain $ bnot $ b `strIsInfixOf` c

-- Any string is equal to the prefix and suffix that add up to a its length.
strExamples8 :: Symbolic ()
strExamples8 = do
  [a, b, c] <- sStrings ["a", "b", "c"]
  constrain $ b `strIsPrefixOf` a
  constrain $ c `strIsSuffixOf` a
  constrain $ strLen a .== strLen b + strLen c
  constrain $ bnot $ a .== b .++ c

-- The maximal length is 6 for a string of length 2 repeated at most 3 times
strExamples9 :: Symbolic ()
strExamples9 = do
   a <- sString "a"
   constrain $ strMatch a (RE_Loop 1 3 (RE_Literal "ab"))
   constrain $ strLen a .== 6

-- The maximal length is 6 for a string of length 2 repeated at most 3 times
strExamples10 :: Symbolic ()
strExamples10 = do
   a <- sString "a"
   constrain $ strMatch a (RE_Loop 1 3 (RE_Literal "ab"))
   constrain $ strLen a .> 6

-- Conversion from nat to string, only ground terms
strExamples11 :: Symbolic ()
strExamples11 = do
   i <- sInteger "i"
   constrain $ i .== 11
   constrain $ bnot $ strNatToStr i .== "11"

-- Conversion from nat to string, negative values produce empty string
strExamples12 :: Symbolic ()
strExamples12 = do
   i <- sInteger "i"
   constrain $ i .== -2
   constrain $ bnot $ strNatToStr i .== ""

-- Conversion from string to nat, only ground terms
strExamples13 :: Symbolic ()
strExamples13 = do
   s <- sString "s"
   constrain $ s .== "13"
   constrain $ bnot $ strStrToNat s .== 13
