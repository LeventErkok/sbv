-----------------------------------------------------------------------------
-- |
-- Module    : TestSuite.Uninterpreted.Axioms
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Test suite for basic axioms and uninterpreted functions
-----------------------------------------------------------------------------

{-# LANGUAGE DeriveAnyClass     #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell    #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module TestSuite.Uninterpreted.Axioms(tests) where

import Utils.SBVTestFramework

import Data.SBV.Control

data Bitstring
data B
data Thing

mkUninterpretedSort ''Bitstring
mkUninterpretedSort ''B
mkUninterpretedSort ''Thing

tests :: TestTree
tests =
  testGroup "Uninterpreted.Axioms"
    [ testCase         "unint-axioms"       (assertIsThm p0)
    , testCase         "unint-axioms-empty" (assertIsThm p1)
    , goldenCapturedIO "unint-axioms-query" testQuery
    ]

a :: SBitstring -> SBool
a = uninterpret "a"

e :: SBitstring -> SBitstring -> SBitstring
e = uninterpret "e"

axE :: [String]
axE = [ "(assert (forall ((p Bitstring) (k Bitstring))"
      , "         (=> (and (a k) (a p)) (a (e k p)))))"
      ]

p0 :: Symbolic SBool
p0 = do
    p <- free "p" :: Symbolic SBitstring
    k <- free "k" :: Symbolic SBitstring
    addAxiom "axE" axE
    constrain $ a p
    constrain $ a k
    return $ a (e k p)

axThings :: [String]
axThings = [ -- thingCompare is reflexive
             "(assert (forall ((k1 Thing))"
           , "  (thingCompare k1 k1)))"
           -- thingMerge produces a new, distinct thing
           , "(assert (forall ((k1 Thing) (k2 Thing))"
           , "  (distinct k1 (thingMerge k1 k2))))"
           ]

thingCompare :: SThing -> SThing -> SBV Bool
thingCompare = uninterpret "thingCompare"

thingMerge :: SThing -> SThing -> SThing
thingMerge = uninterpret "thingMerge"

p1 :: Symbolic SBool
p1 = do addAxiom "things" axThings
        registerUISMTFunction thingMerge
        k1 <- sbvForall_
        k2 <- sbvForall_
        return $ k1 .== k2 .=> thingCompare k1 k2

testQuery :: FilePath -> IO ()
testQuery rf = do r <- runSMTWith defaultSMTCfg{verbose=True, redirectVerbose=Just rf} t
                  appendFile rf ("\n FINAL:" ++ show r ++ "\nDONE!\n")
 where t = do p <- free "p"
              q <- free "q"
              r <- free "r"
              query $ do let oR, aND :: SB  -> SB -> SB
                             oR  = uninterpret "OR"
                             aND = uninterpret "AND"
                             nOT :: SB -> SB
                             nOT = uninterpret "NOT"
                         constrain $ nOT (p `oR` (q `aND` r)) ./= (nOT p `aND` nOT q) `oR` (nOT p `aND` nOT r)
                         addAxiom "OR distributes over AND" [ "(assert (forall ((p B) (q B) (r B))"
                                                            , "   (= (AND (OR p q) (OR p r))"
                                                            , "      (OR p (AND q r)))))"
                                                            ]
                         addAxiom "de Morgan"               [ "(assert (forall ((p B) (q B))"
                                                            , "   (= (NOT (OR p q))"
                                                            , "      (AND (NOT p) (NOT q)))))"
                                                            ]
                         addAxiom "double negation"         ["(assert (forall ((p B)) (= (NOT (NOT p)) p)))"]
                         checkSat
