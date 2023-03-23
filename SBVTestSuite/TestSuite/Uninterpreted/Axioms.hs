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
    [ goldenCapturedIO "unint-axioms"       $ \rf -> isTheoremWith z3{verbose=True, redirectVerbose=Just rf} p0 >>= \r -> appendFile rf ("\n FINAL:" ++ show r ++ "\nDONE!\n")
    , goldenCapturedIO "unint-axioms-empty" $ \rf -> isTheoremWith z3{verbose=True, redirectVerbose=Just rf} p1 >>= \r -> appendFile rf ("\n FINAL:" ++ show r ++ "\nDONE!\n")
    , goldenCapturedIO "unint-axioms-query" testQuery
    ]

a :: SBitstring -> SBool
a = uninterpret "a"

e :: SBitstring -> SBitstring -> SBitstring
e = uninterpret "e"

p0 :: Symbolic SBool
p0 = do
    constrain $ \(Forall p) (Forall k) -> a k .&& a p .=> a (e k p)
    p <- free "p" :: Symbolic SBitstring
    k <- free "k" :: Symbolic SBitstring
    constrain $ a p
    constrain $ a k
    return $ a (e k p)

thingCompare :: SThing -> SThing -> SBV Bool
thingCompare = uninterpret "thingCompare"

thingMerge :: SThing -> SThing -> SThing
thingMerge = uninterpret "thingMerge"

p1 :: Symbolic SBool
p1 = do constrain $ \(Forall x) -> thingCompare x x
        constrain $ \(Forall k1) (Forall k2) -> k1 ./= thingMerge k1 k2
        registerUISMTFunction thingMerge
        k1 <- free_
        k2 <- free_
        return $ k1 .== k2 .=> thingCompare k1 k2

testQuery :: FilePath -> IO ()
testQuery rf = do r <- runSMTWith defaultSMTCfg{verbose=True, redirectVerbose=Just rf} t
                  appendFile rf ("\n FINAL:" ++ show r ++ "\nDONE!\n")
 where t = do vp <- free "p"
              vq <- free "q"
              vr <- free "r"
              query $ do let oR, aND :: SB  -> SB -> SB
                             oR  = uninterpret "OR"
                             aND = uninterpret "AND"
                             nOT :: SB -> SB
                             nOT = uninterpret "NOT"
                         constrain  $ nOT (vp `oR` (vq `aND` vr)) ./= (nOT vp `aND` nOT vq) `oR` (nOT vp `aND` nOT vr)
                         constrain $ \(Forall p) (Forall q) (Forall r) -> (p `oR` q) `aND` (p `oR` r) .== p `oR` (q `aND` r)
                         constrain $ \(Forall p) (Forall q)            -> nOT (p `oR` q) .== nOT p `aND` nOT q
                         constrain $ \(Forall p)                       -> nOT (nOT p) .== p
                         checkSat
