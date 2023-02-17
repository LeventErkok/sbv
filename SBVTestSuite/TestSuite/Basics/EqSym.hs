-----------------------------------------------------------------------------
-- |
-- Module    : TestSuite.Basics.BasicTests
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Test suite for Examples.Basics.EqSym
-----------------------------------------------------------------------------

{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric  #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module TestSuite.Basics.EqSym(tests) where

import Utils.SBVTestFramework

import Control.Monad (void)
import GHC.Generics

-- Test suite
tests :: TestTree
tests = testGroup "Basics.EqSym"
   [ goldenCapturedIO "check1" $ \rf -> void (isTheoremWith z3{verbose=True, redirectVerbose=Just rf} check1)
   , goldenCapturedIO "check2" $ \rf -> void (isTheoremWith z3{verbose=True, redirectVerbose=Just rf} check2)
   ]

data F = A SWord8 SWord16
       | B SBool
       deriving (Generic, EqSymbolic)

newF :: Symbolic F
newF = A <$> free_ <*> free_

check1 :: Predicate
check1 = do x <- newF
            y <- newF
            pure $ x .== y

check2 :: Predicate
check2 = do x <- newF
            pure $ x ./= x
