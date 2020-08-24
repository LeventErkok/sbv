-----------------------------------------------------------------------------
-- |
-- Module    : TestSuite.Basics.SmallShifts
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Testing small-shift amounts using the dynamic interface. See
-- http://github.com/LeventErkok/sbv/issues/323 for the genesis.
-----------------------------------------------------------------------------

{-# OPTIONS_GHC -Wall -Werror #-}

module TestSuite.Basics.SmallShifts(tests) where

import Utils.SBVTestFramework hiding (proveWith)

import Data.SBV.Dynamic
import Data.SBV.Internals  (genMkSymVar, unSBV, VarContext(..))

k1, k32, k33 :: Kind
k1   = KBounded False  1
k32  = KBounded False 32
k33  = KBounded False 33
type SW32 = SVal
type SW33 = SVal
type SW1  = SVal

b0 :: SW1
b0 = svInteger k1 0

b1 :: SW1
b1 = svInteger k1 1

average33 :: SW32 -> SW32 -> SW32
average33 x y = svExtract 31 0 (z' `svDivide` svInteger k33 2)
    where z' :: SW33
          z' = (b0 `svJoin` x) `svPlus` (b0 `svJoin` y)

average4 :: SW32 -> SW32 -> SW32
average4 x y =   ((x `svShiftRight` b1) `svPlus` (y `svShiftRight` b1))
                `svPlus` (x `svAnd` (y `svAnd` svInteger k32 1))

prop :: Symbolic SVal
prop = do x <- unSBV <$> genMkSymVar k32 (NonQueryVar Nothing) (Just "x")
          y <- unSBV <$> genMkSymVar k32 (NonQueryVar Nothing) (Just "y")
          return $ average33 x y `svEqual` average4 x y

checkThm :: ThmResult -> Assertion
checkThm r = assert isThm
  where isThm = case r of
                  ThmResult Unsatisfiable{} -> return True :: IO Bool
                  ThmResult Satisfiable{}   -> return False
                  _                         -> error "checkThm: Unexpected result!"

-- Test suite
tests :: TestTree
tests = testGroup "Basics.SmallShifts"
   [ testCase "smallShift" $ checkThm =<< proveWith z3 prop
   ]
