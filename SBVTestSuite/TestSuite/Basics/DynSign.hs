-----------------------------------------------------------------------------
-- |
-- Module    : TestSuite.Basics.DynSign
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Test case for <http://github.com/GaloisInc/cryptol/issues/566>
-----------------------------------------------------------------------------

{-# OPTIONS_GHC -Wall -Werror #-}

module TestSuite.Basics.DynSign(tests) where

import Utils.SBVTestFramework hiding (proveWith)

import Data.SBV.Dynamic
import Data.SBV.Internals  (genMkSymVar, unSBV, VarContext(..))

prop :: Symbolic SVal
prop = do x <- unSBV <$> genMkSymVar w8 (NonQueryVar Nothing) (Just "x")
          let lhs = svUnsign (svSign x `svShiftRight` sfour)
              rhs = svExtract 7 0    x `svShiftRight` ufour
          return $ lhs `svEqual` rhs
  where w8, i8 :: Kind
        w8 = kindOf (undefined :: SWord8)
        i8 = kindOf (undefined :: SInt8)
        sfour = svInteger i8 4
        ufour = svInteger w8 4

checkSat :: ThmResult -> Assertion
checkSat r = assert isThm
  where isThm = case r of
                  ThmResult Unsatisfiable{} -> return False :: IO Bool
                  ThmResult Satisfiable{}   -> return True
                  _                         -> error "checkSat: Unexpected result!"

-- Test suite
tests :: TestTree
tests = testGroup "Basics.DynSign"
   [ testCase "dynSign" $ checkSat =<< proveWith z3 prop
   ]
