-----------------------------------------------------------------------------
-- |
-- Module    : TestSuite.Basics.Recursive
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Some recursive definitions.
-----------------------------------------------------------------------------

{-# OPTIONS_GHC -Wall -Werror #-}

module TestSuite.Basics.Recursive(tests) where

import Utils.SBVTestFramework

import Data.SBV.Internals  (genMkSymVar, unSBV, VarContext(..))

import qualified Data.SBV.Dynamic as D

-- This is recursive and suffers from the termination problem.
-- But we can still prove a few things about it!
mgcd :: SWord8 -> SWord8 -> SWord8
mgcd a b = ite (b .== 0) a (mgcd b (a `sMod` b))

-- Same construction, expressed in terms of the dynamic interface
mgcdDyn :: Int -> IO ThmResult
mgcdDyn i = D.proveWith z3 $ do

              let var8 :: String -> Symbolic D.SVal
                  var8 nm = unSBV <$> genMkSymVar word8 (NonQueryVar (Just D.ALL)) (Just nm)

                  word8   = KBounded False 8
                  zero8   = D.svInteger word8 0

                  gcdDyn a b = D.svIte (b `D.svEqual` zero8) a (gcdDyn b (a `D.svRem` b))

              x <- var8 "x"

              let prop0 = gcdDyn zero8 x `D.svEqual` x
                  prop1 = gcdDyn x zero8 `D.svEqual` x

              return $  if i == 0 then prop0 else prop1

checkThm :: ThmResult -> Assertion
checkThm r = assert isThm
  where isThm = case r of
                  ThmResult Unsatisfiable{} -> return True :: IO Bool
                  ThmResult Satisfiable{}   -> return False
                  _                         -> error "checkThm: Unexpected result!"

-- Test suite
tests :: TestTree
tests = testGroup "Basics.Recursive"
   [ testCase "recursive1"    $ assertIsThm $ \x -> mgcd    0 x .== x
   , testCase "recursive2"    $ assertIsThm $ \x -> mgcd    x 0 .== x
   , testCase "recursiveDyn1" $ checkThm =<< mgcdDyn 0
   , testCase "recursiveDyn2" $ checkThm =<< mgcdDyn 1
   ]
