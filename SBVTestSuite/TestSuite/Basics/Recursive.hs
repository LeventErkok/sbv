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

{-# LANGUAGE ScopedTypeVariables #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module TestSuite.Basics.Recursive(tests) where

import Utils.SBVTestFramework

import Data.SBV.Internals  (genMkSymVar, unSBV, VarContext(..))

import Data.List (isInfixOf)

import qualified Data.SBV.Dynamic as D

import qualified Control.Exception as C

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

-- | Test that a recursive smtFunction without a measure is rejected
recursiveNoMeasure :: Assertion
recursiveNoMeasure = do
  r <- C.try $ sat $ \(x :: SInteger) -> f x .== x
  case r of
    Left (e :: C.SomeException) -> if "missing termination measure" `isInfixOf` show e
                                      then pure ()
                                      else assertFailure $ "Unexpected exception: " ++ show e
    Right _                     -> assertFailure "Expected error for recursive function without measure"
  where f :: SInteger -> SInteger
        f = smtFunction "recF" NoMeasure $ \x -> ite (x .<= 0) 0 (1 + f (x - 1))

-- | Test that a non-recursive smtFunction without a measure is accepted
nonRecursiveNoMeasure :: Assertion
nonRecursiveNoMeasure = assertIsSat $ \(x :: SInteger) -> g x .== 4
  where g :: SInteger -> SInteger
        g = smtFunction "nonRecG" NoMeasure $ \x -> 2 * x

-- Test suite
tests :: TestTree
tests = testGroup "Basics.Recursive"
   [ testCase "recursive1"              $ assertIsThm $ \x -> mgcd    0 x .== x
   , testCase "recursive2"              $ assertIsThm $ \x -> mgcd    x 0 .== x
   , testCase "recursiveDyn1"           $ checkThm =<< mgcdDyn 0
   , testCase "recursiveDyn2"           $ checkThm =<< mgcdDyn 1
   , testCase "recursiveNoMeasure"      recursiveNoMeasure
   , testCase "nonRecursiveNoMeasure"   nonRecursiveNoMeasure
   ]
