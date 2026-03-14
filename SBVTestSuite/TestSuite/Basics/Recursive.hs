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

import qualified Data.SBV.List as L
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

-- | Test that auto-guess succeeds for an integer-recursive function (abs measure)
autoGuessInteger :: Assertion
autoGuessInteger = assertIsSat $ \(x :: SInteger) -> f x .== x
  where f :: SInteger -> SInteger
        f = smtFunction "autoGuessIntF" $ \x -> ite (x .<= 0) 0 (1 + f (x - 1))

-- | Test that auto-guess succeeds for a list-recursive function (length measure)
autoGuessList :: Assertion
autoGuessList = assertIsSat $ \(xs :: SList Integer) -> myLen xs .>= 0
  where myLen :: SList Integer -> SInteger
        myLen = smtFunction "autoGuessListLen" $ \xs ->
                  ite (L.null xs) 0 (1 + myLen (L.tail xs))

-- | Test that auto-guess fails when candidates exist but don't work (Ackermann)
autoGuessFailCandidates :: Assertion
autoGuessFailCandidates = do
  r <- C.try $ sat $ \(x :: SInteger) (y :: SInteger) -> ack x y .== 0
  case r of
    Left (e :: C.SomeException) -> if "Cannot determine a termination measure" `isInfixOf` show e
                                      then pure ()
                                      else assertFailure $ "Unexpected exception: " ++ show e
    Right _                     -> assertFailure "Expected error for Ackermann auto-guess"
  where ack :: SInteger -> SInteger -> SInteger
        ack = smtFunction "ackermann" $ \m n ->
                ite (m .== 0) (n + 1)
                    (ite (n .== 0) (ack (m - 1) 1)
                                   (ack (m - 1) (ack m (n - 1))))

-- | Test that auto-guess fails when no candidates can be derived (non-integer, non-list args)
autoGuessNoCandidates :: Assertion
autoGuessNoCandidates = do
  r <- C.try $ sat $ \(b :: SBool) -> h b .== 0
  case r of
    Left (e :: C.SomeException) -> if "No measure candidates" `isInfixOf` show e
                                      then pure ()
                                      else assertFailure $ "Unexpected exception: " ++ show e
    Right _                     -> assertFailure "Expected error for no-candidate auto-guess"
  where h :: SBool -> SInteger
        h = smtFunction "noCandidate" $ \b -> ite b (1 + h (sNot b)) 0

-- | Test that a non-recursive smtFunction without a measure is accepted
nonRecursiveNoMeasure :: Assertion
nonRecursiveNoMeasure = assertIsSat $ \(x :: SInteger) -> g x .== 4
  where g :: SInteger -> SInteger
        g = smtFunction "nonRecG" $ \x -> 2 * x

-- Test suite
tests :: TestTree
tests = testGroup "Basics.Recursive"
   [ testCase "recursive1"                $ assertIsThm $ \x -> mgcd    0 x .== x
   , testCase "recursive2"                $ assertIsThm $ \x -> mgcd    x 0 .== x
   , testCase "recursiveDyn1"             $ checkThm =<< mgcdDyn 0
   , testCase "recursiveDyn2"             $ checkThm =<< mgcdDyn 1
   , testCase "autoGuessInteger"          autoGuessInteger
   , testCase "autoGuessList"             autoGuessList
   , testCase "autoGuessFailCandidates"   autoGuessFailCandidates
   , testCase "autoGuessNoCandidates"     autoGuessNoCandidates
   , testCase "nonRecursiveNoMeasure"     nonRecursiveNoMeasure
   ]
