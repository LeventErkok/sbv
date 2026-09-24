-----------------------------------------------------------------------------
-- |
-- Module    : TestSuite.Queries.Registration
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Type registration before and during incremental solver interaction.
-----------------------------------------------------------------------------

{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE FlexibleInstances   #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell     #-}
{-# LANGUAGE TypeApplications    #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module TestSuite.Queries.Registration (tests) where

import Control.Monad (when)
import Data.Proxy

import Data.SBV.Control
import Utils.SBVTestFramework

-- | A rational field must be declared before the containing datatype.
newtype RationalBox = RationalBox Rational deriving (Eq, Show)

-- | An empty datatype represents an uninterpreted solver sort.
data RegistrationSort

mkSymbolic [''RationalBox, ''RegistrationSort]

tests :: TestTree
tests = testGroup "Queries.Registration"
  [ testGroup "rationals"
      [ rationalTest "automatic"                 False False
      , rationalTest "registered before query"   True  False
      , rationalTest "registered inside query"   False True
      , rationalTest "registered in both phases" True  True
      ]
  , testCase "rational function first used in query" $ do
      let half :: SInteger -> SRational
          half = smtFunction "registration.half" $ \n -> ite (n .== 1) (1/2) (2/3)
      result <- runSMT $ query $ do
        n <- freshVar @Integer "n"
        constrain $ n .== 1
        getValue (half n)
      result == 1 % 2 @? "Expected a rational result from a query-mode definition"
  , testCase "nested rational types first used in query" $ do
      result <- runSMT $ query $ do
        x <- freshVar @(RationalBox, [Rational]) "x"
        let expected = (RationalBox (1 % 2), [2 % 3])
        constrain $ x .== literal expected
        getValue x
      result == (RationalBox (1 % 2), [2 % 3]) @? "Expected nested rational values"
  , testCase "explicit nested type registration inside query" $ do
      result <- runSMT $ query $ do
        registerType (Proxy @(RationalBox, [Rational]))
        registerType (Proxy @(RationalBox, [Rational]))
        ensureSat
        x <- freshVar @(RationalBox, [Rational]) "x"
        constrain $ x .== literal (RationalBox (1 % 2), [2 % 3])
        getValue x
      result == (RationalBox (1 % 2), [2 % 3]) @? "Explicit registration must reach the solver"
  , testCase "explicit uninterpreted sort registration inside query" $ do
      result <- runSMT $ query $ do
        registerType (Proxy @RegistrationSort)
        registerType (Proxy @RegistrationSort)
        ensureSat
        x <- freshVar @RegistrationSort "x"
        y <- freshVar_ @RegistrationSort
        constrain $ x ./= y
        checkSat
      result == Sat @? "Explicit registration must declare an uninterpreted sort exactly once"
  , testCase "quantified function first used in query" $ do
      result <- runSMT $ query $ do
        let f = uninterpret "registration.quantified" :: SInteger -> SInteger
        constrain $ \(Forall (x :: SInteger)) -> f x .== f x
        checkSat
      result == Sat @? "Quantified uses must register their functions automatically"
  ]

-- | Exercise both rational equality helpers, repeated declarations, named and
-- unnamed fresh variables, and declarations surviving assertion-stack changes.
rationalTest :: String -> Bool -> Bool -> TestTree
rationalTest testName before inside = testCase testName $ do
  result <- runSMT $ do
    when before $ registerType (Proxy @Rational)
    query $ do
      when inside $ do registerType (Proxy @Rational)
                       registerType (Proxy @Rational)
      push 1
      x <- freshVar @Rational "x"
      constrain $ x .== 1/2
      first <- getValue x
      pop 1
      y <- freshVar_ @Rational
      constrain $ y .== 1/3
      constrain $ y ./= 0
      later <- getValue y
      pure (first, later)
  result == (1 % 2, 1 % 3) @? "Expected rational values across incremental contexts, received: " ++ show result
