-----------------------------------------------------------------------------
-- |
-- Module    : TestSuite.CodeGeneration.Boundaries
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Executable contracts for deliberately unsupported C-backend features.
-----------------------------------------------------------------------------

{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE EmptyDataDecls        #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TemplateHaskell       #-}
{-# LANGUAGE TypeApplications      #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module TestSuite.CodeGeneration.Boundaries (tests) where

import Control.Exception (ErrorCall, displayException, try)
import Control.Monad (void)
import Data.List (isInfixOf)
import System.Directory (listDirectory)
import System.IO.Temp (withSystemTempDirectory)
import Test.Tasty.HUnit (assertBool, assertEqual)

import Data.SBV.Internals (AlgRealPoly(..))
import Data.SBV.Control (SMTOption(..))
import qualified Data.SBV.List as SL
import Data.SBV.Tools.CodeGen
import Utils.SBVTestFramework

-- | An abstract solver sort deliberately lacking a C representation.
data Opaque

-- | Recursive references hidden inside a by-value tuple cannot have a finite C layout.
data NestedRecursion = EndRecursion | NestedRecursion (Word8, NestedRecursion)

mkSymbolic [''Opaque, ''NestedRecursion]

-- | Every rejected feature is checked through both public entry points;
-- library failures must not leave even an earlier, valid component behind.
tests :: TestTree
tests = testGroup "CodeGeneration.Boundaries"
  [ rejects "uninterpreted sort" "uninterpreted sorts" $ do
      value <- cgInput "value" :: SBVCodeGen (SBV Opaque)
      cgReturn value
  , rejects "nested recursive ADT" "Recursive ADT references nested inside composite fields" $ do
      value <- cgInput "value" :: SBVCodeGen (SBV NestedRecursion)
      cgReturn value
  , rejects "solver option" "SMT solver options have no executable C semantics" $ do
      setOption (ProduceAssertions True)
      cgReturn sTrue
  , rejects "solver option through cgSym" "SMT solver options have no executable C semantics" $ do
      cgSym $ setOption (ProduceAssertions True)
      cgReturn sTrue
  , rejects "nested uninterpreted sort" "uninterpreted sorts" $ do
      value <- cgInput "value" :: SBVCodeGen (SList (Maybe Opaque))
      cgReturn value
  , rejects "finite quantifier" "quantified" $ do
      value <- cgInput "value" :: SBVCodeGen SBool
      cgReturn (quantifiedBool (\(Forall b) -> b .|| value))
  , rejects "infinite quantifier" "quantified" $ do
      value <- cgInput "value" :: SBVCodeGen SInteger
      cgReturn (quantifiedBool (\(Forall n) -> n .>= value))
  , rejects "quantifier in private function" "quantified" $ do
      value <- cgInput "value" :: SBVCodeGen SInteger
      cgReturn (smtFunction "quantifiedFunction" (\v -> quantifiedBool (\(Forall n) -> n .>= v)) value)
  , rejects "quantifier in array lambda" "quantified" $
      cgReturn (lambdaArray (\v -> quantifiedBool (\(Forall n) -> n .>= v)) :: SArray Integer Bool)
  , rejects "special relation" "special relations" $
      cgReturn (isPartialOrder "order" (uncurry ((.<=) :: SInteger -> SInteger -> SBool)))
  , rejects "soft constraint" "Soft constraints" $ do
      value <- cgInput "value" :: SBVCodeGen SBool
      softConstrain value
      cgReturn value
  , rejects "SMT-only constraint attribute" "Constraint attributes: :weight" $ do
      value <- cgInput "value" :: SBVCodeGen SBool
      constrainWithAttribute [(":weight", "2")] value
      cgReturn value
  , rejects "minimize" "Optimization objectives require a solver" $ do
      value <- cgInput "value" :: SBVCodeGen SInteger
      cgSym $ minimize "minimum" value
      cgReturn value
  , rejects "maximize" "Optimization objectives require a solver" $ do
      value <- cgInput "value" :: SBVCodeGen SWord8
      cgSym $ maximize "maximum" value
      cgReturn value
  , rejects "implicit higher-order capture" "Defined functions with implicit captures" $ do
      offset <- cgInput "offset" :: SBVCodeGen SInteger
      values <- cgInput "values" :: SBVCodeGen (SList Integer)
      cgReturn (SL.map (+ offset) values)
  , rejects "implicit managed higher-order capture" "Defined functions with implicit captures" $ do
      offset <- cgInput "offset" :: SBVCodeGen SString
      values <- cgInput "values" :: SBVCodeGen (SList String)
      cgReturn (SL.map (.== offset) values)
  , rejects "penalized assertion" "Optimization objectives require a solver" $ do
      value <- cgInput "value" :: SBVCodeGen SBool
      cgSym $ assertWithPenalty "penalty" value DefaultPenalty
      cgReturn value
  , rejects "algebraic real literal" "Algebraic SReal literals" $ cgReturn (literal algebraic)
  , rejects "nested algebraic real literal" "Algebraic SReal literals" $ cgReturn (literal [algebraic])
  , rejects "mapped algebraic real literal" "Algebraic SReal literals" $ cgSRealType CgDouble >> cgReturn (literal algebraic)
  , rejects "inexact real literal" "Inexact SReal literals" $ cgReturn (literal (AlgRational False (1 / 3)))
  , rejects "exact transcendental" "exact GMP-rational SReal representation cannot represent" $ do
      value <- cgInput "value" :: SBVCodeGen SReal
      cgReturn (sin value)
  , rejects "private exact transcendental" "exact GMP-rational SReal representation cannot represent" $ do
      value <- cgInput "value" :: SBVCodeGen SReal
      cgReturn (smtFunction "exactSine" sin value)
  , rejects "sparse infinite-domain equality" "cannot enumerate key domain" $ do
      value <- cgInput "value" :: SBVCodeGen SWord8
      let base = constArray 0 :: SArray Integer Word8
      cgReturn (writeArray base 1 value .== writeArray base 2 value)
  ]

-- | The positive square root of two, represented without an approximation.
algebraic :: AlgReal
algebraic = AlgPolyRoot (2, AlgRealPoly [(1, 2), (-2, 0)]) Nothing

-- | Check an intentional diagnostic, not just any exception, and ensure that
-- validation completes before standalone or library output is written.
rejects :: String -> String -> SBVCodeGen () -> TestTree
rejects testName diagnostic program = testGroup testName
  [ testCase mode $ withSystemTempDirectory "sbv-c-boundary" $ \dir -> do
      let prepare body = cgGenerateDriver False >> cgOverwriteFiles True >> body
          action | library = void $ compileToCLib (Just dir) "rejectedLibrary"
                               [("validComponent", prepare (cgReturn sTrue)), ("rejectedComponent", prepare program)]
                 | True    = compileToC (Just dir) "rejectedComponent" (prepare program)
      result <- try action :: IO (Either ErrorCall ())
      case result of
        Left exception -> do
          let message = displayException exception
          assertBool message (diagnostic `isInfixOf` message)
          assertBool message (not (any (`isInfixOf` message) ["Unexpected:", "Missing assignment", "Impossible happened"]))
        Right () -> assertFailure "Expected an explicit unsupported-feature diagnostic"
      assertEqual "Rejected generation must not write any files" [] =<< listDirectory dir
  | (mode, library) <- [("standalone", False), ("library", True)]
  ]
