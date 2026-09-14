-----------------------------------------------------------------------------
-- |
-- Module    : TestSuite.CodeGeneration.ArrayCaptures
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Reject unsupported array-lambda captures before emitting C artifacts.
-----------------------------------------------------------------------------

{-# OPTIONS_GHC -Wall -Werror #-}

module TestSuite.CodeGeneration.ArrayCaptures (tests) where

import Control.Exception (ErrorCall, displayException, try)
import Control.Monad (void)
import Data.List (isInfixOf)
import System.Directory (listDirectory)
import System.IO.Temp (withSystemTempDirectory)
import Test.Tasty.HUnit (assertBool, assertEqual)

import Data.SBV.Tools.CodeGen
import Utils.SBVTestFramework

-- | Captures in ordinary and operator-embedded operands must fail clearly,
-- including in nested callbacks and library components. Existing frontend
-- restrictions remain in place; closed callbacks remain supported.
tests :: TestTree
tests = testGroup "CodeGeneration.ArrayCaptures"
  [ rejects "direct result capture" captureDiagnostic $ do
      value <- cgInput "value" :: SBVCodeGen SWord32
      cgReturn (lambdaArray (const value) :: SArray Word8 Word32)
  , rejects "arithmetic capture" captureDiagnostic $ do
      value <- cgInput "value" :: SBVCodeGen SWord32
      cgReturn (lambdaArray (+ value) :: SArray Word32 Word32)
  , rejects "managed value capture" captureDiagnostic $ do
      value <- cgInput "value" :: SBVCodeGen SString
      cgReturn (lambdaArray (const value) :: SArray Word8 String)
  , rejects "array descriptor capture" captureDiagnostic $ do
      value <- cgInput "value" :: SBVCodeGen (SArray Word32 Word32)
      cgReturn (lambdaArray (readArray value) :: SArray Word32 Word32)
  , rejects "table entry capture" captureDiagnostic $ do
      value <- cgInput "value" :: SBVCodeGen SWord32
      cgReturn (lambdaArray (select [value, 17] 0) :: SArray Word8 Word32)
  , rejects "table default capture" captureDiagnostic $ do
      cgPerformRTCs True
      value <- cgInput "value" :: SBVCodeGen SWord32
      cgReturn (lambdaArray (select [3, 17] value) :: SArray Word8 Word32)
  , rejects "unchecked table default capture" captureDiagnostic $ do
      cgPerformRTCs False
      value <- cgInput "value" :: SBVCodeGen SWord32
      cgReturn (lambdaArray (select [3, 17] value) :: SArray Word8 Word32)
  , rejects "rounding-mode operand capture" captureDiagnostic $ do
      rounding <- cgInput "rounding" :: SBVCodeGen SRoundingMode
      cgReturn (lambdaArray (toSFloat rounding) :: SArray Word32 Float)
  , rejects "capture hidden in nested array" captureDiagnostic $ do
      value <- cgInput "value" :: SBVCodeGen SWord32
      cgReturn (lambdaArray (\_ -> lambdaArray (+ value)) :: SArray Word8 (ArrayModel Word32 Word32))
  , rejects "nested parameter hidden in a rounding-mode operand" captureDiagnostic $
      cgReturn (lambdaArray (lambdaArray . toSFloat) :: SArray RoundingMode (ArrayModel Word32 Float))
  , rejects "defined-function parameter hidden in a rounding-mode operand" captureDiagnostic $ do
      rounding <- cgInput "rounding" :: SBVCodeGen SRoundingMode
      cgReturn (smtFunction "rounding array" (\mode -> lambdaArray (toSFloat mode) :: SArray Word32 Float) rounding)
  , rejects "nested parameter capture remains frontend-rejected" "Detected free variables passed to a lambda" $
      cgReturn (lambdaArray (\outer -> lambdaArray (+ outer)) :: SArray Word32 (ArrayModel Word32 Word32))
  , rejects "defined-function parameter capture remains frontend-rejected" "Detected free variables passed to a lambda" $ do
      value <- cgInput "value" :: SBVCodeGen SWord32
      cgReturn (smtFunction "capturing array" (\offset -> lambdaArray (+ offset) :: SArray Word32 Word32) value)
  , testCase "library rejects captures without writing earlier components" libraryCapture
  , testCase "closed nested callbacks with literal constants still compile" closedArrays
  ]

-- | Stable user-facing diagnostic shared by all C-side capture failures.
captureDiagnostic :: String
captureDiagnostic = "Array lambdas that capture outer symbolic values are not supported"

-- | A failed standalone generation must create no files and must not expose
-- the scheduler's internal missing-assignment error as its capture diagnostic.
rejects :: String -> String -> SBVCodeGen () -> TestTree
rejects testName diagnostic program = testCase testName $
  withSystemTempDirectory "sbv-c-array-capture-rejection" $ \dir -> do
    result <- try (compileToC (Just dir) "capturingArray" (cgGenerateDriver False >> program)) :: IO (Either ErrorCall ())
    checkRejection diagnostic result
    assertEqual "Rejected generation must not create files" [] =<< listDirectory dir

-- | Keep whole-library preflight atomic even when a valid component precedes
-- the component with an unsupported capture.
libraryCapture :: Assertion
libraryCapture = withSystemTempDirectory "sbv-c-array-capture-library" $ \dir -> do
  let closed = cgGenerateDriver False >> cgReturn (lambdaArray (+ 3) :: SArray Word32 Word32)
      capturing = do
        cgGenerateDriver False
        value <- cgInput "value" :: SBVCodeGen SWord32
        cgReturn (lambdaArray (+ value) :: SArray Word32 Word32)
  result <- try (void $ compileToCLib (Just dir) "captureLibrary" [("closedArray", closed), ("capturingArray", capturing)])
  checkRejection captureDiagnostic result
  assertEqual "Rejected library must not create any component files" [] =<< listDirectory dir

-- | Check the explicit unsupported boundary instead of accepting any failure.
checkRejection :: String -> Either ErrorCall () -> Assertion
checkRejection diagnostic result = case result of
  Left err -> do
    let message = displayException err
    assertBool message (diagnostic `isInfixOf` message)
    assertBool "Capture diagnostics must not expose an internal scheduling failure"
               (not ("Missing assignment" `isInfixOf` message))
  Right () -> assertFailure "Expected generation to reject an array-lambda capture"

-- | Haskell lexical bindings that contain only literal constants do not
-- require a runtime environment, nor does nesting otherwise closed lambdas.
closedArrays :: Assertion
closedArrays = withSystemTempDirectory "sbv-c-closed-array-lambdas" $ \dir -> do
  compileToC (Just dir) "closedArrays" $ do
    cgGenerateDriver False
    let offset = literal (3 :: Word32)
    cgReturn (lambdaArray (\_ -> lambdaArray (+ offset)) :: SArray Word8 (ArrayModel Word32 Word32))
  assertBool "Closed callbacks still produce C artifacts" . not . null =<< listDirectory dir
