-----------------------------------------------------------------------------
-- |
-- Module    : TestSuite.CodeGeneration.CgTests
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Test suite for code-generation features
-----------------------------------------------------------------------------

{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE ScopedTypeVariables #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module TestSuite.CodeGeneration.CgTests(tests) where

import Data.List (isInfixOf)
import Data.SBV.Internals
import qualified Data.SBV.Tools.CodeGen.Legacy as PublicLegacy

import System.Exit     (ExitCode(..))
import System.FilePath ((</>))
import System.IO.Temp  (withSystemTempDirectory)
import System.Process  (readProcessWithExitCode)

import Test.Tasty.HUnit (assertBool, assertEqual)

import Utils.SBVTestFramework

-- | Code-generation tests.
tests :: TestTree
tests = testGroup "CodeGeneration.CgTests"
  [ goldenVsStringShow "selChecked"   $ genSelect True  "selChecked"
  , goldenVsStringShow "selUnchecked" $ genSelect False "selUnChecked"
  , goldenVsStringShow "codeGen1"       foo
  , testCase "compile through the public legacy facade" legacyPublicFacade
  , testCase "collect C runtime requirements" dependencyRequirements
  , testCase "compile and execute persistent arrays" persistentArrays
  , testCase "preserve native floating-point array-key equality" nativeFloatArrayKeys
  , testCase "compile repeated array types into a library" persistentArrayLibrary
  , testCase "compile and execute a callback-backed array input" callbackArrayInput
  , testCase "compile and execute a structured lambda array" structuredLambdaArray
  , testCase "compile and execute structured lambda tables" structuredLambdaTables
  , testCase "compile and execute a free array with a C definition" definedFreeArray
  ]
 where thd (_, _, r) = r

       genSelect b n = thd <$> compileToC' n (do
                         cgSetDriverValues [65]
                         cgPerformRTCs b
                         let sel :: SWord8 -> SWord8
                             sel x = select [1, x+2] 3 x
                         x <- cgInput "x"
                         cgReturn $ sel x)
       foo = thd <$> compileToC' "foo" fooProgram

       fooProgram = do
                        cgSetDriverValues $ repeat 0
                        (x::SInt16)    <- cgInput "x"
                        (ys::[SInt64]) <- cgInputArr 45 "xArr"
                        cgOutput "z" (5 :: SWord16)
                        cgOutputArr "zArr" (replicate 7 (x+1))
                        cgOutputArr "yArr" ys
                        cgReturn (x*2)

-- | Compile and execute a scalar program using only the public compatibility
-- module's code-generation interface.
legacyPublicFacade :: Assertion
legacyPublicFacade = withSystemTempDirectory "sbv-legacy-c-backend" $ \dir -> do
  let programDir = dir </> "program"
      libraryDir = dir </> "library"

  PublicLegacy.compileToC (Just programDir) "legacyFacade" $ do
    PublicLegacy.cgOverwriteFiles True
    PublicLegacy.cgSetDriverValues [41]
    value <- PublicLegacy.cgInput "value" :: PublicLegacy.SBVCodeGen SWord32
    PublicLegacy.cgReturn (value + 1)

  programOutput <- compileAndRunGenerated programDir "legacyFacade"
  let expectedProgram = "0x0000002aUL"
  assertBool ("Expected legacy generated output to contain " ++ expectedProgram ++ ", received:\n" ++ programOutput) (expectedProgram `isInfixOf` programOutput)

  let component operation = do
        PublicLegacy.cgOverwriteFiles True
        PublicLegacy.cgSetDriverValues [41]
        value <- PublicLegacy.cgInput "value" :: PublicLegacy.SBVCodeGen SWord32
        PublicLegacy.cgReturn (operation value)
  _ <- PublicLegacy.compileToCLib (Just libraryDir) "legacyLibrary"
         [ ("increment", component (+ 1))
         , ("twice", component (* 2))
         ]
  libraryOutput <- compileAndRunGenerated libraryDir "legacyLibrary"
  let expectedLibrary = ["0x0000002aUL", "0x00000052UL"]
  mapM_ (\expected -> assertBool ("Expected legacy library output to contain " ++ expected ++ ", received:\n" ++ libraryOutput) (expected `isInfixOf` libraryOutput)) expectedLibrary

-- | Build and execute a generated C program or library driver.
compileAndRunGenerated :: FilePath -> String -> IO String
compileAndRunGenerated dir executableName = do
  (makeExit, _, makeError) <- readProcessWithExitCode "make" ["-C", dir] ""
  assertEqual makeError ExitSuccess makeExit
  (runExit, outputText, runError) <- readProcessWithExitCode (dir </> executableName ++ "_driver") [] ""
  assertEqual runError ExitSuccess runExit
  pure outputText

-- | Check that ABI kinds and scalar operations contribute the exact external
-- runtime dependencies needed by their generated C bundles.
dependencyRequirements :: Assertion
dependencyRequirements = do
  (_, _, wideBundle) <- compileToC' "requirementsWide" $ do
    value <- cgInput "value" :: SBVCodeGen (SWord 673)
    cgReturn value

  (_, _, fpBundle) <- compileToC' "requirementsFP" $ do
    value <- cgInput "value" :: SBVCodeGen (SFloatingPoint 7 19)
    cgReturn value

  (_, _, integerBundle) <- compileToC' "requirementsInteger" $ do
    value <- cgInput "value" :: SBVCodeGen SInteger
    cgReturn value

  (_, _, nativeFloatBundle) <- compileToC' "requirementsNativeFloat" $ do
    value <- cgInput "value" :: SBVCodeGen SFloat
    cgReturn (fpSqrt sRoundNearestTiesToEven value)

  (_, _, roundedNativeFloatBundle) <- compileToC' "requirementsRoundedNativeFloat" $ do
    value <- cgInput "value" :: SBVCodeGen SFloat
    cgReturn (fpSqrt sRoundNearestTiesToAway value)

  assertEqual "wide bit-vectors should not add an external library" [[]]              (linkerFlags wideBundle)
  assertEqual "arbitrary floats should request LibBF and libm"       [["-lbf", "-lm"]] (linkerFlags fpBundle)
  assertEqual "exact integers should request GMP"                    [["-lgmp"]]        (linkerFlags integerBundle)
  assertEqual "native floating-point sqrt should request libm"       [["-lm"]]          (linkerFlags nativeFloatBundle)
  assertEqual "explicit native rounding should request LibBF and libm" [["-lbf", "-lm"]] (linkerFlags roundedNativeFloatBundle)

-- | Exercise symbolic constant initialization, immutable writes, reads, and
-- an array-valued conditional without exposing arrays at the public C ABI.
persistentArrays :: Assertion
persistentArrays = withSystemTempDirectory "sbv-persistent-arrays" $ \dir -> do
  let program = do
        cgOverwriteFiles True
        cgSetDriverValues [11, 22, 7, 99, 1]
        firstKey     <- cgInput "firstKey"     :: SBVCodeGen SWord8
        secondKey    <- cgInput "secondKey"    :: SBVCodeGen SWord8
        defaultValue <- cgInput "defaultValue" :: SBVCodeGen SWord32
        storedValue  <- cgInput "storedValue"  :: SBVCodeGen SWord32
        chooseNewest <- cgInput "chooseNewest" :: SBVCodeGen SBool
        let base       = constArray defaultValue
            firstWrite = writeArray base firstKey storedValue
            newest     = writeArray firstWrite secondKey (storedValue + 1)
            selected   = ite chooseNewest newest firstWrite
            literalMap = listArray [(11, 42), (11, 43)] 44 :: SArray Word8 Word32
        cgOutput "baseStillDefault" (readArray base firstKey)
        cgOutput "oldVersionDefault" (readArray firstWrite secondKey)
        cgOutput "literalMapValue" (readArray literalMap firstKey)
        cgReturn (readArray selected secondKey)

  stdoutText <- compileProgramAndRunGenerated dir "persistentArrays" program
  mapM_ (\fragment -> assertBool ("Expected generated output to contain " ++ fragment ++ ", received:\n" ++ stdoutText) (fragment `isInfixOf` stdoutText))
    [ "0x00000064UL"
    , "baseStillDefault = 0x00000007UL"
    , "oldVersionDefault = 0x00000007UL"
    , "literalMapValue = 0x0000002aUL"
    ]

-- | Check that native floating-point array keys use SMT object equality:
-- NaNs match, while positive and negative zero remain distinct.
nativeFloatArrayKeys :: Assertion
nativeFloatArrayKeys = withSystemTempDirectory "sbv-native-float-array-keys" $ \dir -> do
  let program = do
        cgOverwriteFiles True
        cgSetDriverValues [0x7fc00000, 0x00000000, 0x80000000]
        nanBits      <- cgInput "nanBits"      :: SBVCodeGen SWord32
        positiveBits <- cgInput "positiveBits" :: SBVCodeGen SWord32
        negativeBits <- cgInput "negativeBits" :: SBVCodeGen SWord32
        let nanKey       = sWord32AsSFloat nanBits
            positiveZero = sWord32AsSFloat positiveBits
            negativeZero = sWord32AsSFloat negativeBits
            base         = constArray 3
            withNaN      = writeArray base nanKey 11
            withZero     = writeArray withNaN positiveZero 12
            flags        = [ readArray withZero nanKey .== (11 :: SWord8)
                           , readArray withZero positiveZero .== (12 :: SWord8)
                           , readArray withZero negativeZero .== (3 :: SWord8)
                           ]
        cgReturn (sum (zipWith (\flag weight -> ite flag weight 0) flags [1, 2, 4]) :: SWord8)

  stdoutText <- compileProgramAndRunGenerated dir "nativeFloatArrayKeys" program
  assertBool ("Expected all native array-key checks to pass, received:\n" ++ stdoutText) ("= 7" `isInfixOf` stdoutText)

-- | Exercise opaque array-type merging across generated library translation
-- units while keeping every public entry point scalar-valued.
persistentArrayLibrary :: Assertion
persistentArrayLibrary = withSystemTempDirectory "sbv-persistent-array-library" $ \dir -> do
  let component increment = do
        cgOverwriteFiles True
        cgSetDriverValues [40, 9]
        source <- cgInput "source" :: SBVCodeGen (SArray Word16 Word32)
        key    <- cgInput "key"    :: SBVCodeGen SWord16
        let updated = writeArray source key (readArray source key + increment)
        cgReturn (readArray updated key)

      lambdaComponent = do
        cgOverwriteFiles True
        cgSetDriverValues [1]
        key <- cgInput "key" :: SBVCodeGen SWord16
        let source = lambdaArray (\index -> select [sFromIntegral index * 3 + 1, sFromIntegral index * 3 + 2] 0 index :: SWord32)
                     :: SArray Word16 Word32
        cgReturn (readArray source key)

  (_, cfg, bundle) <- compileToCLib' "persistentArrayLibrary"
    [ ("increment",   component 1)
    , ("addTwo",      component 2)
    , ("lambdaValue", lambdaComponent)
    ]
  renderCgPgmBundle (Just dir) (cfg, bundle)
  stdoutText <- compileAndRunGenerated dir "persistentArrayLibrary"
  mapM_ (\fragment -> assertBool ("Expected generated library output to contain " ++ fragment ++ ", received:\n" ++ stdoutText) (fragment `isInfixOf` stdoutText))
    ["0x00000029UL", "0x0000002aUL", "0x00000005UL"]

-- | Exercise the borrowed callback descriptor used for a public array input,
-- including local writes that shadow the callback only at matching keys.
callbackArrayInput :: Assertion
callbackArrayInput = withSystemTempDirectory "sbv-callback-array-input" $ \dir -> do
  let program = do
        cgOverwriteFiles True
        cgSetDriverValues [40, 9]
        source <- cgInput "source" :: SBVCodeGen (SArray Word8 Word32)
        key    <- cgInput "key"    :: SBVCodeGen SWord8
        let updated = writeArray source key 99
        cgOutput "sourceValue" (readArray source key)
        cgOutput "unshadowedValue" (readArray updated (key + 1))
        cgReturn (readArray updated key)

  stdoutText <- compileProgramAndRunGenerated dir "callbackArrayInput" program
  mapM_ (\fragment -> assertBool ("Expected callback-backed output to contain " ++ fragment ++ ", received:\n" ++ stdoutText) (fragment `isInfixOf` stdoutText))
    [ "0x00000063UL"
    , "sourceValue = 0x00000028UL"
    , "unshadowedValue = 0x00000028UL"
    ]

-- | Exercise a retained lambda DAG together with a persistent write that
-- shadows exactly one value produced by the lambda.
structuredLambdaArray :: Assertion
structuredLambdaArray = withSystemTempDirectory "sbv-structured-lambda-array" $ \dir -> do
  let program = do
        cgOverwriteFiles True
        cgSetDriverValues [9]
        key <- cgInput "key" :: SBVCodeGen SWord16
        let source  = lambdaArray (\index -> sFromIntegral index * 3 + 1) :: SArray Word16 Word32
            updated = writeArray source key 99
        cgOutput "nextValue" (readArray updated (key + 1))
        cgReturn (readArray updated key)

  stdoutText <- compileProgramAndRunGenerated dir "structuredLambdaArray" program
  mapM_ (\fragment -> assertBool ("Expected structured-lambda output to contain " ++ fragment ++ ", received:\n" ++ stdoutText) (fragment `isInfixOf` stdoutText))
    [ "0x00000063UL"
    , "nextValue = 0x0000001fUL"
    ]

-- | Exercise parameter-dependent tables in two structured lambdas, ensuring
-- their independently numbered local table declarations do not collide.
structuredLambdaTables :: Assertion
structuredLambdaTables = withSystemTempDirectory "sbv-structured-lambda-tables" $ \dir -> do
  let program = do
        cgOverwriteFiles True
        cgSetDriverValues [1]
        key <- cgInput "key" :: SBVCodeGen SWord8
        let first  = lambdaArray (\index -> select [sFromIntegral index + 10, sFromIntegral index + 20] 99 index :: SWord32)
                     :: SArray Word8 Word32
            second = lambdaArray (\index -> select [sFromIntegral index * 2, sFromIntegral index * 3] 77 index :: SWord32)
                     :: SArray Word8 Word32
        cgOutput "firstValue" (readArray first key)
        cgReturn (readArray second key)

  stdoutText <- compileProgramAndRunGenerated dir "structuredLambdaTables" program
  mapM_ (\fragment -> assertBool ("Expected structured-lambda table output to contain " ++ fragment ++ ", received:\n" ++ stdoutText) (fragment `isInfixOf` stdoutText))
    [ "0x00000003UL"
    , "firstValue = 0x00000015UL"
    ]

-- | Exercise 'freeArray' by supplying the corresponding total C function as
-- a user declaration, preserving the existing uninterpreted-function escape hatch.
definedFreeArray :: Assertion
definedFreeArray = withSystemTempDirectory "sbv-defined-free-array" $ \dir -> do
  let program = do
        cgOverwriteFiles True
        cgSetDriverValues [9]
        cgAddDecl ["static SWord32 free_source(SWord16 key) { return (SWord32) key + UINT32_C(5); }"]
        key <- cgInput "key" :: SBVCodeGen SWord16
        let source = freeArray "free_source" :: SArray Word16 Word32
        cgReturn (readArray source key)

  stdoutText <- compileProgramAndRunGenerated dir "definedFreeArray" program
  assertBool ("Expected defined free-array output to contain 0x0000000eUL, received:\n" ++ stdoutText) ("0x0000000eUL" `isInfixOf` stdoutText)

-- | Generate, compile, and execute one standalone C program.
compileProgramAndRunGenerated :: FilePath -> String -> SBVCodeGen () -> IO String
compileProgramAndRunGenerated dir executableName program = do
  (_, cfg, bundle) <- compileToC' executableName program
  renderCgPgmBundle (Just dir) (cfg, bundle)
  compileAndRunGenerated dir executableName

-- | Extract linker-option lists from the Makefile entries in a generated C
-- bundle.
linkerFlags :: CgPgmBundle -> [[String]]
linkerFlags (CgPgmBundle _ files) = [flags | (_, (CgMakefile flags, _)) <- files]
