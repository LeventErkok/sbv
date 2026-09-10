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
{-# LANGUAGE FlexibleInstances   #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell     #-}
{-# LANGUAGE TypeApplications    #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module TestSuite.CodeGeneration.CgTests(tests) where

import Control.Exception (ErrorCall, displayException, evaluate, try)
import Data.List (isInfixOf)
import Data.SBV.Internals
import Data.SBV.Tuple (tuple, untuple)
import qualified Data.SBV.Tools.CodeGen.Legacy as PublicLegacy

import System.Exit     (ExitCode(..))
import System.FilePath ((</>))
import System.IO.Temp  (withSystemTempDirectory)
import System.Process  (readProcessWithExitCode)

import Test.Tasty.HUnit (assertBool, assertEqual)

import Utils.SBVTestFramework

-- | A non-recursive, parameterized sum type used to exercise C tagged-union
-- generation with nullary, unary, and product constructors.
data CodeGenADT a = CGEmpty
                  | CGOne a
                  | CGPair a Word16
                  deriving Show

-- | A finite enumeration used to check that constructor order is preserved by
-- the C tag representation.
data CodeGenEnum = CGRed | CGGreen | CGBlue deriving Show

-- | An acyclic parameterized ADT reference used to exercise 'KApp'
-- resolution and dependency-ordered C declarations.
data CodeGenEnvelope a = CGNoEnvelope | CGEnvelope (CodeGenADT a) deriving Show

-- | A recursive type used to verify the current C ABI boundary.
data CodeGenTree = CGLeaf Word8 | CGNode CodeGenTree CodeGenTree deriving Show

-- | An acyclic wrapper around a recursive value, used to check transitive
-- ownership without changing its embedded by-value layout.
newtype CodeGenForest = CGForest CodeGenTree deriving Show

-- | The even layer of a mutually recursive pair used to exercise C forward
-- declarations and cross-type ownership helpers.
data CodeGenEven = CGEvenEnd Word8 | CGEvenStep CodeGenOdd deriving Show

-- | The odd layer of the mutually recursive code-generation test pair.
newtype CodeGenOdd = CGOddStep CodeGenEven deriving Show

-- | A recursive type with no finite inhabitant, used to check generated-driver
-- diagnostics.
newtype CodeGenLoop = CGLoop CodeGenLoop deriving Show

-- | Generate the symbolic interfaces for the code-generation ADTs.
mkSymbolic [''CodeGenADT, ''CodeGenEnum, ''CodeGenEnvelope, ''CodeGenTree, ''CodeGenForest, ''CodeGenEven, ''CodeGenOdd, ''CodeGenLoop]

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
  , testCase "return and output owned arrays" ownedArrayResults
  , testCase "retain an escaping callback array" escapingCallbackArray
  , testCase "compile and execute structural tuples" structuralTuples
  , testCase "compile repeated tuple types into a library" structuralTupleLibrary
  , testCase "compile and execute non-recursive ADTs" nonRecursiveADTs
  , testCase "compile and execute nested ADTs" nestedADTs
  , testCase "compile repeated ADT types into a library" nonRecursiveADTLibrary
  , testCase "preserve ADT aggregate equality" adtAggregateEquality
  , testCase "compile and execute recursive ADTs" recursiveADTs
  , testCase "embed recursive ADTs by value" wrappedRecursiveADTs
  , testCase "compile and execute mutually recursive ADTs" mutuallyRecursiveADTs
  , testCase "compile repeated recursive ADTs into a library" recursiveADTLibrary
  , testCase "report recursive ADTs without finite samples" uninhabitedRecursiveADT
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

-- | Exercise array-type merging across generated library translation units,
-- including an owned array returned through the public library ABI.
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

      ownedComponent = do
        cgOverwriteFiles True
        let source = lambdaArray (\index -> sFromIntegral index + 5) :: SArray Word16 Word32
        cgReturn (writeArray source 0 55)

  (_, cfg, bundle) <- compileToCLib' "persistentArrayLibrary"
    [ ("increment",   component 1)
    , ("addTwo",      component 2)
    , ("lambdaValue", lambdaComponent)
    , ("ownedArray",  ownedComponent)
    ]
  renderCgPgmBundle (Just dir) (cfg, bundle)
  stdoutText <- compileAndRunGenerated dir "persistentArrayLibrary"
  mapM_ (\fragment -> assertBool ("Expected generated library output to contain " ++ fragment ++ ", received:\n" ++ stdoutText) (fragment `isInfixOf` stdoutText))
    [ "0x00000029UL"
    , "0x0000002aUL"
    , "0x00000005UL"
    , "ownedArray()[0] =0x00000037UL"
    ]

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

-- | Exercise independent owned descriptors for an array output parameter and
-- an array return, including persistent stores above a structured callback.
ownedArrayResults :: Assertion
ownedArrayResults = withSystemTempDirectory "sbv-owned-array-results" $ \dir -> do
  let program = do
        cgOverwriteFiles True
        let source = lambdaArray (\index -> sFromIntegral index + 5) :: SArray Word8 Word32
        cgOutput "owned" (writeArray source 0 99)
        cgReturn (writeArray source 0 42)

  stdoutText <- compileProgramAndRunGenerated dir "ownedArrayResults" program
  mapM_ (\fragment -> assertBool ("Expected owned-array output to contain " ++ fragment ++ ", received:\n" ++ stdoutText) (fragment `isInfixOf` stdoutText))
    [ "ownedArrayResults(&owned)[0] =0x0000002aUL"
    , "owned[0] =0x00000063UL"
    ]

-- | Exercise retention of a borrowed input callback when a persistent array
-- derived from it escapes through an owned return descriptor.
escapingCallbackArray :: Assertion
escapingCallbackArray = withSystemTempDirectory "sbv-escaping-callback-array" $ \dir -> do
  let program = do
        cgOverwriteFiles True
        cgSetDriverValues [7]
        source <- cgInput "source" :: SBVCodeGen (SArray Word8 Word32)
        cgReturn (writeArray source 1 99)

  stdoutText <- compileProgramAndRunGenerated dir "escapingCallbackArray" program
  assertBool ("Expected retained callback output to contain 0x00000007UL, received:\n" ++ stdoutText) ("[0] =0x00000007UL" `isInfixOf` stdoutText)

-- | Exercise nested tuple inputs, construction, projection, conditionals,
-- tuple constants in finite tables, public outputs, and returns.
structuralTuples :: Assertion
structuralTuples = withSystemTempDirectory "sbv-structural-tuples" $ \dir -> do
  let program = do
        cgOverwriteFiles True
        cgSetDriverValues [3, 0]
        source   <- cgInput "source"   :: SBVCodeGen (SBV (Word8, (Word16, Word32)))
        selector <- cgInput "selector" :: SBVCodeGen SWord8
        let (first, nested)   = untuple source
            (second, third)  = untuple nested
            rebuilt          = tuple (first + 1, tuple (second + 2, third + 3))
            alternate        = tuple (9, tuple (10, 11))
            selected         = select [rebuilt, alternate] alternate selector
            conditional      = ite (selector .== 0) rebuilt alternate
        cgOutput "selected" selected
        cgOutput "rounding" (tuple (sRTN, first))
        cgOutput "unit" (literal () :: SBV ())
        cgReturn conditional

  stdoutText <- compileProgramAndRunGenerated dir "structuralTuples" program
  mapM_ (\fragment -> assertBool ("Expected tuple output to contain " ++ fragment ++ ", received:\n" ++ stdoutText) (fragment `isInfixOf` stdoutText))
    [ "(4, (0x0006U, 0x00000008UL))"
    , "selected =(4, (0x0006U, 0x00000008UL))"
    , "rounding =(3, 3)"
    , "unit =()"
    ]

-- | Exercise guarded tuple declarations shared by multiple generated library
-- translation units and returned through the public by-value ABI.
structuralTupleLibrary :: Assertion
structuralTupleLibrary = withSystemTempDirectory "sbv-structural-tuple-library" $ \dir -> do
  let component :: Integer -> SBVCodeGen ()
      component increment = do
        cgOverwriteFiles True
        cgSetDriverValues [4]
        source <- cgInput "source" :: SBVCodeGen (SBV (Word8, Word16))
        let (first, second) = untuple source
        cgReturn (tuple (first + fromInteger increment, second + fromInteger increment))

  (_, cfg, bundle) <- compileToCLib' "structuralTupleLibrary"
    [ ("incrementTuple", component 1)
    , ("addTwoTuple",    component 2)
    ]
  renderCgPgmBundle (Just dir) (cfg, bundle)
  stdoutText <- compileAndRunGenerated dir "structuralTupleLibrary"
  mapM_ (\fragment -> assertBool ("Expected tuple library output to contain " ++ fragment ++ ", received:\n" ++ stdoutText) (fragment `isInfixOf` stdoutText))
    [ "(5, 0x0006U)"
    , "(6, 0x0007U)"
    ]

-- | Exercise parameter substitution, constructors, tests, accessors,
-- structural equality, constants, tables, public outputs, and returns.
nonRecursiveADTs :: Assertion
nonRecursiveADTs = withSystemTempDirectory "sbv-non-recursive-adts" $ \dir -> do
  let program = do
        cgOverwriteFiles True
        cgSetDriverValues [2, 1, 0, 1]
        source   <- cgInput "source"   :: SBVCodeGen (SCodeGenADT Word8)
        choose   <- cgInput "choose"   :: SBVCodeGen SBool
        selector <- cgInput "selector" :: SBVCodeGen SWord8
        color    <- cgInput "color"    :: SBVCodeGen SCodeGenEnum
        let first       = getCGPair_1 source
            second      = getCGPair_2 source
            constructed = ite choose (sCGPair (first + 1) (second + 1)) (sCGOne first)
            constant    = literal (CGPair 9 10)
            selected    = select [source, constructed, constant] sCGEmpty selector
        cgOutput "sourceCopy" source
        cgOutput "constructed" constructed
        cgOutput "constant" constant
        cgOutput "isPair" (isCGPair source)
        cgOutput "sameValue" (source .== literal (CGPair 2 3))
        cgOutput "colorBeforeBlue" (color .< sCGBlue)
        cgReturn selected

  stdoutText <- compileProgramAndRunGenerated dir "nonRecursiveADTs" program
  mapM_ (\fragment -> assertBool ("Expected ADT output to contain " ++ fragment ++ ", received:\n" ++ stdoutText) (fragment `isInfixOf` stdoutText))
    [ "CGPair(2, 0x0003U)"
    , "constructed =CGPair(3, 0x0004U)"
    , "constant =CGPair(9, 0x000aU)"
    , "isPair = 1"
    , "sameValue = 1"
    , "colorBeforeBlue = 1"
    ]

-- | Exercise an acyclic parameterized 'KApp' reference through construction,
-- access, structural equality against a literal, and the public return ABI.
nestedADTs :: Assertion
nestedADTs = withSystemTempDirectory "sbv-nested-adts" $ \dir -> do
  let program = do
        cgOverwriteFiles True
        cgSetDriverValues [1]
        source <- cgInput "source" :: SBVCodeGen (SCodeGenEnvelope Word8)
        let inner  = getCGEnvelope_1 source
            result = sCGEnvelope (sCGOne (getCGOne_1 inner + 3))
        cgOutput "sameValue" (source .== literal (CGEnvelope (CGOne 1)))
        cgReturn result

  stdoutText <- compileProgramAndRunGenerated dir "nestedADTs" program
  headerText <- readFile (dir </> "nestedADTs.h")
  mapM_ (\fragment -> assertBool ("Expected nested ADT output to contain " ++ fragment
                               ++ ", received:\n" ++ stdoutText)
                               (fragment `isInfixOf` stdoutText))
    [ "CGEnvelope(CGOne(4))"
    , "sameValue = 1"
    ]
  assertBool "Expected the concrete Word8 inner ADT declaration"
             ("SBVADT_CodeGenADT_2_u8" `isInfixOf` headerText)
  assertBool "Unexpected placeholder Integer ADT declaration"
             (not ("SBVADT_CodeGenADT_7_integer" `isInfixOf` headerText))

-- | Exercise guarded ADT declarations shared by multiple generated library
-- translation units and returned through the public by-value ABI.
nonRecursiveADTLibrary :: Assertion
nonRecursiveADTLibrary = withSystemTempDirectory "sbv-non-recursive-adt-library" $ \dir -> do
  let component :: Word8 -> SBVCodeGen ()
      component increment = do
        cgOverwriteFiles True
        cgSetDriverValues [1]
        source <- cgInput "source" :: SBVCodeGen (SCodeGenADT Word8)
        cgReturn (ite (isCGOne source) (sCGOne (getCGOne_1 source + literal increment)) sCGEmpty)

  (_, cfg, bundle) <- compileToCLib' "nonRecursiveADTLibrary"
    [ ("incrementADT", component 1)
    , ("addTwoADT",    component 2)
    ]
  renderCgPgmBundle (Just dir) (cfg, bundle)
  stdoutText <- compileAndRunGenerated dir "nonRecursiveADTLibrary"
  mapM_ (\fragment -> assertBool ("Expected ADT library output to contain " ++ fragment ++ ", received:\n" ++ stdoutText) (fragment `isInfixOf` stdoutText))
    [ "CGOne(2)"
    , "CGOne(3)"
    ]

-- | Exercise structural equality for ADTs instantiated with wide bit-vectors,
-- arbitrary floating-point formats, and native floating-point values.
adtAggregateEquality :: Assertion
adtAggregateEquality = withSystemTempDirectory "sbv-adt-aggregate-equality" $ \dir -> do
  let program = do
        cgOverwriteFiles True
        cgSetDriverValues [1, 1, 1, 1, 9, 9]
        wideLeft     <- cgInput "wideLeft"     :: SBVCodeGen (SCodeGenADT (WordN 673))
        wideRight    <- cgInput "wideRight"    :: SBVCodeGen (SCodeGenADT (WordN 673))
        floatLeft    <- cgInput "floatLeft"    :: SBVCodeGen (SCodeGenADT Float)
        floatRight   <- cgInput "floatRight"   :: SBVCodeGen (SCodeGenADT Float)
        integerLeft  <- cgInput "integerLeft"  :: SBVCodeGen SInteger
        integerRight <- cgInput "integerRight" :: SBVCodeGen SInteger
        cgOutput "wideEqual" (wideLeft .== wideRight)
        cgOutput "exactEqual" (sCGOne integerLeft .== sCGOne integerRight)
        cgReturn (floatLeft .=== floatRight)

  stdoutText <- compileProgramAndRunGenerated dir "adtAggregateEquality" program
  mapM_ (\fragment -> assertBool ("Expected aggregate equality output to contain " ++ fragment ++ ", received:\n" ++ stdoutText) (fragment `isInfixOf` stdoutText))
    [ "= 1"
    , "wideEqual = 1"
    , "exactEqual = 1"
    ]

  (_, _, arbitraryFPBundle) <- compileToC' "adtArbitraryFPEquality" $ do
    left  <- cgInput "left"  :: SBVCodeGen (SCodeGenADT (FloatingPoint 7 19))
    right <- cgInput "right" :: SBVCodeGen (SCodeGenADT (FloatingPoint 7 19))
    cgReturn (left .=== right)
  let generated = show arbitraryFPBundle
  assertBool "Expected a concrete arbitrary-float ADT declaration" ("SBVADT_CodeGenADT_9_fp_e7_s19" `isInfixOf` generated)
  assertBool "Expected arbitrary-float object equality in the ADT comparison" ("sbv_fp_e7_s19_obj_eq" `isInfixOf` generated)

-- | Exercise a recursive input layout, including a pointer-backed accessor and
-- a bounded generated-driver value.
recursiveADTs :: Assertion
recursiveADTs = withSystemTempDirectory "sbv-recursive-adts" $ \dir -> do
  let program = do
        cgOverwriteFiles True
        cgSetDriverValues [1]
        value <- cgInput "value" :: SBVCodeGen SCodeGenTree
        let left   = getCGNode_1 value
            result = sCGNode left (sCGLeaf 99)
        cgOutput "isNode" (isCGNode value)
        cgOutput "sameTree" (value .== value)
        cgOutput "sameTreeObject" (value .=== value)
        cgOutput "treeCopy" value
        cgReturn result

  stdoutText <- compileProgramAndRunGenerated dir "recursiveADTs" program
  headerText <- readFile (dir </> "recursiveADTs.h")
  assertBool ("Expected the recursive driver to select a node, received:\n" ++ stdoutText)
             ("isNode = 1" `isInfixOf` stdoutText)
  assertBool ("Expected recursive structural equality, received:\n" ++ stdoutText)
             ("sameTree = 1" `isInfixOf` stdoutText)
  assertBool ("Expected recursive strong equality, received:\n" ++ stdoutText)
             ("sameTreeObject = 1" `isInfixOf` stdoutText)
  assertBool ("Expected a deeply owned recursive result, received:\n" ++ stdoutText)
             ("CGLeaf(99)" `isInfixOf` stdoutText)
  assertBool "Expected a forward-declared recursive ADT"
             ("typedef struct SBVADT_CodeGenTree SBVADT_CodeGenTree;" `isInfixOf` headerText)
  assertBool "Expected recursive fields to use pointers"
             ("SBVADT_CodeGenTree * field1;" `isInfixOf` headerText)
  assertBool "Expected recursive equality to reject null child pointers"
             ("== NULL) abort();" `isInfixOf` headerText)

-- | Exercise transitive ownership when an acyclic ADT embeds a recursive ADT
-- by value.
wrappedRecursiveADTs :: Assertion
wrappedRecursiveADTs = withSystemTempDirectory "sbv-wrapped-recursive-adts" $ \dir -> do
  let program = do
        cgOverwriteFiles True
        cgSetDriverValues [1]
        value <- cgInput "value" :: SBVCodeGen SCodeGenForest
        cgOutput "sameForest" (value .== value)
        cgReturn value

  stdoutText <- compileProgramAndRunGenerated dir "wrappedRecursiveADTs" program
  headerText <- readFile (dir </> "wrappedRecursiveADTs.h")
  assertBool ("Expected the wrapped recursive value to survive an owned return, received:\n" ++ stdoutText)
             ("CGForest(CGNode" `isInfixOf` stdoutText)
  assertBool ("Expected wrapped recursive structural equality, received:\n" ++ stdoutText)
             ("sameForest = 1" `isInfixOf` stdoutText)
  assertBool "Expected an acyclic wrapper field to remain embedded by value"
             ("SBVADT_CodeGenTree field1;" `isInfixOf` headerText)

-- | Exercise mutually recursive layouts, bounded samples, equality, printing,
-- accessors, and deep-owned outputs and returns.
mutuallyRecursiveADTs :: Assertion
mutuallyRecursiveADTs = withSystemTempDirectory "sbv-mutually-recursive-adts" $ \dir -> do
  let program = do
        cgOverwriteFiles True
        cgSetDriverValues [1]
        value <- cgInput "value" :: SBVCodeGen SCodeGenOdd
        cgOutput "sameValue" (value .== value)
        cgOutput "valueCopy" value
        cgReturn (getCGOddStep_1 value)

  stdoutText <- compileProgramAndRunGenerated dir "mutuallyRecursiveADTs" program
  headerText <- readFile (dir </> "mutuallyRecursiveADTs.h")
  assertBool ("Expected mutually recursive structural equality, received:\n" ++ stdoutText)
             ("sameValue = 1" `isInfixOf` stdoutText)
  assertBool ("Expected mutually recursive values to print, received:\n" ++ stdoutText)
             ("CGOddStep(CGEven" `isInfixOf` stdoutText)
  assertBool "Expected the odd-to-even edge to use a pointer"
             ("SBVADT_CodeGenEven * field1;" `isInfixOf` headerText)
  assertBool "Expected the even-to-odd edge to use a pointer"
             ("SBVADT_CodeGenOdd * field1;" `isInfixOf` headerText)

-- | Exercise guarded recursive declarations and ownership helpers shared by
-- multiple generated library components.
recursiveADTLibrary :: Assertion
recursiveADTLibrary = withSystemTempDirectory "sbv-recursive-adt-library" $ \dir -> do
  let component :: Integer -> SBVCodeGen ()
      component seed = do
        cgOverwriteFiles True
        cgSetDriverValues [seed]
        value <- cgInput "value" :: SBVCodeGen SCodeGenTree
        cgReturn value

  (_, cfg, bundle) <- compileToCLib' "recursiveADTLibrary"
    [ ("copyRecursiveLeaf", component 0)
    , ("copyRecursiveTree", component 1)
    ]
  renderCgPgmBundle (Just dir) (cfg, bundle)
  stdoutText <- compileAndRunGenerated dir "recursiveADTLibrary"
  assertBool ("Expected recursive library results, received:\n" ++ stdoutText)
             ("CGLeaf" `isInfixOf` stdoutText && "CGNode" `isInfixOf` stdoutText)

-- | Check that bounded driver generation rejects recursive ADTs without any
-- finite constructor path.
uninhabitedRecursiveADT :: Assertion
uninhabitedRecursiveADT = do
  recursiveResult <- try (do
    (_, _, bundle) <- compileToC' "uninhabitedRecursiveADT" $ do
      value <- cgInput "value" :: SBVCodeGen SCodeGenLoop
      cgReturn (isCGLoop value)
    evaluate (length (show bundle))) :: IO (Either ErrorCall Int)
  case recursiveResult of
    Left exception -> assertBool ("Expected a finite-constructor diagnostic, received:\n" ++ displayException exception)
                                 ("has no finite constructor" `isInfixOf` displayException exception)
    Right _        -> assertBool "Expected driver generation to reject an uninhabited recursive ADT" False

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
