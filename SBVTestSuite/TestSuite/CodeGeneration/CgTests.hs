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
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell     #-}
{-# LANGUAGE TypeApplications    #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module TestSuite.CodeGeneration.CgTests(tests) where

import Control.Exception (ErrorCall, displayException, evaluate, try)
import Control.Monad (forM, unless, void, when)
import qualified Data.Bifunctor as B
import Data.List (isInfixOf)
import Data.Proxy (Proxy(..))
import Data.SBV.Internals
import Data.SBV.Tools.CodeGen (compileToC, compileToCLib)
import qualified Data.SBV.Char as SC
import qualified Data.SBV.List as SL
import qualified Data.SBV.Set as SS
import Data.SBV.Tuple (tuple, untuple)
import qualified Data.SBV.Tools.CodeGen.Legacy as PublicLegacy

import System.Directory (listDirectory)
import System.Exit      (ExitCode(..))
import System.FilePath  ((</>))
import System.IO.Temp   (withSystemTempDirectory)
import System.Process   (readProcessWithExitCode)

import Test.Tasty.HUnit (assertBool, assertEqual)

import Utils.SBVTestFramework
import Utils.CCodeGen (generatedMakeOptions)

-- | A non-recursive, parameterized sum type used to exercise C tagged-union
-- generation with nullary, unary, and product constructors.
data CodeGenADT a = CGEmpty
                  | CGOne a
                  | CGPair a Word16
                  deriving Show

-- | A finite enumeration used to check that constructor order is preserved by
-- the C tag representation.
data CodeGenEnum = CGRed | CGGreen | CGBlue deriving (Eq, Ord, Show)

-- | An acyclic parameterized ADT reference used to exercise 'KApp'
-- resolution and dependency-ordered C declarations.
data CodeGenEnvelope a = CGNoEnvelope | CGEnvelope (CodeGenADT a) deriving Show

-- | A recursive type used to verify the current C ABI boundary.
data CodeGenTree = CGLeaf Word8 | CGNode CodeGenTree CodeGenTree deriving (Eq, Ord, Show)

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

-- | A managed aggregate used to exercise direct and tuple-nested collection
-- fields in generated C ADTs.
data CodeGenCollections = CGNoCollections
                        | CGCollections [Integer] (RCSet Rational) ([Integer], RCSet Rational)
                        deriving Show

-- | A managed aggregate used to exercise native-width collection ownership
-- without relying on exact-element storage to select the owned ABI.
data CodeGenNativeCollections = CGNativeCollections [Word16] (RCSet Word16) deriving Show

-- | A managed aggregate used to exercise direct text fields and collections
-- whose elements are strings.
data CodeGenText = CGText String [String] (RCSet String) deriving Show

-- | An aggregate used to exercise retained array fields in generated C ADTs.
data CodeGenArrayBox = CGArrayBox (ArrayModel Word8 Word32) Word8 deriving Show

-- | An ADT that hides an array-owning ADT behind an intermediate tuple.
newtype CodeGenArrayEnvelope = CGArrayEnvelope (CodeGenArrayBox, Word16) deriving Show

-- | A recursive managed aggregate whose leaf owns exact-element collections.
data CodeGenCollectionTree = CGCollectionLeaf [Integer] (RCSet Rational)
                           | CGCollectionBranch CodeGenCollectionTree
                           deriving Show

-- | A recursive type whose spelling differs from 'CodeGenCASE' only in case.
data CodeGenCase = CGCaseLeaf Word8 | CGCaseNext CodeGenCase deriving (Eq, Ord, Show)

-- | The case-sensitive companion used to expose collisions in generated
-- declaration guards, constructor tags, and transitive collection helpers.
data CodeGenCASE = CGCASELeaf Word8 | CGCASENext CodeGenCASE deriving (Eq, Ord, Show)

-- | Generate the symbolic interfaces for the code-generation ADTs.
mkSymbolic [''CodeGenADT, ''CodeGenEnum, ''CodeGenEnvelope, ''CodeGenTree, ''CodeGenForest, ''CodeGenEven, ''CodeGenOdd, ''CodeGenLoop, ''CodeGenCollections, ''CodeGenNativeCollections, ''CodeGenText, ''CodeGenArrayBox, ''CodeGenArrayEnvelope, ''CodeGenCollectionTree, ''CodeGenCase, ''CodeGenCASE]

-- | Code-generation tests.
tests :: TestTree
tests = testGroup "CodeGeneration.CgTests"
  [ goldenVsStringShow "selChecked"   $ genSelect True  "selChecked"
  , goldenVsStringShow "selUnchecked" $ genSelect False "selUnChecked"
  , goldenVsStringShow "codeGen1"       foo
  , testCase "compile through the public legacy facade" legacyPublicFacade
  , testCase "execute guarded pseudo-Boolean reductions in functions and array lambdas" scopedPseudoBoolean
  , testCase "floor long doubles inside functions and array lambdas" scopedMappedRealFloor
  , testCase "collect C runtime requirements" dependencyRequirements
  , testCase "escape assertion messages in generated C" escapedAssertionMessages
  , escapedValueLabels
  , testCase "execute IEEE native floating-point remainders" nativeFloatingRemainders
  , testCase "declare rounding modes in nested collections" collectionRoundingModes
  , testCase "relink library drivers after component changes" libraryDriverDependencies
  , arrayCollectionComparisons
  , testCase "preserve external prototypes in libraries" libraryExternalPrototypes
  , testCase "reject empty or conflicting libraries before rendering" libraryValidation
  , testCase "terminate on failed library preconditions and assertions" libraryRuntimeFailures
  , testCase "reject invalid and reserved public C names before rendering" publicCNameValidation
  , testCase "preserve public C names without local collisions" privateCBindings
  , testCase "preserve case through ADTs and structural type guards" caseSensitiveCKinds
  , testCase "frame nested array key and value type names" structuralCNameFraming
  , testCase "honor ownership across independent C library calls" libraryOwnershipContract
  , testCase "compare finite ADT set universes" finiteADTSetUniverses
  , testCase "compile exact symbolic rationals" exactSymbolicRationals
  , testCase "compile rationals with mapped integers" mappedIntegerRationals
  , testCase "compile divisibility with mapped integers" mappedIntegerDivisibility
  , testCase "compile mapped real non-linear operations" mappedRealNonLinearOperations
  , testCase "compile mapped integer exponentiation" mappedIntegerExponentiation
  , testCase "execute mapped integer arithmetic at every native width" mappedIntegerArithmetic
  , testCase "reject non-linear exact real operations" exactRealNonLinearDiagnostic
  , testCase "compile repeated exact rationals into a library" exactRationalLibrary
  , testCase "compile and execute persistent arrays" persistentArrays
  , testCase "compare finite arrays including callback and defined-function values" finiteArrayEquality
  , testCase "configure finite array equality limits" finiteArrayEqualityLimits
  , testCase "enumerate scalar and aggregate finite array keys" finiteArrayKeyKinds
  , testCase "observe finite array callback coverage and short circuiting" finiteArrayCallbacks
  , testCase "reject unsupported finite array equality domains before rendering" finiteArrayRejections
  , testCase "compare managed and floating finite array values" finiteArrayValues
  , testCase "compile and execute nested persistent arrays" nestedPersistentArrays
  , testCase "compile and execute arrays stored in tuples" tupleStoredArrays
  , testCase "compile and execute arrays stored in ADTs" adtStoredArrays
  , testCase "compile and execute arrays stored in lists" listStoredArrays
  , testCase "initialize aggregate inputs containing arrays" aggregateArrayInputs
  , testCase "initialize transitively nested array inputs" transitiveAggregateArrayInputs
  , testCase "preserve native floating-point array-key equality" nativeFloatArrayKeys
  , testCase "compile repeated array types into a library" persistentArrayLibrary
  , testCase "compile and execute a callback-backed array input" callbackArrayInput
  , testCase "compile and execute a structured lambda array" structuredLambdaArray
  , testCase "compile managed structured lambda arrays" managedStructuredLambdaArrays
  , testCase "retain an escaping managed lambda array" escapingManagedLambdaArray
  , testCase "call defined functions inside array lambdas" definedFunctionsInsideArrayLambdas
  , testCase "call defined functions from library array lambdas" definedFunctionArrayLambdaLibrary
  , testCase "return arrays from structured array lambdas" arrayValuedLambdaResults
  , testCase "return array-valued lambdas from a library" arrayValuedLambdaLibrary
  , testCase "compile nested structured array lambdas" nestedStructuredArrayLambdas
  , testCase "compile nested structured lambdas in a library" nestedStructuredArrayLambdaLibrary
  , testCase "compile and execute structured lambda tables" structuredLambdaTables
  , testCase "compile and execute a defined SBV function" definedSBVFunction
  , testCase "compose acyclic defined SBV functions" composedDefinedSBVFunctions
  , testCase "guard inactive branches in acyclic defined functions" guardedAcyclicDefinedFunctions
  , testCase "guard inactive branches in entry points" (guardedProgramEvaluation False)
  , testCase "guard inactive branches in array lambdas" (guardedProgramEvaluation True)
  , testCase "retain checks as demand-driven evaluation roots" guardedRuntimeChecks
  , testCase "preserve sharing across guarded evaluation diamonds" guardedEvaluationSharing
  , testCase "evaluate shared external calls at most once on each path" guardedExternalSharing
  , testCase "honor linker overrides, ignored assertions, and nonreserved macro prefixes" reviewedBuildOptions
  , testCase "remove all matching elements from borrowed duplicate sets" borrowedDuplicateRemoval
  , testCase "guard unselected finite-table entries and defaults" guardedTableEvaluation
  , testCase "check wide and exact indices before guarded table selection" guardedTableIndices
  , testCase "compile structural defined SBV functions" structuralDefinedSBVFunctions
  , testCase "compile managed scalar defined SBV functions" managedScalarDefinedSBVFunctions
  , testCase "compile collection defined SBV functions" collectionDefinedSBVFunctions
  , testCase "compile persistent-array defined SBV functions" persistentArrayDefinedSBVFunctions
  , testCase "compile owned-ADT defined SBV functions" ownedADTDefinedSBVFunctions
  , testCase "compile recursive defined SBV functions" recursiveDefinedSBVFunctions
  , testCase "compile recursive defined SBV functions in a library" recursiveDefinedSBVFunctionLibrary
  , testCase "compile recursive persistent-array functions" recursivePersistentArrayFunctions
  , testCase "compile recursive ADT functions" recursiveADTDefinedSBVFunctions
  , testCase "compile recursive ADT functions in a library" recursiveADTDefinedSBVFunctionLibrary
  , testCase "compile firstified higher-order list functions" higherOrderListFunctions
  , testCase "compile higher-order list functions in a library" higherOrderListFunctionLibrary
  , testCase "compile explicit hard constraints" explicitHardConstraints
  , testCase "reject solver-only constraint features" unsupportedConstraintFeatures
  , testCase "return a non-atomic value group" nonAtomicReturnGroup
  , testCase "return multiple value groups" multipleReturnGroups
  , testCase "return managed non-atomic value groups" managedReturnGroups
  , testCase "return grouped values from a library" groupedReturnLibrary
  , testCase "borrow symbolic-array input groups" (groupedArrayInputs False)
  , testCase "borrow symbolic-array input groups in a library" (groupedArrayInputs True)
  , testCase "retain grouped callback inputs across independent library calls" groupedArrayInputOwnership
  , testCase "initialize and release managed input groups" (groupedManagedInputs False)
  , testCase "initialize and release managed input groups in a library" (groupedManagedInputs True)
  , testCase "compile and execute a free array with a C definition" definedFreeArray
  , testCase "return and output owned arrays" ownedArrayResults
  , testCase "retain an escaping callback array" escapingCallbackArray
  , testCase "compile arrays with managed aggregate fields" managedAggregateArrays
  , testCase "return managed aggregate arrays from a library" managedAggregateArrayLibrary
  , testCase "compile managed aggregate lookup tables" managedAggregateTables
  , testCase "compile array-valued lookup tables" (arrayValuedTables False)
  , testCase "retain ready array-valued lookup tables" (arrayValuedTables True)
  , testCase "return managed table values from a library" managedAggregateTableLibrary
  , testCase "compile and execute structural tuples" structuralTuples
  , testCase "compile repeated tuple types into a library" structuralTupleLibrary
  , testCase "compile and execute tuples containing strings" ownedTextTuples
  , testCase "return string tuples from a generated library" ownedTextTupleLibrary
  , testCase "compile and execute tuples containing collections" ownedCollectionTuples
  , testCase "return collection tuples from a generated library" ownedCollectionTupleLibrary
  , testCase "compile tuple-valued symbolic collections" tupleValuedCollections
  , testCase "return tuple-valued collections from a library" tupleValuedCollectionLibrary
  , testCase "compile managed tuple-valued collections" managedTupleValuedCollections
  , testCase "return managed tuple-valued collections from a library" managedTupleValuedCollectionLibrary
  , testCase "compile string-valued collections and text ADTs" textAggregateCollections
  , testCase "return text ADTs from a library" textAggregateLibrary
  , testCase "compile directly nested collections" directlyNestedCollections
  , testCase "return nested collections from a library" directlyNestedCollectionLibrary
  , testCase "compile ADT-valued collections" adtValuedCollections
  , testCase "return ADT-valued collections from a library" adtValuedCollectionLibrary
  , testCase "compile and execute characters and strings" characterStrings
  , testCase "compile strings with mapped integers" mappedIntegerStrings
  , testCase "return owned strings from a generated library" ownedStringLibrary
  , testCase "compile and execute symbolic lists" symbolicLists
  , testCase "compile arbitrary-width symbolic lists" wideSymbolicLists
  , testCase "compile arbitrary floating-point symbolic lists" arbitraryFloatLists
  , testCase "preserve native floating-point list equality" nativeFloatLists
  , testCase "compile lists with mapped numeric elements" mappedNumericLists
  , testCase "return owned lists from a generated library" ownedListLibrary
  , testCase "compile lists of exact GMP values" exactGMPLists
  , testCase "compile and execute symbolic sets" symbolicSets
  , testCase "compare finite and cofinite Boolean sets" finiteUniverseSets
  , testCase "compile arbitrary-width symbolic sets" wideSymbolicSets
  , testCase "compile character symbolic sets" characterSets
  , testCase "compile arbitrary floating-point symbolic sets" arbitraryFloatSets
  , testCase "preserve native floating-point set equality" nativeFloatSets
  , testCase "compile sets with mapped numeric elements" mappedNumericSets
  , testCase "return owned sets from a generated library" ownedSetLibrary
  , testCase "compile sets of exact GMP values" exactGMPSets
  , testCase "compile and execute non-recursive ADTs" nonRecursiveADTs
  , testCase "compile and execute nested ADTs" nestedADTs
  , testCase "compile repeated ADT types into a library" nonRecursiveADTLibrary
  , testCase "compile ADTs containing managed collections" collectionADTs
  , testCase "compile recursive ADTs containing collections" recursiveCollectionADTs
  , testCase "return collection ADTs from a generated library" collectionADTLibrary
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

-- | Preserve diagnostic text literally, both in C comments and as a printf
-- argument, including characters that could otherwise alter the generated C.
escapedAssertionMessages :: Assertion
escapedAssertionMessages = withSystemTempDirectory "sbv-assertion-escaping" $ \dir -> do
  let message = "must be \"small\"; 100% %n */\n\\\n??/"
  compileToC (Just dir) "escapedAssertion" $ do
    cgOverwriteFiles True
    cgSetDriverValues [7]
    value <- cgInput "value" :: SBVCodeGen SWord8
    cgReturn (sAssert Nothing message (value .< 5) value)
  makeOptions <- generatedMakeOptions dir
  (makeExit, _, makeError) <- readProcessWithExitCode "make" (["-C", dir] ++ makeOptions) ""
  assertEqual makeError ExitSuccess makeExit
  (runExit, _, runError) <- readProcessWithExitCode (dir </> "escapedAssertion_driver") [] ""
  assertBool "Expected the violated assertion to terminate the driver" (runExit /= ExitSuccess)
  assertBool ("Assertion text was changed: " ++ runError) (("ASSERTION FAILED: " ++ message) `isInfixOf` runError)

-- | Labels are semantic no-ops even when their text contains C statements,
-- nested comment markers, preprocessing splices, trigraphs, or control bytes.
-- Exercise scalar, tuple, acyclic/recursive ADT, and persistent-array labels in
-- entry points, private functions, and closed lambdas, including static libraries.
escapedValueLabels :: TestTree
escapedValueLabels = testGroup "escaped C labels"
  [ testCase (form ++ "/" ++ scopeName ++ "/" ++ sampleName) (check (library, scope, message))
  | (form, library) <- [("program", False), ("library", True)]
  , (scopeName, scope) <- [("entry", 0 :: Int), ("function", 1), ("array lambda", 2)]
  , (sampleName, message) <- messages
  ]
 where messages = [ ("statements", "*/; abort(); /*")
                  , ("preprocessing", "nested /* comment; \\\n??/\n*/")
                  , ("control characters", "Unicode \955, NUL \0, CR \r, tab \t and control \SOH")
                  ]

       check (library, scope, message) = withSystemTempDirectory "sbv-c-label-escaping" $ \dir -> do
         let functionName = "escapedLabels"
             evaluateValue :: SWord8 -> SBool
             evaluateValue value =
               let annotate :: SymVal a => SBV a -> SBV a
                   annotate = label message
                   (firstField, secondField) = untuple (annotate (tuple (value, value + 1)))
                   tagged = annotate (sCGOne value)
                   tree   = annotate (sCGNode (sCGLeaf value) (sCGLeaf (value + 1)))
                   array  = annotate (constArray value :: SArray Word8 Word8)
               in sAnd [ annotate value .== value
                       , firstField .== value
                       , secondField .== value + 1
                       , getCGOne_1 tagged .== value
                       , getCGLeaf_1 (getCGNode_1 tree) .== value
                       , readArray array value .== value
                       ]
             evaluateScoped value = case scope of
               0 -> evaluateValue value
               1 -> smtFunction "C escaped labels" evaluateValue value
               _ -> readArray (lambdaArray evaluateValue) value
             program = do
               cgOverwriteFiles True
               cgSetDriverValues [7]
               value <- cgInput "value"
               cgReturn (evaluateScoped value)
         (_, cfg, bundle) <- if library
                               then compileToCLib' functionName [("labelComponent", program)]
                               else compileToC' functionName ((:[]) <$> program)
         renderCgPgmBundle (Just dir) (cfg, bundle)
         outputText <- compileAndRunGenerated dir functionName
         assertBool outputText (") = 1" `isInfixOf` outputText)

-- | Compare executed native remainders against constant SBV evaluation,
-- including quotient ties, negative operands, and a negative divisor.
nativeFloatingRemainders :: Assertion
nativeFloatingRemainders = mapM_ check [(7, 4), (6, 4), (-7, 4), (7, -4)]
 where check (left, right) = withSystemTempDirectory "sbv-native-remainder" $ \dir -> do
         let program = do
               cgOverwriteFiles True
               cgSetDriverValues [left, right, left, right]
               leftFloat   <- cgInput "leftFloat"   :: SBVCodeGen SFloat
               rightFloat  <- cgInput "rightFloat"  :: SBVCodeGen SFloat
               leftDouble  <- cgInput "leftDouble"  :: SBVCodeGen SDouble
               rightDouble <- cgInput "rightDouble" :: SBVCodeGen SDouble
               let expectedFloat  = fpRem (fromInteger left) (fromInteger right) :: SFloat
                   expectedDouble = fpRem (fromInteger left) (fromInteger right) :: SDouble
               cgReturn ((fpRem leftFloat rightFloat .== expectedFloat) .&& (fpRem leftDouble rightDouble .== expectedDouble))
         outputText <- compileProgramAndRunGenerated dir "nativeRemainder" program
         assertBool ("Incorrect native remainder: " ++ outputText) ("= 1" `isInfixOf` outputText)

-- | Equality observes every key, including a mismatch at the last key. The
-- same helper is available inside defined functions and retained lambdas.
finiteArrayEquality :: Assertion
finiteArrayEquality = mapM_ check [(library, identical) | library <- [False, True], identical <- [False, True]]
 where check (library, identical) = withSystemTempDirectory "sbv-finite-array-equality" $ \dir -> do
         let functionName = "finiteArrayEquality"
             program = do
               cgOverwriteFiles True
               cgSetDriverValues [3, if identical then 3 else 4]
               left  <- cgInput "left"  :: SBVCodeGen (SArray Word8 Word32)
               right <- cgInput "right" :: SBVCodeGen (SArray Word8 Word32)
               let equalArrays = smtFunction "C finite array equality" ((.==) :: SArray Word8 Word32 -> SArray Word8 Word32 -> SBool)
                   changed     = writeArray left 255 (readArray left 255 + 1)
                   another     = writeArray left 255 (readArray left 255 + 2)
                   callback    = lambdaArray (\key -> (constArray key :: SArray Bool Bool) .== constArray sTrue) :: SArray Bool Bool
               cgReturn $ sAnd [ (left .== right) .== literal identical
                               , equalArrays left right .== literal identical
                               , left ./= changed
                               , distinct [left, changed, another]
                               , (left .=== right) .== literal identical
                               , readArray callback sTrue
                               , sNot (readArray callback sFalse)
                               ]
         (_, cfg, bundle) <- if library
                               then compileToCLib' functionName [("equalityComponent", program)]
                               else compileToC' functionName ((:[]) <$> program)
         renderCgPgmBundle (Just dir) (cfg, bundle)
         outputText <- compileAndRunGenerated dir functionName
         assertBool outputText (") = 1" `isInfixOf` outputText)

-- | The limit rejects excessive work during generation, can be raised to
-- admit a 16-bit key domain, and can be set to zero to disable enumeration.
finiteArrayEqualityLimits :: Assertion
finiteArrayEqualityLimits = do
  let program limit = do
        cgOverwriteFiles True
        cgSetDriverValues [7, 7]
        mapM_ cgArrayEqualityLimit limit
        left  <- cgInput "left"  :: SBVCodeGen (SArray Word16 Word8)
        right <- cgInput "right" :: SBVCodeGen (SArray Word16 Word8)
        cgReturn (left .== right)
  mapM_ (\limit -> do
    result <- try (do (_, _, bundle) <- compileToC' "limitedEquality" (program limit)
                      evaluate (length (show bundle))) :: IO (Either ErrorCall Int)
    case result of
      Left exception -> assertBool (displayException exception) ("cgArrayEqualityLimit" `isInfixOf` displayException exception)
      Right _        -> assertFailure "Expected the array equality limit to reject generation") [Nothing, Just 0, Just (-1)]
  withSystemTempDirectory "sbv-configured-array-equality" $ \dir -> do
    outputText <- compileProgramAndRunGenerated dir "configuredEquality" (program (Just 65536))
    sourceText <- readFile (dir </> "configuredEquality.c")
    assertBool outputText (") = 1" `isInfixOf` outputText)
    assertBool "Equality must use a compact loop, not an unrolled key table" (length sourceText < 50000)

-- | Enumerate signed bit patterns, sub-native bit-vectors, sums, products,
-- and rounding modes without relying on the example driver's sample keys.
finiteArrayKeyKinds :: Assertion
finiteArrayKeyKinds = withSystemTempDirectory "sbv-finite-array-key-kinds" $ \dir -> do
  let pair :: forall key. SymVal key => Proxy key -> String -> SBVCodeGen SBool
      pair _ prefix = do
        left  <- cgInput (prefix ++ "Left")  :: SBVCodeGen (SArray key Word8)
        right <- cgInput (prefix ++ "Right") :: SBVCodeGen (SArray key Word8)
        pure (left .=== right)
      program = do
        cgOverwriteFiles True
        cgSetDriverValues (repeat 3)
        results <- sequence [ pair (Proxy @Bool) "bool"
                            , pair (Proxy @Int8) "signed"
                            , pair (Proxy @(WordN 1)) "bit"
                            , pair (Proxy @(IntN 1)) "signedBit"
                            , pair (Proxy @(WordN 5)) "wide"
                            , pair (Proxy @(IntN 5)) "signedWide"
                            , pair (Proxy @(Bool, WordN 2)) "tuple"
                            , pair (Proxy @(Maybe Bool)) "maybe"
                            , pair (Proxy @(Either Bool (WordN 2))) "either"
                            , pair (Proxy @CodeGenEnum) "enum"
                            , pair (Proxy @RoundingMode) "rounding"
                            , pair (Proxy @(FloatingPoint 2 3)) "tinyFloat"
                            , pair (Proxy @()) "unit"
                            ]
        cgReturn (sAnd results)
  outputText <- compileProgramAndRunGenerated dir "finiteArrayKeys" program
  assertBool outputText (") = 1" `isInfixOf` outputText)

-- | Exercise actual C callbacks, counting complete enumeration and early
-- mismatches. Tiny floats cover every object exactly once, including both
-- zeros and a single NaN, and library components retain independent limits.
finiteArrayCallbacks :: Assertion
finiteArrayCallbacks = withSystemTempDirectory "sbv-finite-array-callbacks" $ \dir -> do
  let component :: forall key. SymVal key => Proxy key -> Integer -> SBVCodeGen ()
      component _ limit = do
        cgOverwriteFiles True
        cgGenerateDriver False
        cgArrayEqualityLimit limit
        left  <- cgInput "left"  :: SBVCodeGen (SArray key Word8)
        right <- cgInput "right" :: SBVCodeGen (SArray key Word8)
        cgReturn (left .=== right)
      large = do
        cgOverwriteFiles True
        cgGenerateDriver False
        cgArrayEqualityLimit 65536
        left  <- cgInput "left"  :: SBVCodeGen (SArray Word16 Word8)
        right <- cgInput "right" :: SBVCodeGen (SArray Word16 Word8)
        let compareArrays = smtFunction "C configured equality" ((.==) :: SArray Word16 Word8 -> SArray Word16 Word8 -> SBool)
        cgReturn (compareArrays left right)
  _ <- compileToCLib (Just dir) "arrayEqualityLibrary"
    [("compareBytes", component (Proxy @Word8) 256)
    , ("compareTinyFloats", component (Proxy @(FloatingPoint 2 3)) 27)
    , ("compareChars", component (Proxy @Char) 0x30000)
    , ("compareLarge", large)
    ]
  compileAndRunCaller dir "arrayEqualityLibrary" $ unlines
    ["#include \"arrayEqualityLibrary.h\""
    , "#include <assert.h>"
    , "static unsigned calls, nans, positive_zeros, negative_zeros;"
    , "static SWord8 byte_lookup(const void *context, SWord8 key)"
    , "{ ++calls; return context != NULL && key == *(const unsigned *) context; }"
    , "static SWord8 float_lookup(const void *context, SFP2_3 key)"
    , "{"
    , "  (void) context; ++calls;"
    , "  unsigned raw = (unsigned) key.limb[0];"
    , "  bool nan = (raw & 12) == 12 && (raw & 3) != 0;"
    , "  nans += nan; positive_zeros += raw == 0; negative_zeros += raw == 16;"
    , "  return nan ? 1 : (SWord8) raw;"
    , "}"
    , "static SWord8 char_lookup(const void *context, SChar key)"
    , "{ (void) context; ++calls; return (SWord8) key; }"
    , "static SWord8 large_lookup(const void *context, SWord16 key)"
    , "{ (void) context; ++calls; return (SWord8) key; }"
    , "int main(void)"
    , "{"
    , "  unsigned changed = 255;"
    , "  SBVArrayInput_2_u8_2_u8 left = {byte_lookup, NULL, NULL, NULL};"
    , "  SBVArrayInput_2_u8_2_u8 right = {byte_lookup, &changed, NULL, NULL};"
    , "  assert(!compareBytes(left, right) && calls == 512);"
    , "  calls = 0; changed = 0; assert(!compareBytes(left, right) && calls == 2);"
    , "  calls = 0; assert(compareBytes(left, left) && calls == 512);"
    , "  SBVArrayInput_8_fp_e2_s3_2_u8 floats = {float_lookup, NULL, NULL, NULL};"
    , "  calls = 0; assert(compareTinyFloats(floats, floats) && calls == 54);"
    , "  assert(nans == 2 && positive_zeros == 2 && negative_zeros == 2);"
    , "  SBVArrayInput_4_char_2_u8 chars = {char_lookup, NULL, NULL, NULL};"
    , "  calls = 0; assert(compareChars(chars, chars) && calls == 0x60000);"
    , "  SBVArrayInput_3_u16_2_u8 large = {large_lookup, NULL, NULL, NULL};"
    , "  calls = 0; assert(compareLarge(large, large) && calls == 131072);"
    , "  return 0;"
    , "}"
    ]

-- | Reject disabled, oversized, infinite, recursive, and nested-array comparisons
-- with user-facing diagnostics before creating standalone or library files.
-- Opt-in permits compact native-floating and wide
-- bit-vector loops to be generated without attempting to execute them.
finiteArrayRejections :: Assertion
finiteArrayRejections = do
  let comparison :: forall key. SymVal key => Proxy key -> SBVCodeGen ()
      comparison _ = do
        cgGenerateDriver False
        left  <- cgInput "left"  :: SBVCodeGen (SArray key Word8)
        right <- cgInput "right" :: SBVCodeGen (SArray key Word8)
        cgReturn (left .=== right)
      reject diagnostic program = mapM_ (checkRejection diagnostic program) [False, True]
      checkRejection diagnostic program library = withSystemTempDirectory "sbv-array-equality-rejection" $ \dir -> do
        let closed = cgGenerateDriver False >> cgReturn sTrue
            action | library = void $ compileToCLib (Just dir) "rejectedLibrary" [("closedComponent", closed), ("rejectedEquality", program)]
                   | True    = compileToC (Just dir) "rejectedEquality" program
        result <- try action :: IO (Either ErrorCall ())
        case result of
          Left exception -> do
            let message = displayException exception
            assertBool message (diagnostic `isInfixOf` message)
            assertBool "An intentional array-equality limit must not be reported as an internal error"
                       (not ("Unexpected" `isInfixOf` message))
          Right _ -> assertFailure "Expected array equality to reject generation"
        assertEqual "Rejected equality must not create any component files" [] =<< listDirectory dir
      checkCompact program = do
        (_, _, bundle) <- compileToC' "largeDomain" (cgArrayEqualityLimit (2 ^ (673 :: Int)) >> program)
        assertBool "Explicitly admitted large domains must generate compact loops" (length (show bundle) < 100000)
  mapM_ (reject "cgArrayEqualityLimit")
    [comparison (Proxy @Word32), comparison (Proxy @(WordN 673)), comparison (Proxy @Float)
    , cgArrayEqualityLimit 26 >> comparison (Proxy @(FloatingPoint 2 3))]
  reject "disabled by cgArrayEqualityLimit 0" (cgArrayEqualityLimit 0 >> comparison (Proxy @Bool))
  mapM_ (reject "cannot enumerate key domain")
    [comparison (Proxy @Integer), comparison (Proxy @String), comparison (Proxy @CodeGenTree)]
  reject "Nested extensional array equality" $ do
    cgGenerateDriver False
    left  <- cgInput "left"  :: SBVCodeGen (SArray Bool (ArrayModel Bool Word8))
    right <- cgInput "right" :: SBVCodeGen (SArray Bool (ArrayModel Bool Word8))
    cgReturn (left .== right)
  mapM_ checkCompact [comparison (Proxy @Float), comparison (Proxy @Double), comparison (Proxy @(WordN 673))]

-- | Array values use structural object equality, including managed GMP,
-- collection and ADT values, NaNs, and the distinction between signed zeros.
finiteArrayValues :: Assertion
finiteArrayValues = withSystemTempDirectory "sbv-finite-array-values" $ \dir -> do
  let pair :: forall value. SymVal value => Proxy value -> String -> SBVCodeGen SBool
      pair _ prefix = do
        left  <- cgInput (prefix ++ "Left")  :: SBVCodeGen (SArray Bool value)
        right <- cgInput (prefix ++ "Right") :: SBVCodeGen (SArray Bool value)
        pure (left .=== right)
      program = do
        cgOverwriteFiles True
        cgSetDriverValues (repeat 3)
        results <- sequence [ pair (Proxy @Integer) "integer"
                            , pair (Proxy @Rational) "rational"
                            , pair (Proxy @String) "string"
                            , pair (Proxy @[Integer]) "list"
                            , pair (Proxy @(RCSet Word8)) "set"
                            , pair (Proxy @(Maybe Integer)) "adt"
                            ]
        bits <- cgInput "bits" :: SBVCodeGen SWord32
        let array value = constArray value :: SArray Bool Float
            nanValue    = sWord32AsSFloat (bits .|. 0x7fc00000)
            positive    = sWord32AsSFloat (bits .&. 0)
            negative    = sWord32AsSFloat ((bits .&. 0) .|. 0x80000000)
        cgReturn $ sAnd (results ++ [array nanValue .=== array (nanValue + 1), sNot (array positive .=== array negative)])
  outputText <- compileProgramAndRunGenerated dir "finiteArrayValues" program
  assertBool outputText (") = 1" `isInfixOf` outputText)

-- | Discover rounding-mode declarations through collection element kinds,
-- and compile their borrowed/owned interfaces with strict C warnings.
collectionRoundingModes :: Assertion
collectionRoundingModes = withSystemTempDirectory "sbv-collection-rounding" $ \dir -> do
  compileToC (Just dir) "collectionRounding" $ do
    cgOverwriteFiles True
    values <- cgInput "values" :: SBVCodeGen (SList RoundingMode)
    modes  <- cgInput "modes"  :: SBVCodeGen (SList [RoundingMode])
    cgOutput "modesResult" modes
    cgReturn values
  makeOptions <- generatedMakeOptions dir
  (makeExit, _, makeError) <- readProcessWithExitCode "make" (["-C", dir] ++ makeOptions) ""
  assertEqual makeError ExitSuccess makeExit
  _ <- compileAndRunGenerated dir "collectionRounding"
  pure ()

-- | The driver must wait for its archive in parallel builds and become stale
-- whenever a component source changes, even if the public header is unchanged.
libraryDriverDependencies :: Assertion
libraryDriverDependencies = withSystemTempDirectory "sbv-library-dependencies" $ \dir -> do
  _ <- compileToCLib (Just dir) "dependencyLibrary"
    [("component", do cgOverwriteFiles True
                      value <- cgInput "value" :: SBVCodeGen SWord8
                      cgReturn (value + 1))]
  makeOptions <- generatedMakeOptions dir
  (makeExit, _, makeError) <- readProcessWithExitCode "make" (["-j2", "-C", dir] ++ makeOptions) ""
  assertEqual makeError ExitSuccess makeExit
  (queryExit, _, queryError) <- readProcessWithExitCode "make" ["-q", "-C", dir, "-W", "component.c", "dependencyLibrary_driver"] ""
  assertEqual queryError (ExitFailure 1) queryExit

-- | Reject direct and nested array comparisons, including sequence operations
-- that implicitly compare elements and comparisons inside defined functions.
-- Every rejection must precede file creation, even after a valid library entry.
arrayCollectionComparisons :: TestTree
arrayCollectionComparisons = testGroup "reject comparisons of array-valued collections"
  [ testCase (testName ++ if library then " library" else " standalone") (checkOutput testName program library)
  | (testName, program) <- programs, library <- [False, True]
  ]
 where binary :: forall a b. (SymVal a, SymVal b) => Proxy a -> (SBV a -> SBV a -> SBV b) -> SBVCodeGen ()
       binary _ operation = do
         cgGenerateDriver False
         left  <- cgInput "left"  :: SBVCodeGen (SBV a)
         right <- cgInput "right" :: SBVCodeGen (SBV a)
         cgReturn (operation left right)

       comparisons :: SymVal a => Proxy a -> [(String, SBVCodeGen ())]
       comparisons proxy = [("equal", binary proxy (.==)), ("distinct", binary proxy (./=)), ("objectEqual", binary proxy (.===))]

       -- ArrayModel deliberately has no Haskell Eq instance, so construct the
       -- sequence primitives directly to test the backend boundary independently
       -- of the public list API's concrete-folding constraints.
       sequenceExpr :: forall a b. (SymVal a, SymVal b)
                    => (Kind -> SeqOp) -> SList a -> SList a -> [SVal] -> SBV b
       sequenceExpr operation left right extra = SBV $ SVal resultKind $ Right $ cache $ \st -> do
         arguments <- mapM (svToSV st) ([unSBV left, unSBV right] ++ extra)
         newExpr st resultKind (SBVApp (SeqOp (operation (kindOf (Proxy @a)))) arguments)
        where resultKind = kindOf (Proxy @b)

       sequences :: forall a. SymVal a => Proxy [a] -> [(String, SBVCodeGen ())]
       sequences proxy = comparisons proxy ++
         [ ("indexOf",  binary proxy (\left right -> sequenceExpr SeqIndexOf left right [unSBV (1 :: SInteger)] :: SInteger))
         , ("contains", predicate SeqContains)
         , ("prefix",   predicate SeqPrefixOf)
         , ("suffix",   predicate SeqSuffixOf)
         , ("replace",  binary proxy (\left right -> sequenceExpr SeqReplace left right [unSBV left] :: SList a))
         ]
        where predicate operation = binary proxy (\left right -> sequenceExpr operation left right [] :: SBool)

       named prefix = map (B.first (prefix ++))

       programs = named "list_"      (sequences   (Proxy @[ArrayModel Word8 Word8]))
               ++ named "listTuple_" (sequences   (Proxy @[(Word8, ArrayModel Word8 Word8)]))
               ++ named "nested_"    (sequences   (Proxy @[[ArrayModel Word8 Word8]]))
               ++ named "tuple_"     (comparisons (Proxy @(Word8, ArrayModel Word8 Word8)))
               ++ named "adt_"       (comparisons (Proxy @CodeGenArrayBox))
               ++ named "envelope_"  (comparisons (Proxy @CodeGenArrayEnvelope))
               ++ named "recursive_" (comparisons (Proxy @(Either CodeGenTree CodeGenArrayBox)))
               ++ [ ("defined", binary (Proxy @[ArrayModel Word8 Word8]) (smtFunction "compareArrayElements" (.===)))
                  , ("definedSearch", binary (Proxy @[ArrayModel Word8 Word8])
                      (smtFunction "findArrayElements" (\left right -> sequenceExpr SeqIndexOf left right [unSBV (0 :: SInteger)] :: SInteger)))
                  , ("lambda", cgReturn (lambdaArray (\index -> tuple (constArray index :: SArray Word8 Word8, index)
                                                          .=== tuple (constArray (index + 1) :: SArray Word8 Word8, index))
                                         :: SArray Word8 Bool))
                  , ("arrayKeys", do value <- cgInput "value" :: SBVCodeGen (SArray (Word8, ArrayModel Word8 Word8) Word8)
                                     cgReturn value)
                  ]

       checkOutput testName program library = withSystemTempDirectory "sbv-array-comparison-rejection" $ \dir -> do
         let valid = cgGenerateDriver False >> cgReturn sTrue
             action | library = void $ compileToCLib (Just dir) "rejectedLibrary" [("validComponent", valid), (testName, program)]
                    | True    = compileToC (Just dir) testName program
         result <- try action :: IO (Either ErrorCall ())
         case result of
           Left exception -> do
             let message = displayException exception
             assertBool (testName ++ ": " ++ message) ("extensional array equality" `isInfixOf` message)
             assertBool (testName ++ ": intentional rejection must not be an internal compiler error")
                        (not ("Unexpected" `isInfixOf` message))
           Right _ -> assertFailure (testName ++ ": expected generation to reject array-element comparison")
         assertEqual (testName ++ ": rejected comparisons must not create any files") [] =<< listDirectory dir

-- | An external C provider may return a borrowed set containing duplicates.
-- Removing an element must count every retained slot before exporting it.
borrowedDuplicateRemoval :: Assertion
borrowedDuplicateRemoval = withSystemTempDirectory "sbv-duplicate-set" $ \dir -> do
  compileToC (Just dir) "removeDuplicates" $ do
    cgOverwriteFiles True
    cgGenerateDriver False
    cgAddPrototype ["SBVSet_u8 duplicates(SWord8);"]
    cgAddDecl [ "SBVSet_u8 duplicates(SWord8 unused) { (void) unused; static const SWord8 values[] = {7, 7, 9};"
              , "return (SBVSet_u8) {values, 3, false}; }"
              , "int main(void) { SBVSet_u8 result = removeDuplicates(0);"
              , "int failed = result.length != 1 || result.data[0] != 9;"
              , "sbv_set_release_u8(&result); return failed; }"
              ]
    input <- cgInput "input" :: SBVCodeGen SWord8
    cgReturn (SS.delete 7 (uninterpret "duplicates" input :: SSet Word8))
  runEmbeddedCaller dir "removeDuplicates"

-- | Instrument an external function: a branch-local demand followed by an
-- unconditional demand must not repeat the call, and a dead arm must not call it.
guardedExternalSharing :: Assertion
guardedExternalSharing = withSystemTempDirectory "sbv-shared-external" $ \dir -> do
  compileToC (Just dir) "sharedExternal" $ do
    cgOverwriteFiles True
    cgGenerateDriver False
    cgAddPrototype ["SWord8 counted(SWord8);"]
    cgAddDecl [ "static unsigned calls;"
              , "SWord8 counted(SWord8 x) { ++calls; return x; }"
              , "int main(void) { SWord8 first, second;"
              , "sharedExternal(true, 7, &first, &second); if (calls != 1 || first != 7 || second != 7) return 1;"
              , "calls = 0; sharedExternal(false, 8, &first, &second); return calls != 1 || first != 0 || second != 8; }"
              ]
    condition <- cgInput "condition" :: SBVCodeGen SBool
    value <- cgInput "value" :: SBVCodeGen SWord8
    let shared = uninterpret "counted" value :: SWord8
    cgOutput "first" (ite condition shared 0)
    cgOutput "second" shared
  runEmbeddedCaller dir "sharedExternal"

-- | Build a translation unit containing its own test main, preserving the
-- same compilation, sanitizer, and dependency flags at the final link step.
runEmbeddedCaller :: FilePath -> String -> Assertion
runEmbeddedCaller dir entry = do
  writeFile (dir </> "caller.mk") $ unlines
    [entry ++ ": " ++ entry ++ ".o"
    , "\t${CC} ${CCFLAGS} $^ -o $@ ${LDFLAGS} ${SBV_LIBS}"
    ]
  makeOptions <- generatedMakeOptions dir
  (buildExit, _, buildError) <- readProcessWithExitCode "make" (["-C", dir, entry] ++ makeOptions) ""
  assertEqual buildError ExitSuccess buildExit
  (runExit, _, runError) <- readProcessWithExitCode (dir </> entry) [] ""
  assertEqual runError ExitSuccess runExit

-- | Linker settings must survive a caller's LDFLAGS, and disabling assertions
-- must remove executable checks without imposing floating rules on integer C.
reviewedBuildOptions :: Assertion
reviewedBuildOptions = withSystemTempDirectory "sbv-reviewed-options" $ \dir -> do
  compileToC (Just dir) "INTERVAL" $ do
    cgOverwriteFiles True
    cgIgnoreSAssert True
    cgAddLDFlags ["-lm"]
    cgSetDriverValues [7]
    value <- cgInput "PRIMARY" :: SBVCodeGen SInteger
    cgReturn (sAssert Nothing "deliberately disabled" (value .< 0) (value + 1))
  makefile <- readFile (dir </> "Makefile")
  header <- readFile (dir </> "INTERVAL.h")
  assertBool makefile (not ("-ffp-contract" `isInfixOf` makefile))
  assertBool "cgAddLDFlags must contribute to separately retained link dependencies"
             ("SBV_LIBS?=" `isInfixOf` makefile && "-lm" `isInfixOf` makefile)
  assertBool header (not ("__FAST_MATH__" `isInfixOf` header))
  makeOptions <- generatedMakeOptions dir
  (buildExit, _, buildError) <- readProcessWithExitCode "make" (["-C", dir, "LDFLAGS="] ++ makeOptions) ""
  assertEqual buildError ExitSuccess buildExit
  (runExit, outputText, runError) <- readProcessWithExitCode (dir </> "INTERVAL_driver") [] ""
  assertEqual runError ExitSuccess runExit
  assertBool outputText ("=8" `isInfixOf` outputText)

-- | A library header must retain user prototypes needed by its translation
-- units, even when the external implementation is supplied at final linking.
libraryExternalPrototypes :: Assertion
libraryExternalPrototypes = withSystemTempDirectory "sbv-library-prototypes" $ \dir -> do
  _ <- compileToCLib (Just dir) "prototypeLibrary"
    [("externalCall", do cgOverwriteFiles True
                         cgAddPrototype ["SWord8 external(SWord8);"]
                         value <- cgInput "value" :: SBVCodeGen SWord8
                         cgReturn (uninterpret "external" value :: SWord8))]
  makeOptions <- generatedMakeOptions dir
  (makeExit, _, makeError) <- readProcessWithExitCode "make" (["-C", dir, "externalCall.o"] ++ makeOptions) ""
  assertEqual makeError ExitSuccess makeExit

-- | Reject invalid library layouts before rendering any files. Driver symbols
-- are checked separately from file names, and disabled drivers reserve neither.
libraryValidation :: Assertion
libraryValidation = do
  mapM_ check
    [("emptyLibrary", [], "at least one component")
    , ("duplicateLibrary", [("duplicate", program True), ("duplicate", program True)], "Duplicate component names")
    , ("fileLibrary", [("fileLibrary_driver", program True)], "Conflicting generated file names")
    , ("symbolLibrary", [("entry", program True), ("entry_driver", program False)], "Conflicting generated entry points")
    , ("mainLibrary", [("main", program True)], "reserved C/backend name")
    , ("caseLibrary", [("entry", program True), ("Entry", program True)], "Conflicting generated file names")
    ]
  withSystemTempDirectory "sbv-library-no-drivers" $ \dir -> do
    _ <- compileToCLib (Just dir) "noDriverLibrary"
      [("noDriverLibrary_driver", program False), ("entry", program False), ("entry_driver", program False)]
    makeOptions <- generatedMakeOptions dir
    (makeExit, _, makeError) <- readProcessWithExitCode "make" (["-C", dir] ++ makeOptions) ""
    assertEqual makeError ExitSuccess makeExit
 where program driver = do
         cgOverwriteFiles True
         cgGenerateDriver driver
         value <- cgInput "value" :: SBVCodeGen SWord8
         cgReturn value

       check (libName, components, diagnostic) = withSystemTempDirectory "sbv-library-validation" $ \dir -> do
         result <- try (compileToCLib (Just dir) libName components) :: IO (Either ErrorCall [()])
         case result of
           Left exception -> assertBool (displayException exception) (diagnostic `isInfixOf` displayException exception)
           Right _        -> assertBool ("Expected library rejection: " ++ libName) False
         assertEqual "Invalid libraries must not write files" [] =<< listDirectory dir

-- | Check all public naming entry points and ensure diagnostics precede any
-- file writes, including names that could otherwise escape the output directory.
publicCNameValidation :: Assertion
publicCNameValidation = do
  mapM_ (\badName -> rejects $ \dir -> compileToC (Just dir) badName scalar)
    ["", "my-function", "../escape", "line\nbreak", "switch", "9lives", "caf\233", "sbv_bv_s16_mul", "SBVList_u8", "SFP7_19", "__result", "printf", "remainder", "uint32_t"]
  rejects $ \dir -> compileToC (Just dir) "badInput" $ do
    value <- cgInput "switch" :: SBVCodeGen SWord8
    cgReturn value
  rejects $ \dir -> compileToC (Just dir) "badOutput" $ do
    value <- cgInput "value" :: SBVCodeGen SWord8
    cgOutput "sbv_output_0" value
  rejects $ \dir -> compileToC (Just dir) "badInputGroup" $ do
    values <- cgInputArr 2 "my-values" :: SBVCodeGen [SWord8]
    cgReturnArr values
  rejects $ \dir -> compileToC (Just dir) "badOutputGroup" $ cgOutputArr "int" [literal (3 :: Word8)]
  rejects $ \dir -> void $ compileToCLib (Just dir) "my-library" [("component", scalar)]
  rejects $ \dir -> void $ compileToCLib (Just dir) "validLibrary" [("my-component", scalar)]
 where scalar = do
         value <- cgInput "value" :: SBVCodeGen SWord8
         cgReturn value

       rejects generate = withSystemTempDirectory "sbv-c-names" $ \dir -> do
         result <- try (generate dir) :: IO (Either ErrorCall ())
         case result of
           Left exception -> assertBool (displayException exception) ("Invalid" `isInfixOf` displayException exception)
           Right _        -> assertBool "Expected a public name diagnostic" False
         assertEqual "Invalid names must not write files" [] =<< listDirectory dir

-- | Keep valid identifiers in the ABI while isolating symbolic temporaries,
-- table names, and recursively generated driver storage from user names.
privateCBindings :: Assertion
privateCBindings = withSystemTempDirectory "sbv-private-c-bindings" $ \dir -> do
  compileToC (Just dir) "s0" $ do
    cgOverwriteFiles True
    cgSetDriverValues [7, 2, 3, 4, 5]
    value      <- cgInput "s0" :: SBVCodeGen SWord8
    tableValue <- cgInput "table0" :: SBVCodeGen SWord8
    values     <- cgInput "values" :: SBVCodeGen (SList Integer)
    moreValues <- cgInput "values_data" :: SBVCodeGen (SList Integer)
    group      <- cgInputArr 1 "group" :: SBVCodeGen [SWord8]
    cgOutput "s1" (select [value, value+1, value+2] 0 tableValue)
    cgOutput "group_ctr" (sum group)
    cgOutput "values_element_0" moreValues
    cgReturn values
  headerText <- readFile (dir </> "s0.h")
  mapM_ (\fragment -> assertBool headerText (fragment `isInfixOf` headerText))
    ["SWord8 s0", "SWord8 table0", "*s1", "*group_ctr"]
  outputText <- compileAndRunGenerated dir "s0"
  mapM_ (\fragment -> assertBool outputText (fragment `isInfixOf` outputText))
    ["s1 = 9", "group_ctr = 5", "values_element_0 =", "s0(7, 2, values, values_data, group"]

-- | Distinct recursive ADTs must coexist both directly and through every
-- structural wrapper. Repeated library components must deduplicate each
-- type's helpers without suppressing the differently-cased companion.
caseSensitiveCKinds :: Assertion
caseSensitiveCKinds = mapM_ check [False, True]
 where check library = withSystemTempDirectory "sbv-case-sensitive-kinds" $ \dir -> do
         if library
            then do _ <- compileToCLib (Just dir) "caseSensitiveKinds" [("firstCase", program), ("secondCase", program)]
                    pure ()
            else compileToC (Just dir) "caseSensitiveKinds" program
         outputText <- compileAndRunGenerated dir "caseSensitiveKinds"
         mapM_ (\fragment -> assertBool outputText (fragment `isInfixOf` outputText))
           ["CGCaseNext", "CGCASENext", "lowerList =", "upperList =", "lowerSet =", "upperSet ="]

       program = do
         cgOverwriteFiles True
         cgSetDriverValues (repeat 1)
         lower      <- cgInput "lower"      :: SBVCodeGen (SBV CodeGenCase)
         upper      <- cgInput "upper"      :: SBVCodeGen (SBV CodeGenCASE)
         lowerTuple <- cgInput "lowerTuple" :: SBVCodeGen (SBV (CodeGenCase, Word8))
         upperTuple <- cgInput "upperTuple" :: SBVCodeGen (SBV (CodeGenCASE, Word8))
         lowerList  <- cgInput "lowerListInput" :: SBVCodeGen (SList CodeGenCase)
         upperList  <- cgInput "upperListInput" :: SBVCodeGen (SList CodeGenCASE)
         lowerSet   <- cgInput "lowerSetInput"  :: SBVCodeGen (SSet CodeGenCase)
         upperSet   <- cgInput "upperSetInput"  :: SBVCodeGen (SSet CodeGenCASE)
         lowerArray <- cgInput "lowerArray" :: SBVCodeGen (SArray Word8 CodeGenCase)
         upperArray <- cgInput "upperArray" :: SBVCodeGen (SArray Word8 CodeGenCASE)
         cgOutput "lowerChild" (getCGCaseNext_1 lower)
         cgOutput "upperChild" (getCGCASENext_1 upper)
         cgOutput "lowerPair" lowerTuple
         cgOutput "upperPair" upperTuple
         cgOutput "lowerList" lowerList
         cgOutput "upperList" upperList
         cgOutput "lowerSet" lowerSet
         cgOutput "upperSet" upperSet
         cgOutput "lowerArrayResult" (writeArray lowerArray 0 lower)
         cgOutput "upperArrayResult" (writeArray upperArray 0 upper)
         cgReturn (tuple (sCGCaseNext lower, sCGCASENext upper))

-- | Different placements of tuple and array boundaries produce distinct C
-- descriptor names, and the framed names agree across declarations, storage,
-- access helpers, and driver-side ownership operations.
structuralCNameFraming :: Assertion
structuralCNameFraming = withSystemTempDirectory "sbv-structural-c-names" $ \dir -> do
  compileToC (Just dir) "structuralNames" $ do
    cgOverwriteFiles True
    cgSetDriverValues [7, 0, 0]
    value <- cgInput "value" :: SBVCodeGen SWord32
    keyed <- cgInput "keyed" :: SBVCodeGen (SArray (Word8, Word16) Word32)
    paired <- cgInput "paired" :: SBVCodeGen (SArray Word8 (Word16, Word32))
    let key = tuple (1 :: SWord8, 2 :: SWord16)
        keyedResult = writeArray keyed key value
        pairedResult = writeArray paired 1 (tuple (2 :: SWord16, value))
        nested = constArray (constArray value :: SArray Word16 Word32) :: SArray Word8 (ArrayModel Word16 Word32)
        (_, pairedValue) = untuple (readArray pairedResult 1)
    cgOutput "keyedResult" keyedResult
    cgOutput "pairedResult" pairedResult
    cgOutput "nested" nested
    cgReturn (readArray keyedResult key .== value .&& pairedValue .== value .&& readArray (readArray nested 1) 2 .== value)
  headerText <- readFile (dir </> "structuralNames.h")
  mapM_ (\typeName -> assertBool headerText (typeName `isInfixOf` headerText))
    ["SBVArrayOutput_13_t2_2_u8_3_u16_3_u32"
    , "SBVArrayOutput_2_u8_14_t2_3_u16_3_u32"
    , "SBVArrayOutput_2_u8_20_array_11_3_u16_3_u32"
    ]
  outputText <- compileAndRunGenerated dir "structuralNames"
  assertBool outputText (") = 1" `isInfixOf` outputText)

-- | Use a hand-written caller to check output reuse, independent ownership,
-- borrowed array reads, and balanced callback lifetimes across library calls.
libraryOwnershipContract :: Assertion
libraryOwnershipContract = withSystemTempDirectory "sbv-library-ownership" $ \dir -> do
  let component program = do
        cgOverwriteFiles True
        cgGenerateDriver False
        program
  _ <- compileToCLib (Just dir) "ownershipLibrary"
    [("copyLists", component $ do
        values <- cgInput "values" :: SBVCodeGen (SList Word16)
        cgOutput "copy" values
        cgReturn values)
    , ("listArray", component $ do
        values <- cgInput "values" :: SBVCodeGen (SList Word16)
        cgReturn (constArray values :: SArray Word8 [Word16]))
    , ("retainArray", component $ do
        values <- cgInput "values" :: SBVCodeGen (SArray Word8 Word16)
        cgReturn (writeArray values 0 42))
    , ("readArrayValue", component $ do
        values <- cgInput "values" :: SBVCodeGen (SArray Word8 Word16)
        cgReturn (readArray values 1))
    , ("exactOutputs", component $ do
        value <- cgInput "value" :: SBVCodeGen SInteger
        cgOutput "copy" (value + 1)
        cgReturn (value + 2))
    ]
  compileAndRunCaller dir "ownershipLibrary" $ unlines
    ["#include \"ownershipLibrary.h\""
    , "#include <assert.h>"
    , "typedef struct { unsigned references; SWord16 value; } Context;"
    , "static unsigned live_contexts;"
    , "static SWord16 lookup(const void *opaque, SWord8 key)"
    , "{ const Context *context = opaque; return context->value + key; }"
    , "static const void *retain(const void *opaque)"
    , "{ Context *context = (Context *) opaque; ++context->references; return context; }"
    , "static void release(const void *opaque)"
    , "{ Context *context = (Context *) opaque; if (--context->references == 0) { --live_contexts; free(context); } }"
    , "int main(void)"
    , "{"
    , "  mpz_t input, first, second; mpz_inits(input, first, second, NULL);"
    , "  for (unsigned i = 0; i < 32; ++i) {"
    , "    SWord16 data[] = {7, 11}; SBVList_u16 borrowed = {data, 2}, copy;"
    , "    SBVList_u16 result = copyLists(borrowed, &copy);"
    , "    data[0] = 99;"
    , "    assert(copy.data[0] == 7 && result.data[0] == 7);"
    , "    sbv_list_release_u16(&copy);"
    , "    assert(result.data[1] == 11);"
    , "    copy = copyLists(result, &borrowed);"
    , "    sbv_list_release_u16(&result); sbv_list_release_u16(&borrowed);"
    , "    SBVArrayOutput_2_u8_10_list_3_u16 array = listArray(copy);"
    , "    sbv_list_release_u16(&copy);"
    , "    SBVList_u16 read = sbv_array_output_read_2_u8_10_list_3_u16(array, 3);"
    , "    SBVList_u16 saved = sbv_list_clone_u16(read);"
    , "    sbv_array_output_release_2_u8_10_list_3_u16(&array);"
    , "    assert(saved.length == 2 && saved.data[0] == 7); sbv_list_release_u16(&saved);"
    , "    Context *context = malloc(sizeof *context); assert(context != NULL);"
    , "    *context = (Context) {1, 17}; ++live_contexts;"
    , "    SBVArrayInput_2_u8_3_u16 source = {lookup, context, retain, release};"
    , "    assert(readArrayValue(source) == 18 && context->references == 1);"
    , "    SBVArrayOutput_2_u8_3_u16 owned = retainArray(source);"
    , "    release(context);"
    , "    SBVArrayOutput_2_u8_3_u16 retained = sbv_array_output_retain_2_u8_3_u16(owned);"
    , "    sbv_array_output_release_2_u8_3_u16(&owned);"
    , "    assert(readArrayValue(sbv_array_output_as_input_2_u8_3_u16(retained)) == 18);"
    , "    assert(sbv_array_output_read_2_u8_3_u16(retained, 0) == 42);"
    , "    sbv_array_output_release_2_u8_3_u16(&retained); assert(live_contexts == 0);"
    , "    mpz_set_ui(input, i); exactOutputs(input, first, second);"
    , "    assert(mpz_cmp_ui(first, i + 1) == 0 && mpz_cmp_ui(second, i + 2) == 0);"
    , "  }"
    , "  mpz_clears(input, first, second, NULL); return 0;"
    , "}"
    ]

-- | Compile and execute an independent C caller against a generated library.
-- Use its Makefile so compiler overrides, dependencies, and runtime link flags
-- match those used for the generated translation units.
compileAndRunCaller :: FilePath -> String -> String -> Assertion
compileAndRunCaller dir libraryName source = do
  writeFile (dir </> "caller.c") source
  writeFile (dir </> "caller.mk") $ unlines
    ["caller: caller.c " ++ libraryName ++ ".h " ++ libraryName ++ ".a"
    , "\t${CC} ${CCFLAGS} ${GMP_CFLAGS} caller.c " ++ libraryName ++ ".a ${LDFLAGS} ${SBV_LIBS} -o $@"
    ]
  makeOptions <- generatedMakeOptions dir
  (makeExit, _, makeError) <- readProcessWithExitCode "make" (["-C", dir, "caller"] ++ makeOptions) ""
  assertEqual makeError ExitSuccess makeExit
  (runExit, _, runError) <- readProcessWithExitCode (dir </> "caller") [] ""
  assertEqual runError ExitSuccess runExit

-- | Library calls share the standalone fail-fast contract. Exercise both
-- executable hard constraints and explicit assertions in separate processes.
libraryRuntimeFailures :: Assertion
libraryRuntimeFailures = mapM_ check [False, True]
 where check assertion = withSystemTempDirectory "sbv-library-fail-fast" $ \dir -> do
         _ <- compileToCLib (Just dir) "failFastLibrary"
           [("checkedEntry", do cgOverwriteFiles True
                                cgSetDriverValues [7]
                                value <- cgInput "value" :: SBVCodeGen SWord8
                                if assertion
                                   then cgReturn (sAssert Nothing "library assertion" (value .< 5) value)
                                   else do constrain (value .< 5)
                                           cgReturn value)]
         makeOptions <- generatedMakeOptions dir
         (makeExit, _, makeError) <- readProcessWithExitCode "make" (["-C", dir] ++ makeOptions) ""
         assertEqual makeError ExitSuccess makeExit
         (runExit, _, runError) <- readProcessWithExitCode (dir </> "failFastLibrary_driver") [] ""
         assertBool "Expected a failed library call to terminate the process" (runExit /= ExitSuccess)
         let diagnostic = if assertion then "ASSERTION FAILED" else "CONSTRAINT FAILED"
         assertBool runError (diagnostic `isInfixOf` runError)

-- | Finite sums and products have complete universes even when constructors
-- carry fields. Dynamic inputs prevent constant folding from hiding the C
-- finite/cofinite comparison; both regular and complemented inputs are tested.
finiteADTSetUniverses :: Assertion
finiteADTSetUniverses = mapM_ check [1, 2]
 where check seed = withSystemTempDirectory "sbv-finite-adt-sets" $ \dir -> do
         let program = do
               cgOverwriteFiles True
               cgSetDriverValues [seed, seed]
               simple <- cgInput "simple" :: SBVCodeGen (SSet (Maybe Bool))
               nested <- cgInput "nested" :: SBVCodeGen (SSet (Maybe (Either Bool Bool), Bool))
               let simpleUniverse = SS.fromList [Nothing, Just False, Just True]
                   alternatives   = [Nothing, Just (Left False), Just (Left True), Just (Right False), Just (Right True)]
                   nestedUniverse = SS.fromList [(value, flag) | value <- alternatives, flag <- [False, True]]
                   simpleFull     = simple `SS.union` simpleUniverse
                   nestedFull     = nested `SS.union` nestedUniverse
               cgReturn (simpleFull .== SS.full .&& nestedFull .== SS.full .&& SS.full `SS.isSubsetOf` nestedFull)
         outputText <- compileProgramAndRunGenerated dir "finiteADTUniverses" program
         assertBool outputText ("= 1" `isInfixOf` outputText)

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
  (_, _, lowLevelProgram) <- PublicLegacy.compileToC' "legacyLowLevel" (component (+ 1))
  (_, _, lowLevelLibrary) <- PublicLegacy.compileToCLib' "legacyLowLevelLibrary" [("increment", component (+ 1))]
  assertBool "Public Legacy low-level entry points must generate bundles"
             ("legacyLowLevel.c" `isInfixOf` show lowLevelProgram && "legacyLowLevelLibrary.a" `isInfixOf` show lowLevelLibrary)

-- | Build and execute a generated C program or library driver with strict
-- warnings so representation and ownership qualifier errors cannot pass silently.
compileAndRunGenerated :: FilePath -> String -> IO String
compileAndRunGenerated dir executableName = do
  makeOptions <- generatedMakeOptions dir
  (makeExit, _, makeError) <- readProcessWithExitCode "make" (["-C", dir] ++ makeOptions) ""
  assertEqual makeError ExitSuccess makeExit
  (runExit, outputText, runError) <- readProcessWithExitCode (dir </> executableName ++ "_driver") [] ""
  assertEqual runError ExitSuccess runExit
  pure outputText

-- | Exercise Unicode and embedded-NUL literals, character-based indexing,
-- string combinators, exact numeric conversions, printing, and owned results.
characterStrings :: Assertion
characterStrings = withSystemTempDirectory "sbv-character-strings" $ \dir -> do
  let program = do
        cgOverwriteFiles True
        cgSetDriverValues [7, 1, 65]
        value     <- cgInput "value"     :: SBVCodeGen SString
        index     <- cgInput "index"     :: SBVCodeGen SInteger
        character <- cgInput "character" :: SBVCodeGen SChar
        let joined      = value SL.++ literal "\955\NUL"
            numeric     = SL.replace value value (literal "123")
            parsed      = SL.strToNat numeric
            indexedChar = SL.elemAt joined index
        cgOutput "length"         (SL.length joined)
        cgOutput "lambdaIndex"    (SL.indexOf joined (literal "\955"))
        cgOutput "contains"       (literal "v7" `SL.isInfixOf` joined)
        cgOutput "prefix"         (literal "sbv" `SL.isPrefixOf` joined)
        cgOutput "suffix"         (literal "\955\NUL" `SL.isSuffixOf` joined)
        cgOutput "sameObject"     (value .=== value)
        cgOutput "ordered"        (value .< joined)
        cgOutput "slice"          (SL.subList joined 3 2)
        cgOutput "replacement"    (SL.replace joined (literal "bv") (literal "X"))
        cgOutput "indexedChar"    indexedChar
        cgOutput "characterCode"  (SC.ord indexedChar)
        cgOutput "roundTripChar"  (SC.chr (SC.ord indexedChar))
        cgOutput "inputCharacter" character
        cgOutput "parsed"         parsed
        cgOutput "rendered"       (SL.natToStr (parsed + 1))
        cgReturn joined

  stdoutText <- compileProgramAndRunGenerated dir "characterStrings" program
  headerText <- readFile (dir </> "characterStrings.h")
  mapM_ (\fragment -> assertBool ("Expected generated text output to contain " ++ show fragment ++ ", received:\n" ++ stdoutText)
                                (fragment `isInfixOf` stdoutText))
    [ ") =sbv7\955\NUL"
    , "length =6"
    , "lambdaIndex =4"
    , "contains = 1"
    , "prefix = 1"
    , "suffix = 1"
    , "sameObject = 1"
    , "ordered = 1"
    , "slice =7\955"
    , "replacement =sX7\955\NUL"
    , "indexedChar =b"
    , "characterCode =98"
    , "roundTripChar =b"
    , "inputCharacter =a"
    , "parsed =123"
    , "rendered =124"
    ]
  assertBool "Expected a length-aware public string descriptor"
             ("size_t byte_length;" `isInfixOf` headerText && "size_t length;" `isInfixOf` headerText)
  assertBool "Expected public string ownership helpers"
             ("sbv_string_clone" `isInfixOf` headerText && "sbv_string_release" `isInfixOf` headerText)

-- | Exercise string indices and numeric conversions when the user explicitly
-- selects the historical lossy native mapping for 'SInteger'.
mappedIntegerStrings :: Assertion
mappedIntegerStrings = withSystemTempDirectory "sbv-mapped-integer-strings" $ \dir -> do
  let program = do
        cgOverwriteFiles True
        cgIntegerSize 64
        cgSetDriverValues [42, 1]
        value <- cgInput "value" :: SBVCodeGen SString
        index <- cgInput "index" :: SBVCodeGen SInteger
        cgOutput "selected" (SL.elemAt value index)
        cgOutput "numeric"  (SL.strToNat (SL.replace value value (literal "99")))
        cgReturn (SL.natToStr (SL.length value + 1))

  stdoutText <- compileProgramAndRunGenerated dir "mappedIntegerStrings" program
  mapM_ (\fragment -> assertBool ("Expected mapped-integer text output to contain " ++ show fragment ++ ", received:\n" ++ stdoutText)
                                (fragment `isInfixOf` stdoutText))
    [ ") =6"
    , "selected =b"
    , "numeric = 99LL"
    ]

-- | Exercise guarded string declarations and independent owned returns from
-- multiple generated library translation units.
ownedStringLibrary :: Assertion
ownedStringLibrary = withSystemTempDirectory "sbv-owned-string-library" $ \dir -> do
  let component suffix seed = do
        cgOverwriteFiles True
        cgSetDriverValues [seed]
        value <- cgInput "value" :: SBVCodeGen SString
        cgReturn (value SL.++ suffix)

  (_, cfg, bundle) <- compileToCLib' "ownedStringLibrary"
    [ ("firstText",  component (literal "\955") 4)
    , ("secondText", component (literal "!") 5)
    ]
  renderCgPgmBundle (Just dir) (cfg, bundle)
  stdoutText <- compileAndRunGenerated dir "ownedStringLibrary"
  assertBool ("Expected both owned string results, received:\n" ++ stdoutText)
             ("sbv4\955" `isInfixOf` stdoutText && "sbv5!" `isInfixOf` stdoutText)

-- | Exercise the primitive symbolic-list operations, exact indices, borrowed
-- inputs, and independently owned output and return values.
symbolicLists :: Assertion
symbolicLists = withSystemTempDirectory "sbv-symbolic-lists" $ \dir -> do
  let program = do
        cgOverwriteFiles True
        cgSetDriverValues [10, 1]
        values <- cgInput "values" :: SBVCodeGen (SList Word16)
        index  <- cgInput "index"  :: SBVCodeGen SInteger
        let suffix      = literal ([99, 100] :: [Word16])
            joined      = values SL.++ suffix
            contains    = suffix `SL.isInfixOf` joined
            slice       = SL.subList joined 2 2
            replaced    = SL.replace joined (literal ([11, 12] :: [Word16])) (SL.singleton 77)
        cgOutput "length"      (SL.length joined)
        cgOutput "selected"    (SL.elemAt joined index)
        cgOutput "suffixIndex" (SL.indexOf joined suffix)
        cgOutput "contains"    contains
        cgOutput "prefix"      (values `SL.isPrefixOf` joined)
        cgOutput "suffix"      (suffix `SL.isSuffixOf` joined)
        cgOutput "sameObject"  (values .=== values)
        cgOutput "different"   (values ./== suffix)
        cgOutput "conditional" (ite contains joined values)
        cgOutput "slice"       slice
        cgOutput "replaced"    replaced
        cgReturn joined

  stdoutText <- compileProgramAndRunGenerated dir "symbolicLists" program
  headerText <- readFile (dir </> "symbolicLists.h")
  mapM_ (\fragment -> assertBool ("Expected generated list output to contain " ++ show fragment ++ ", received:\n" ++ stdoutText)
                                (fragment `isInfixOf` stdoutText))
    [ ") =[0x000aU, 0x000bU, 0x000cU, 0x0063U, 0x0064U]"
    , "length =5"
    , "selected = 0x000bU"
    , "suffixIndex =3"
    , "contains = 1"
    , "prefix = 1"
    , "suffix = 1"
    , "sameObject = 1"
    , "different = 1"
    , "conditional =[0x000aU, 0x000bU, 0x000cU, 0x0063U, 0x0064U]"
    , "slice =[0x000cU, 0x0063U]"
    , "replaced =[0x000aU, 0x004dU, 0x0063U, 0x0064U]"
    ]
  assertBool "Expected a typed public list descriptor"
             ("struct SBVList_u16 { const SWord16 *data; size_t length; };" `isInfixOf` headerText)
  assertBool "Expected public list ownership helpers"
             ("sbv_list_clone_u16" `isInfixOf` headerText && "sbv_list_release_u16" `isInfixOf` headerText)

-- | Check that list descriptors remain agnostic to element width by compiling
-- and executing a list whose elements use the arbitrary-width bit-vector ABI.
wideSymbolicLists :: Assertion
wideSymbolicLists = withSystemTempDirectory "sbv-wide-symbolic-lists" $ \dir -> do
  let program = do
        cgOverwriteFiles True
        cgSetDriverValues [1]
        values <- cgInput "values" :: SBVCodeGen (SList (WordN 673))
        cgOutput "length" (SL.length values)
        cgReturn values

  stdoutText <- compileProgramAndRunGenerated dir "wideSymbolicLists" program
  headerText <- readFile (dir </> "wideSymbolicLists.h")
  assertBool ("Expected the wide-list driver to report its three sample elements, received:\n" ++ stdoutText)
             ("length =3" `isInfixOf` stdoutText)
  assertBool "Expected an arbitrary-width typed list descriptor"
             ("struct SBVList_u673 { const SWord673 *data; size_t length; };" `isInfixOf` headerText)

-- | Check that arbitrary floating-point elements retain their raw interchange
-- representation and use the LibBF-backed object-equality semantics.
arbitraryFloatLists :: Assertion
arbitraryFloatLists = do
  (_, _, bundle) <- compileToC' "arbitraryFloatLists" $ do
    cgSetDriverValues [1]
    values <- cgInput "values" :: SBVCodeGen (SList (FloatingPoint 7 19))
    cgOutput "sameObject" (values .=== values)
    cgReturn values
  let generated = show bundle
  assertBool "Expected a typed arbitrary-float list descriptor"
             ("struct SBVList_fp_e7_s19 { const SFP7_19 *data; size_t length; };" `isInfixOf` generated)
  assertBool "Expected arbitrary-float list equality to use object equality"
             ("sbv_fp_e7_s19_obj_eq(left, right)" `isInfixOf` generated)

-- | Check that native floating-point list equality treats NaNs as identical
-- objects while distinguishing positive and negative zero.
nativeFloatLists :: Assertion
nativeFloatLists = withSystemTempDirectory "sbv-native-float-lists" $ \dir -> do
  let program = do
        cgOverwriteFiles True
        cgSetDriverValues [0x7fc00000, 0x00000000, 0x80000000]
        nanBits      <- cgInput "nanBits"      :: SBVCodeGen SWord32
        positiveBits <- cgInput "positiveBits" :: SBVCodeGen SWord32
        negativeBits <- cgInput "negativeBits" :: SBVCodeGen SWord32
        let nanList      = SL.singleton (sWord32AsSFloat nanBits)
            positiveList = SL.singleton (sWord32AsSFloat positiveBits)
            negativeList = SL.singleton (sWord32AsSFloat negativeBits)
        cgOutput "nanSameObject" (nanList .=== nanList)
        cgOutput "zeroObjectsDiffer" (positiveList ./== negativeList)
        cgReturn (nanList SL.++ positiveList)

  stdoutText <- compileProgramAndRunGenerated dir "nativeFloatLists" program
  assertBool ("Expected native floating-point list object equality, received:\n" ++ stdoutText)
             ("nanSameObject = 1" `isInfixOf` stdoutText && "zeroObjectsDiffer = 1" `isInfixOf` stdoutText)

-- | Exercise lists after explicitly selecting the historical native mappings
-- for unbounded integers and reals, including declaration dependency order.
mappedNumericLists :: Assertion
mappedNumericLists = withSystemTempDirectory "sbv-mapped-numeric-lists" $ \dir -> do
  let program = do
        cgOverwriteFiles True
        cgIntegerSize 64
        cgSRealType CgDouble
        cgSetDriverValues [7, 9]
        integers <- cgInput "integers" :: SBVCodeGen (SList Integer)
        reals    <- cgInput "reals"    :: SBVCodeGen (SList AlgReal)
        cgOutput "integerLength" (SL.length integers)
        cgOutput "realSameObject" (reals .=== reals)
        cgReturn integers

  stdoutText <- compileProgramAndRunGenerated dir "mappedNumericLists" program
  mapM_ (\fragment -> assertBool ("Expected mapped-numeric list output to contain " ++ show fragment ++ ", received:\n" ++ stdoutText)
                                (fragment `isInfixOf` stdoutText))
    [ "integerLength = 3LL"
    , "realSameObject = 1"
    , "[7LL, 8LL, 9LL]"
    ]

-- | Exercise guarded list declarations and independent owned returns from
-- multiple generated library translation units.
ownedListLibrary :: Assertion
ownedListLibrary = withSystemTempDirectory "sbv-owned-list-library" $ \dir -> do
  let component suffix seed = do
        cgOverwriteFiles True
        cgSetDriverValues [seed]
        values <- cgInput "values" :: SBVCodeGen (SList Word16)
        cgReturn (values SL.++ literal suffix)

  (_, cfg, bundle) <- compileToCLib' "ownedListLibrary"
    [ ("firstList",  component ([40] :: [Word16]) 4)
    , ("secondList", component ([50] :: [Word16]) 5)
    ]
  renderCgPgmBundle (Just dir) (cfg, bundle)
  stdoutText <- compileAndRunGenerated dir "ownedListLibrary"
  assertBool ("Expected both owned list results, received:\n" ++ stdoutText)
             ("[0x0004U, 0x0005U, 0x0006U, 0x0028U]" `isInfixOf` stdoutText
           && "[0x0005U, 0x0006U, 0x0007U, 0x0032U]" `isInfixOf` stdoutText)

-- | Exercise borrowed exact elements, exact indexing and comparison, list
-- operations, and deep-cloned list results across the generated C ABI.
exactGMPLists :: Assertion
exactGMPLists = withSystemTempDirectory "sbv-exact-gmp-lists" $ \dir -> do
  let program = do
        cgOverwriteFiles True
        cgSetDriverValues [10, 20, 30, 1]
        integers  <- cgInput "integers"  :: SBVCodeGen (SList Integer)
        reals     <- cgInput "reals"     :: SBVCodeGen (SList AlgReal)
        rationals <- cgInput "rationals" :: SBVCodeGen (SList Rational)
        index     <- cgInput "index"     :: SBVCodeGen SInteger
        let joinedIntegers  = integers  SL.++ literal ([13, 14] :: [Integer])
            joinedReals     = reals     SL.++ literal ([23, 24] :: [AlgReal])
            joinedRationals = rationals SL.++ literal ([33, 34] :: [Rational])
        cgOutput "length"           (SL.length joinedIntegers)
        cgOutput "selectedInteger"  (SL.elemAt joinedIntegers index)
        cgOutput "selectedReal"     (SL.elemAt joinedReals index)
        cgOutput "selectedRational" (SL.elemAt joinedRationals index)
        cgOutput "outOfRange"       (SL.elemAt joinedRationals 99)
        cgOutput "sameIntegers"     (joinedIntegers .== literal ([10, 11, 12, 13, 14] :: [Integer]))
        cgOutput "realSlice"        (SL.subList joinedReals 1 3)
        cgOutput "rationalResult"   joinedRationals
        cgReturn joinedIntegers

  stdoutText <- compileProgramAndRunGenerated dir "exactGMPLists" program
  headerText <- readFile (dir </> "exactGMPLists.h")
  mapM_ (\fragment -> assertBool ("Expected exact-list output to contain " ++ show fragment ++ ", received:\n" ++ stdoutText)
                                (fragment `isInfixOf` stdoutText))
    [ ") =[10, 11, 12, 13, 14]"
    , "length =5"
    , "selectedInteger =11"
    , "selectedReal =21"
    , "selectedRational =31"
    , "outOfRange =0"
    , "sameIntegers = 1"
    , "realSlice =[21, 22, 23]"
    , "rationalResult =[30, 31, 32, 33, 34]"
    ]
  assertBool "Expected exact list ownership to clone and clear individual GMP elements"
             ("mpz_init_set(element, value.data[i]);" `isInfixOf` headerText
           && "mpz_clear(element); free(element);" `isInfixOf` headerText
           && "mpq_set(element, value.data[i]);" `isInfixOf` headerText
           && "mpq_clear(element); free(element);" `isInfixOf` headerText)

-- | Exercise finite and cofinite symbolic sets, normalization, every primitive
-- set operation, and independently owned outputs and returns.
symbolicSets :: Assertion
symbolicSets = withSystemTempDirectory "sbv-symbolic-sets" $ \dir -> do
  let program = do
        cgOverwriteFiles True
        cgSetDriverValues [10, 12, 11, 13]
        left       <- cgInput "left"       :: SBVCodeGen (SSet Word16)
        right      <- cgInput "right"      :: SBVCodeGen (SSet Word16)
        cofinite   <- cgInput "cofinite"   :: SBVCodeGen (SSet Word16)
        element    <- cgInput "element"    :: SBVCodeGen SWord16
        let inserted             = SS.insert element left
            deleted              = SS.delete 11 inserted
            unioned              = SS.union left right
            intersected          = SS.intersection left right
            subtracted           = SS.difference left right
            mixedUnion           = SS.union left cofinite
            mixedIntersection    = SS.intersection left cofinite
            cofiniteDifference   = SS.difference cofinite left
            cofiniteInserted     = SS.insert 12 cofinite
            cofiniteDeleted      = SS.delete 14 cofinite
            otherCofinite        = SS.complement right
            cofiniteUnion        = SS.union cofinite otherCofinite
            cofiniteIntersection = SS.intersection cofinite otherCofinite
            cofiniteSubtraction  = SS.difference cofinite otherCofinite
            containsElement      = element `SS.member` unioned
            conditional          = ite containsElement intersected subtracted
        cgOutput "inserted"             inserted
        cgOutput "deleted"              deleted
        cgOutput "unioned"              unioned
        cgOutput "intersected"          intersected
        cgOutput "subtracted"           subtracted
        cgOutput "mixedUnion"           mixedUnion
        cgOutput "mixedIntersection"    mixedIntersection
        cgOutput "cofiniteDifference"   cofiniteDifference
        cgOutput "cofiniteInserted"     cofiniteInserted
        cgOutput "cofiniteDeleted"      cofiniteDeleted
        cgOutput "cofiniteUnion"        cofiniteUnion
        cgOutput "cofiniteIntersection" cofiniteIntersection
        cgOutput "cofiniteSubtraction"  cofiniteSubtraction
        cgOutput "complemented"         (SS.complement left)
        cgOutput "containsElement"      containsElement
        cgOutput "subset"               (intersected `SS.isSubsetOf` left)
        cgOutput "sameObject"           (left .=== left)
        cgOutput "different"            (left ./== right)
        cgOutput "conditional"          conditional
        cgReturn unioned

  stdoutText <- compileProgramAndRunGenerated dir "symbolicSets" program
  headerText <- readFile (dir </> "symbolicSets.h")
  mapM_ (\fragment -> assertBool ("Expected generated set output to contain " ++ show fragment ++ ", received:\n" ++ stdoutText)
                                (fragment `isInfixOf` stdoutText))
    [ ") ={0x000aU, 0x000bU, 0x000cU, 0x000dU, 0x000eU}"
    , "inserted ={0x000aU, 0x000bU, 0x000cU, 0x000dU}"
    , "deleted ={0x000aU, 0x000cU, 0x000dU}"
    , "unioned ={0x000aU, 0x000bU, 0x000cU, 0x000dU, 0x000eU}"
    , "intersected ={0x000cU}"
    , "subtracted ={0x000aU, 0x000bU}"
    , "mixedUnion =U - {0x000dU}"
    , "mixedIntersection ={0x000aU}"
    , "cofiniteDifference =U - {0x000bU, 0x000cU, 0x000dU, 0x000aU}"
    , "cofiniteInserted =U - {0x000bU, 0x000dU}"
    , "cofiniteDeleted =U - {0x000bU, 0x000cU, 0x000dU, 0x000eU}"
    , "cofiniteUnion =U - {0x000cU, 0x000dU}"
    , "cofiniteIntersection =U - {0x000bU, 0x000cU, 0x000dU, 0x000eU}"
    , "cofiniteSubtraction ={0x000eU}"
    , "complemented =U - {0x000aU, 0x000bU, 0x000cU}"
    , "containsElement = 1"
    , "subset = 1"
    , "sameObject = 1"
    , "different = 1"
    , "conditional ={0x000cU}"
    ]
  assertBool "Expected a finite/cofinite public set descriptor"
             ("struct SBVSet_u16 { const SWord16 *data; size_t length; bool is_complement; };" `isInfixOf` headerText)
  assertBool "Expected public set ownership helpers"
             ("sbv_set_clone_u16" `isInfixOf` headerText && "sbv_set_release_u16" `isInfixOf` headerText)

-- | Check equality and subset relations when regular and complemented forms
-- denote the same set over the complete Boolean universe.
finiteUniverseSets :: Assertion
finiteUniverseSets = withSystemTempDirectory "sbv-finite-universe-sets" $ \dir -> do
  let program = do
        cgOverwriteFiles True
        cgSetDriverValues [0]
        inputFull <- cgInput "inputFull" :: SBVCodeGen (SSet Bool)
        let regularTrue   = SS.fromList [True]
            cofiniteFalse = SS.complement (SS.fromList [False])
            regularFull   = SS.fromList [False, True]
            universal     = SS.full :: SSet Bool
        cgOutput "sameSingleton"   (regularTrue .== cofiniteFalse)
        cgOutput "sameUniverse"    (regularFull .== universal)
        cgOutput "leftSubset"      (regularTrue `SS.isSubsetOf` cofiniteFalse)
        cgOutput "rightSubset"     (cofiniteFalse `SS.isSubsetOf` regularTrue)
        cgOutput "normalizedInput" (inputFull .== universal)
        cgReturn (regularTrue .== cofiniteFalse .&& regularFull .== universal .&& inputFull .== universal)

  stdoutText <- compileProgramAndRunGenerated dir "finiteUniverseSets" program
  mapM_ (\fragment -> assertBool ("Expected finite-universe set output to contain " ++ show fragment ++ ", received:\n" ++ stdoutText)
                                (fragment `isInfixOf` stdoutText))
    [ ") = 1"
    , "sameSingleton = 1"
    , "sameUniverse = 1"
    , "leftSubset = 1"
    , "rightSubset = 1"
    , "normalizedInput = 1"
    ]

-- | Check that set descriptors remain agnostic to element width by compiling
-- and executing insert and membership over 673-bit elements.
wideSymbolicSets :: Assertion
wideSymbolicSets = withSystemTempDirectory "sbv-wide-symbolic-sets" $ \dir -> do
  let program = do
        cgOverwriteFiles True
        cgSetDriverValues [10, 13]
        values  <- cgInput "values"  :: SBVCodeGen (SSet (WordN 673))
        element <- cgInput "element" :: SBVCodeGen (SWord 673)
        let updated = SS.insert element values
        cgOutput "contains" (element `SS.member` updated)
        cgReturn updated

  stdoutText <- compileProgramAndRunGenerated dir "wideSymbolicSets" program
  headerText <- readFile (dir </> "wideSymbolicSets.h")
  assertBool ("Expected arbitrary-width set membership to hold, received:\n" ++ stdoutText)
             ("contains = 1" `isInfixOf` stdoutText)
  assertBool "Expected an arbitrary-width typed set descriptor"
             ("struct SBVSet_u673 { const SWord673 *data; size_t length; bool is_complement; };" `isInfixOf` headerText)

-- | Exercise character elements through the shared scalar text representation
-- without requiring string ownership inside the set descriptor.
characterSets :: Assertion
characterSets = withSystemTempDirectory "sbv-character-sets" $ \dir -> do
  let program = do
        cgOverwriteFiles True
        cgSetDriverValues [64, 70]
        values    <- cgInput "values"    :: SBVCodeGen (SSet Char)
        character <- cgInput "character" :: SBVCodeGen SChar
        let updated = SS.insert character values
        cgOutput "contains" (character `SS.member` updated)
        cgReturn updated

  stdoutText <- compileProgramAndRunGenerated dir "characterSets" program
  headerText <- readFile (dir </> "characterSets.h")
  assertBool ("Expected character-set membership to hold, received:\n" ++ stdoutText)
             ("contains = 1" `isInfixOf` stdoutText)
  assertBool "Expected a typed character set descriptor"
             ("struct SBVSet_char { const SChar *data; size_t length; bool is_complement; };" `isInfixOf` headerText)

-- | Check that arbitrary floating-point set elements retain their raw
-- interchange representation and use LibBF-backed object equality.
arbitraryFloatSets :: Assertion
arbitraryFloatSets = do
  (_, _, bundle) <- compileToC' "arbitraryFloatSets" $ do
    cgSetDriverValues [1]
    values <- cgInput "values" :: SBVCodeGen (SSet (FloatingPoint 7 19))
    cgOutput "sameObject" (values .=== values)
    cgReturn values
  let generated = show bundle
  assertBool "Expected a typed arbitrary-float set descriptor"
             ("struct SBVSet_fp_e7_s19 { const SFP7_19 *data; size_t length; bool is_complement; };" `isInfixOf` generated)
  assertBool "Expected arbitrary-float set equality to use object equality"
             ("sbv_fp_e7_s19_obj_eq(left, right)" `isInfixOf` generated)

-- | Check that native floating-point set operations treat NaNs as identical
-- objects while distinguishing positive and negative zero.
nativeFloatSets :: Assertion
nativeFloatSets = withSystemTempDirectory "sbv-native-float-sets" $ \dir -> do
  let program = do
        cgOverwriteFiles True
        cgSetDriverValues [0x7fc00000, 0x00000000, 0x80000000]
        nanBits      <- cgInput "nanBits"      :: SBVCodeGen SWord32
        positiveBits <- cgInput "positiveBits" :: SBVCodeGen SWord32
        negativeBits <- cgInput "negativeBits" :: SBVCodeGen SWord32
        let nanValue      = sWord32AsSFloat nanBits
            positiveValue = sWord32AsSFloat positiveBits
            negativeValue = sWord32AsSFloat negativeBits
            nanSet        = SS.singleton nanValue
            positiveSet   = SS.singleton positiveValue
            negativeSet   = SS.singleton negativeValue
        cgOutput "nanMember" (nanValue `SS.member` nanSet)
        cgOutput "zeroObjectsDiffer" (positiveSet ./== negativeSet)
        cgReturn (SS.union nanSet positiveSet)

  stdoutText <- compileProgramAndRunGenerated dir "nativeFloatSets" program
  assertBool ("Expected native floating-point set object equality, received:\n" ++ stdoutText)
             ("nanMember = 1" `isInfixOf` stdoutText && "zeroObjectsDiffer = 1" `isInfixOf` stdoutText)

-- | Exercise sets after explicitly selecting the historical native mappings
-- for unbounded integers and reals.
mappedNumericSets :: Assertion
mappedNumericSets = withSystemTempDirectory "sbv-mapped-numeric-sets" $ \dir -> do
  let program = do
        cgOverwriteFiles True
        cgIntegerSize 64
        cgSRealType CgDouble
        cgSetDriverValues [8, 10]
        integers <- cgInput "integers" :: SBVCodeGen (SSet Integer)
        reals    <- cgInput "reals"    :: SBVCodeGen (SSet AlgReal)
        cgOutput "integerMember" (8 `SS.member` integers)
        cgOutput "realSameObject" (reals .=== reals)
        cgReturn integers

  stdoutText <- compileProgramAndRunGenerated dir "mappedNumericSets" program
  mapM_ (\fragment -> assertBool ("Expected mapped-numeric set output to contain " ++ show fragment ++ ", received:\n" ++ stdoutText)
                                (fragment `isInfixOf` stdoutText))
    [ "integerMember = 1"
    , "realSameObject = 1"
    , "{8LL, 9LL, 10LL}"
    ]

-- | Exercise guarded set declarations and independent owned returns from
-- multiple generated library translation units.
ownedSetLibrary :: Assertion
ownedSetLibrary = withSystemTempDirectory "sbv-owned-set-library" $ \dir -> do
  let component element seed = do
        cgOverwriteFiles True
        cgSetDriverValues [seed]
        values <- cgInput "values" :: SBVCodeGen (SSet Word16)
        cgReturn (SS.insert element values)

  (_, cfg, bundle) <- compileToCLib' "ownedSetLibrary"
    [ ("firstSet",  component 40 4)
    , ("secondSet", component 50 6)
    ]
  renderCgPgmBundle (Just dir) (cfg, bundle)
  stdoutText <- compileAndRunGenerated dir "ownedSetLibrary"
  assertBool ("Expected both owned set results, received:\n" ++ stdoutText)
             ("{0x0004U, 0x0005U, 0x0006U, 0x0028U}" `isInfixOf` stdoutText
           && "{0x0006U, 0x0007U, 0x0008U, 0x0032U}" `isInfixOf` stdoutText)

-- | Exercise exact-value normalization and comparison, finite/cofinite set
-- algebra, and deep-cloned exact set results across the generated C ABI.
exactGMPSets :: Assertion
exactGMPSets = withSystemTempDirectory "sbv-exact-gmp-sets" $ \dir -> do
  let program = do
        cgOverwriteFiles True
        cgSetDriverValues [10, 12, 11, 20, 30]
        left      <- cgInput "left"      :: SBVCodeGen (SSet Integer)
        right     <- cgInput "right"     :: SBVCodeGen (SSet Integer)
        cofinite  <- cgInput "cofinite"  :: SBVCodeGen (SSet Integer)
        reals     <- cgInput "reals"     :: SBVCodeGen (SSet AlgReal)
        rationals <- cgInput "rationals" :: SBVCodeGen (SSet Rational)
        let unioned        = SS.union left right
            inserted       = SS.insert 13 left
            intersected    = SS.intersection left right
            mixedUnion     = SS.union left cofinite
            realResult     = SS.insert 23 reals
            rationalResult = SS.delete 31 rationals
        cgOutput "sameIntegers"   (left .== SS.fromList [10, 11, 12])
        cgOutput "member"         (13 `SS.member` unioned)
        cgOutput "inserted"       inserted
        cgOutput "intersected"    intersected
        cgOutput "mixedUnion"     mixedUnion
        cgOutput "realMember"     (21 `SS.member` reals)
        cgOutput "rationalMember" (31 `SS.member` rationals)
        cgOutput "realResult"     realResult
        cgOutput "rationalResult" rationalResult
        cgReturn unioned

  stdoutText <- compileProgramAndRunGenerated dir "exactGMPSets" program
  headerText <- readFile (dir </> "exactGMPSets.h")
  mapM_ (\fragment -> assertBool ("Expected exact-set output to contain " ++ show fragment ++ ", received:\n" ++ stdoutText)
                                (fragment `isInfixOf` stdoutText))
    [ ") ={10, 11, 12, 13, 14}"
    , "sameIntegers = 1"
    , "member = 1"
    , "inserted ={10, 11, 12, 13}"
    , "intersected ={12}"
    , "mixedUnion =U - {13}"
    , "realMember = 1"
    , "rationalMember = 1"
    , "realResult ={20, 21, 22, 23}"
    , "rationalResult ={30, 32}"
    ]
  assertBool "Expected exact set ownership to clone and clear individual GMP elements"
             ("mpz_init_set(element, value.data[i]);" `isInfixOf` headerText
           && "mpz_clear(element); free(element);" `isInfixOf` headerText
           && "mpq_set(element, value.data[i]);" `isInfixOf` headerText
           && "mpq_clear(element); free(element);" `isInfixOf` headerText)

-- | Exercise exact symbolic-rational construction, decomposition, arithmetic,
-- comparison, arbitrary-width conversion, and caller-owned results.
exactSymbolicRationals :: Assertion
exactSymbolicRationals = withSystemTempDirectory "sbv-exact-symbolic-rationals" $ \dir -> do
  let program = do
        cgOverwriteFiles True
        cgSetDriverValues [2, 5, 3, 7, 1]
        input    <- cgInput "input"       :: SBVCodeGen SRational
        top      <- cgInput "numerator"   :: SBVCodeGen SInteger
        bot      <- cgInput "denominator" :: SBVCodeGen SInteger
        wide     <- cgInput "wide"        :: SBVCodeGen (SWord 673)
        selector <- cgInput "selector"    :: SBVCodeGen SWord8
        let constructed = top .% bot
            summed      = input + constructed
            multiplied  = input * constructed
            divided     = constructed / input
            converted   = sFromIntegral wide :: SRational
            paired      = tuple (constructed, summed)
            wrapped     = sCGOne constructed :: SCodeGenADT Rational
            rationalMap = writeArray (constArray input :: SArray Word8 Rational) 1 constructed
            stored      = readArray rationalMap 1
            keyed       = readArray (writeArray (constArray (9 :: SWord8) :: SArray Rational Word8) constructed 7) constructed
            fiveThirds  = 5 / 3 :: SRational
            selected    = select [constructed, summed] input selector
        cgOutput "constructed" constructed
        cgOutput "summed"      summed
        cgOutput "multiplied"  multiplied
        cgOutput "divided"     divided
        cgOutput "ordered"     (constructed .< summed)
        cgOutput "converted"   converted
        cgOutput "paired"      paired
        cgOutput "wrapped"     wrapped
        cgOutput "stored"      stored
        cgOutput "rationalMap" rationalMap
        cgOutput "keyed"       keyed
        cgOutput "sameValue"   (constructed .== fiveThirds)
        cgOutput "wrappedSame" (wrapped .== wrapped)
        cgOutput "selected"    selected
        cgReturn summed

  stdoutText <- compileProgramAndRunGenerated dir "exactSymbolicRationals" program
  headerText <- readFile (dir </> "exactSymbolicRationals.h")
  mapM_ (\fragment -> assertBool ("Expected exact-rational output to contain " ++ show fragment ++ ", received:\n" ++ stdoutText)
                                (fragment `isInfixOf` stdoutText))
    [ ") =11/3"
    , "constructed =5/3"
    , "summed =11/3"
    , "multiplied =10/3"
    , "divided =5/6"
    , "ordered = 1"
    , "converted =7"
    , "paired =(5/3, 11/3)"
    , "wrapped =CGOne(5/3)"
    , "stored =5/3"
    , "rationalMap[0] =2"
    , "keyed = 7"
    , "sameValue = 1"
    , "wrappedSame = 1"
    , "selected =11/3"
    ]
  assertBool "Expected a public exact-rational input type"
             ("typedef mpq_srcptr SRational;" `isInfixOf` headerText)
  assertBool "Expected caller-owned exact-rational output and return parameters"
             ("mpq_ptr constructed" `isInfixOf` headerText && "mpq_ptr sbv_result" `isInfixOf` headerText)

-- | Exercise exact rationals when their symbolic numerator and denominator
-- operations use an explicitly selected bounded SInteger representation.
mappedIntegerRationals :: Assertion
mappedIntegerRationals = withSystemTempDirectory "sbv-mapped-integer-rationals" $ \dir -> do
  let program = do
        cgOverwriteFiles True
        cgIntegerSize 16
        cgSetDriverValues [2, 5, 3]
        input <- cgInput "input"       :: SBVCodeGen SRational
        top   <- cgInput "numerator"   :: SBVCodeGen SInteger
        bot   <- cgInput "denominator" :: SBVCodeGen SInteger
        let constructed = top .% bot
        cgOutput "constructed" constructed
        cgOutput "converted"   (sFromIntegral top :: SRational)
        cgOutput "asReal"      (sRationalToSReal constructed)
        cgReturn (input + constructed)

  stdoutText <- compileProgramAndRunGenerated dir "mappedIntegerRationals" program
  mapM_ (\fragment -> assertBool ("Expected mapped-integer rational output to contain " ++ show fragment ++ ", received:\n" ++ stdoutText)
                                (fragment `isInfixOf` stdoutText))
    [ ") =11/3"
    , "constructed =5/3"
    , "converted =5"
    , "asReal =5/3"
    ]

-- | Exercise mapped integer divisibility for an ordinary divisor, the
-- absolute value of the minimum signed integer, and an unrepresentable
-- divisor whose only representable multiple is zero.
mappedIntegerDivisibility :: Assertion
mappedIntegerDivisibility = withSystemTempDirectory "sbv-mapped-integer-divisibility" $ \dir -> do
  let program = do
        cgOverwriteFiles True
        cgIntegerSize 8
        cgSetDriverValues [-126, -128, 0, 127]
        multiple  <- cgInput "multiple" :: SBVCodeGen SInteger
        minValue  <- cgInput "minimum"  :: SBVCodeGen SInteger
        zeroValue <- cgInput "zero"     :: SBVCodeGen SInteger
        maxValue  <- cgInput "maximum"  :: SBVCodeGen SInteger
        cgReturn $ sDivides 3 multiple
               .&& sDivides 128 minValue
               .&& sDivides 129 zeroValue
               .&& sNot (sDivides 128 multiple)
               .&& sNot (sDivides 129 maxValue)

  stdoutText <- compileProgramAndRunGenerated dir "mappedIntegerDivisibility" program
  assertBool ("Expected mapped integer divisibility to succeed, received:\n" ++ stdoutText)
             (") = 1" `isInfixOf` stdoutText)

-- | Exercise every supported mapped-real transcendental operation across
-- the @float@, @double@, and @long double@ C representations.
mappedRealNonLinearOperations :: Assertion
mappedRealNonLinearOperations = withSystemTempDirectory "sbv-mapped-real-non-linear" $ \dir -> do
  let program realType = do
        cgOverwriteFiles True
        cgSRealType realType
        cgSetDriverValues [0, 1, 2, 3, 4]
        zeroValue  <- cgInput "zero"  :: SBVCodeGen SReal
        oneValue   <- cgInput "one"   :: SBVCodeGen SReal
        twoValue   <- cgInput "two"   :: SBVCodeGen SReal
        threeValue <- cgInput "three" :: SBVCodeGen SReal
        fourValue  <- cgInput "four"  :: SBVCodeGen SReal
        cgReturn $ sin zeroValue  .== 0
               .&& cos zeroValue  .== 1
               .&& tan zeroValue  .== 0
               .&& asin zeroValue .== 0
               .&& acos oneValue  .== 0
               .&& atan zeroValue .== 0
               .&& sqrt fourValue .== 2
               .&& sinh zeroValue .== 0
               .&& cosh zeroValue .== 1
               .&& tanh zeroValue .== 0
               .&& exp zeroValue  .== 1
               .&& log oneValue   .== 0
               .&& twoValue ** threeValue .== 8

      mappings = [("float", CgFloat), ("double", CgDouble), ("longDouble", CgLongDouble)]

      runMapping (suffix, realType) = do
        let executableName = "mappedRealNonLinear" ++ suffix
        stdoutText <- compileProgramAndRunGenerated dir executableName (program realType)
        assertBool ("Expected " ++ suffix ++ " non-linear operations to succeed, received:\n" ++ stdoutText)
                   (") = 1" `isInfixOf` stdoutText)

  mapM_ runMapping mappings

-- | Exercise mapped integer exponentiation with modular overflow, negative
-- exponents, signed units, and the @0 ** 0@ boundary.
mappedIntegerExponentiation :: Assertion
mappedIntegerExponentiation = withSystemTempDirectory "sbv-mapped-integer-exponentiation" $ \dir -> do
  let program = do
        cgOverwriteFiles True
        cgIntegerSize 8
        cgSetDriverValues [3, 5, -1, -3, 2, 0, 0]
        base             <- cgInput "base"             :: SBVCodeGen SInteger
        exponentValue    <- cgInput "exponent"         :: SBVCodeGen SInteger
        negativeUnit     <- cgInput "negativeUnit"     :: SBVCodeGen SInteger
        negativeExponent <- cgInput "negativeExponent" :: SBVCodeGen SInteger
        positiveBase     <- cgInput "positiveBase"     :: SBVCodeGen SInteger
        zeroBase         <- cgInput "zeroBase"         :: SBVCodeGen SInteger
        zeroExponent     <- cgInput "zeroExponent"     :: SBVCodeGen SInteger
        cgReturn $ base         .** exponentValue            .== -13
               .&& negativeUnit .** negativeExponent         .== -1
               .&& negativeUnit .** (negativeExponent + 1)   .== 1
               .&& positiveBase .** negativeExponent         .== 0
               .&& zeroBase     .** zeroExponent             .== 1

  stdoutText <- compileProgramAndRunGenerated dir "mappedIntegerExponentiation" program
  assertBool ("Expected mapped integer exponentiation to succeed, received:\n" ++ stdoutText)
             (") = 1" `isInfixOf` stdoutText)

-- | Check fixed-width integer arithmetic against independently reduced
-- mathematical results. Include signed overflow, Euclidean versus truncating
-- division, negative divisors, and the totalized public zero-divisor cases.
mappedIntegerArithmetic :: Assertion
mappedIntegerArithmetic = mapM_ check [8, 16, 32, 64]
 where check bits = withSystemTempDirectory "sbv-mapped-integer-arithmetic" $ \dir -> do
         let half = 2 ^ (bits - 1)
             low  = negate half
             high = half - 1
             oversized = 2 ^ (137 :: Int) + 3
             wrap value = (value + half) `mod` (2 * half) - half
             operands = [(high, 1), (low, -1), (low, 3), (-7, 3), (-7, -3), (7, -3)
                        , (low, low), (-1, low), (high, low), (low, 0), (0, 0), (high, high), (high, 2)]
             program = do
               cgOverwriteFiles True
               cgIntegerSize bits
               cgSetDriverValues (concatMap (\(a, b) -> [a, b]) operands ++ [oversized])
               checks <- forM (zip [0 :: Int ..] operands) $ \(index, (a, b)) -> do
                 left  <- cgInput ("left"  ++ show index) :: SBVCodeGen SInteger
                 right <- cgInput ("right" ++ show index) :: SBVCodeGen SInteger
                 let agrees actual expected = actual .== literal (wrap expected)
                     (quotient, remainder) = if b == 0 then (0, a) else quotRem a b
                     (division, modulus)   = if b == 0 then (0, a) else divMod a b
                     euclidean
                       | b == 0 = []  -- The internal Euclidean operators leave this case unconstrained.
                       | True   = [ agrees (sEDiv left right) ((a `div` abs b) * signum b)
                                  , agrees (sEMod left right) (a `mod` abs b)
                                  ]
                 pure $ sAnd $ euclidean ++
                   [ agrees (left + right) (a + b)
                   , agrees (left - right) (a - b)
                   , agrees (left * right) (a * b)
                   , agrees (negate left)  (negate a)
                   , agrees (abs left)     (abs a)
                   , agrees (left + literal oversized) (a + oversized)
                   , agrees (sQuot left right) quotient
                   , agrees (sRem  left right) remainder
                   , agrees (sDiv  left right) division
                   , agrees (sMod  left right) modulus
                   ]
               oversizedInput <- cgInput "oversized" :: SBVCodeGen SInteger
               cgReturn (sAnd checks .&& oversizedInput .== literal (wrap oversized))
         outputText <- compileProgramAndRunGenerated dir "mappedArithmetic" program
         assertBool ("Incorrect " ++ show bits ++ "-bit arithmetic: " ++ outputText) (") = 1" `isInfixOf` outputText)

-- | Check that transcendental operations over exact rational reals explain
-- how to opt into an approximate native C representation.
exactRealNonLinearDiagnostic :: Assertion
exactRealNonLinearDiagnostic = do
  result <- try (do
    (_, _, bundle) <- compileToC' "exactRealNonLinear" $ do
      value <- cgInput "value" :: SBVCodeGen SReal
      cgReturn (sin value)
    evaluate (length (show bundle))) :: IO (Either ErrorCall Int)
  case result of
    Left exception -> assertBool ("Expected an exact-real non-linear diagnostic, received:\n" ++ displayException exception)
                                 ("cannot represent sin" `isInfixOf` displayException exception
                               && "cgSRealType" `isInfixOf` displayException exception)
    Right _        -> assertBool "Expected C generation to reject non-linear exact real arithmetic" False

-- | Exercise guarded rational declarations and caller-owned rational returns
-- across multiple generated library translation units.
exactRationalLibrary :: Assertion
exactRationalLibrary = withSystemTempDirectory "sbv-exact-rational-library" $ \dir -> do
  let component increment = do
        cgOverwriteFiles True
        cgSetDriverValues [1]
        value <- cgInput "value" :: SBVCodeGen SRational
        cgReturn (value + literal increment)

  (_, cfg, bundle) <- compileToCLib' "exactRationalLibrary"
    [ ("addOneRational", component 1)
    , ("addTwoRational", component 2)
    ]
  renderCgPgmBundle (Just dir) (cfg, bundle)
  stdoutText <- compileAndRunGenerated dir "exactRationalLibrary"
  assertBool ("Expected both exact-rational library results, received:\n" ++ stdoutText)
             (") =2" `isInfixOf` stdoutText && ") =3" `isInfixOf` stdoutText)

-- | Check that ABI kinds and scalar operations contribute the exact external
-- runtime dependencies needed by their generated C bundles. The documented
-- RNE precondition must not introduce hardware-mode guards or LibBF fallbacks.
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

  (_, _, rationalBundle) <- compileToC' "requirementsRational" $ do
    value <- cgInput "value" :: SBVCodeGen SRational
    cgReturn value

  (_, _, nativeFloatBundle) <- compileToC' "requirementsNativeFloat" $ do
    value <- cgInput "value" :: SBVCodeGen SFloat
    cgReturn (fpSqrt sRoundNearestTiesToEven value)

  (_, _, roundedNativeFloatBundle) <- compileToC' "requirementsRoundedNativeFloat" $ do
    value <- cgInput "value" :: SBVCodeGen SFloat
    cgReturn (fpSqrt sRoundNearestTiesToAway value)

  (_, _, nativeLibraryBundle) <- compileToCLib' "requirementsNativeLibrary"
    [("addOne", do value <- cgInput "value" :: SBVCodeGen SFloat
                   cgReturn (fpAdd sRNE value 1))]

  assertEqual "wide bit-vectors should not add an external library" [[]]              (linkerFlags wideBundle)
  assertEqual "arbitrary floats should request LibBF and libm"       [["-lbf", "-lm"]] (linkerFlags fpBundle)
  assertEqual "exact integers should request GMP"                    [["-lgmp"]]        (linkerFlags integerBundle)
  assertEqual "exact rationals should request GMP"                   [["-lgmp"]]        (linkerFlags rationalBundle)
  assertEqual "native floating-point sqrt should request libm"       [["-lm"]]          (linkerFlags nativeFloatBundle)
  assertEqual "explicit native rounding should request LibBF and libm" [["-lbf", "-lm"]] (linkerFlags roundedNativeFloatBundle)
  assertEqual "native RNE arithmetic should not add an external library" [[]] (linkerFlags nativeLibraryBundle)
  let checkConvention bundle = do
        let rendered = show bundle
        assertBool "Generated header must document the RNE calling convention"
                   ("Enter generated code in FE_TONEAREST" `isInfixOf` rendered)
        assertBool "The RNE precondition must not add runtime mode checks or changes"
                   (not (any (`isInfixOf` rendered) ["fegetround(", "fesetround("]))
  mapM_ checkConvention [nativeFloatBundle, nativeLibraryBundle]

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

-- | Exercise array-valued initialization, immutable writes, and reads without
-- exposing a call-scoped inner array through the generated C ABI.
nestedPersistentArrays :: Assertion
nestedPersistentArrays = withSystemTempDirectory "sbv-nested-persistent-arrays" $ \dir -> do
  let program = do
        cgOverwriteFiles True
        cgSetDriverValues [5, 17, 7, 29, 2, 2, 1]
        firstDefault  <- cgInput "firstDefault"  :: SBVCodeGen SWord32
        firstStored   <- cgInput "firstStored"   :: SBVCodeGen SWord32
        secondDefault <- cgInput "secondDefault" :: SBVCodeGen SWord32
        secondStored  <- cgInput "secondStored"  :: SBVCodeGen SWord32
        outerStoreKey <- cgInput "outerStoreKey" :: SBVCodeGen SWord16
        outerReadKey  <- cgInput "outerReadKey"  :: SBVCodeGen SWord16
        innerReadKey  <- cgInput "innerReadKey"  :: SBVCodeGen SWord8
        let firstInner  = writeArray (constArray firstDefault :: SArray Word8 Word32) 1 firstStored
            secondInner = writeArray (constArray secondDefault :: SArray Word8 Word32) 1 secondStored
            outerBase   = constArray firstInner :: SArray Word16 (ArrayModel Word8 Word32)
            outer       = writeArray outerBase outerStoreKey secondInner
            selected    = readArray outer outerReadKey
            original    = readArray outer (outerReadKey + 1)
        cgOutput "selected" (readArray selected innerReadKey)
        cgReturn (readArray original innerReadKey)

  stdoutText <- compileProgramAndRunGenerated dir "nestedPersistentArrays" program
  sourceText <- readFile (dir </> "nestedPersistentArrays.c")
  mapM_ (\fragment -> assertBool ("Expected nested-array output to contain " ++ fragment ++ ", received:\n" ++ stdoutText) (fragment `isInfixOf` stdoutText))
    [ "0x00000011UL"
    , "selected = 0x0000001dUL"
    ]
  assertBool ("Expected nested array values to use retained temporary descriptors, received:\n" ++ sourceText)
             (    "sbv_array_stored_export_2_u8_3_u32(&sbv_local_array_ctx" `isInfixOf` sourceText
              && "sbv_array_ctx_end(&sbv_local_array_ctx)" `isInfixOf` sourceText
              && "sbv_local_array_descriptor_" `isInfixOf` sourceText
             )

-- | Exercise retained array descriptors in tuple construction and projection.
tupleStoredArrays :: Assertion
tupleStoredArrays = withSystemTempDirectory "sbv-tuple-stored-arrays" $ \dir -> do
  let program = do
        cgOverwriteFiles True
        cgSetDriverValues [5, 17, 1]
        defaultValue <- cgInput "defaultValue" :: SBVCodeGen SWord32
        storedValue  <- cgInput "storedValue"  :: SBVCodeGen SWord32
        key          <- cgInput "key"          :: SBVCodeGen SWord8
        let source                  = writeArray (constArray defaultValue :: SArray Word8 Word32) 1 storedValue
            pair                    = tuple (source, key) :: SBV (ArrayModel Word8 Word32, Word8)
            (restored, restoredKey) = untuple pair
        cgOutput "restoredKey" restoredKey
        cgOutput "pair" pair
        cgReturn (readArray restored key)

  stdoutText <- compileProgramAndRunGenerated dir "tupleStoredArrays" program
  sourceText <- readFile (dir </> "tupleStoredArrays.c")
  mapM_ (\fragment -> assertBool ("Expected tuple-stored array output to contain " ++ fragment ++ ", received:\n" ++ stdoutText) (fragment `isInfixOf` stdoutText))
    [ "0x00000011UL"
    , "restoredKey = 1"
    , "pair =([0] =0x00000005UL, 1)"
    ]
  assertBool ("Expected tuple construction and projection to bridge retained arrays, received:\n" ++ sourceText)
             (    ".field1 = sbv_array_stored_export_2_u8_3_u32(&sbv_local_array_ctx" `isInfixOf` sourceText
              && "sbv_local_array_descriptor_" `isInfixOf` sourceText
             )

-- | Exercise retained array descriptors in ADT construction and projection.
adtStoredArrays :: Assertion
adtStoredArrays = withSystemTempDirectory "sbv-adt-stored-arrays" $ \dir -> do
  let program = do
        cgOverwriteFiles True
        cgSetDriverValues [5, 17, 1]
        defaultValue <- cgInput "defaultValue" :: SBVCodeGen SWord32
        storedValue  <- cgInput "storedValue"  :: SBVCodeGen SWord32
        key          <- cgInput "key"          :: SBVCodeGen SWord8
        let source = writeArray (constArray defaultValue :: SArray Word8 Word32) 1 storedValue
            boxed  = sCGArrayBox source key
        cgOutput "boxedKey" (getCGArrayBox_2 boxed)
        cgOutput "boxed" boxed
        cgReturn (readArray (getCGArrayBox_1 boxed) key)

  stdoutText <- compileProgramAndRunGenerated dir "adtStoredArrays" program
  sourceText <- readFile (dir </> "adtStoredArrays.c")
  mapM_ (\fragment -> assertBool ("Expected ADT-stored array output to contain " ++ fragment ++ ", received:\n" ++ stdoutText) (fragment `isInfixOf` stdoutText))
    [ "0x00000011UL"
    , "boxedKey = 1"
    , "boxed =CGArrayBox([0] =0x00000005UL, 1)"
    ]
  assertBool ("Expected ADT construction and projection to bridge retained arrays, received:\n" ++ sourceText)
             (    ".field1 = sbv_array_stored_export_2_u8_3_u32(&sbv_local_array_ctx" `isInfixOf` sourceText
              && "sbv_local_array_descriptor_" `isInfixOf` sourceText
             )

-- | Exercise retained array descriptors in list construction, indexing, and
-- owned list outputs.
listStoredArrays :: Assertion
listStoredArrays = withSystemTempDirectory "sbv-list-stored-arrays" $ \dir -> do
  let program = do
        cgOverwriteFiles True
        cgSetDriverValues [5, 17, 1]
        defaultValue <- cgInput "defaultValue" :: SBVCodeGen SWord32
        storedValue  <- cgInput "storedValue"  :: SBVCodeGen SWord32
        key          <- cgInput "key"          :: SBVCodeGen SWord8
        let source   = writeArray (constArray defaultValue :: SArray Word8 Word32) 1 storedValue
            arrays   = SL.singleton source :: SList (ArrayModel Word8 Word32)
            restored = SL.elemAt arrays 0
        cgOutput "arrays" arrays
        cgReturn (readArray restored key)

  stdoutText <- compileProgramAndRunGenerated dir "listStoredArrays" program
  sourceText <- readFile (dir </> "listStoredArrays.c")
  mapM_ (\fragment -> assertBool ("Expected list-stored array output to contain " ++ fragment ++ ", received:\n" ++ stdoutText) (fragment `isInfixOf` stdoutText))
    [ "0x00000011UL"
    , "arrays =[[0] =0x00000005UL]"
    ]
  assertBool ("Expected list construction and indexing to bridge retained arrays, received:\n" ++ sourceText)
             (    "sbv_list_array_" `isInfixOf` sourceText
              && "sbv_array_stored_export_2_u8_3_u32(&sbv_local_array_ctx" `isInfixOf` sourceText
              && "sbv_local_array_descriptor_" `isInfixOf` sourceText
             )

-- | Exercise generated-driver initialization and cleanup for array fields in
-- tuple, ADT, and list inputs that share a single per-kind callback family.
aggregateArrayInputs :: Assertion
aggregateArrayInputs = withSystemTempDirectory "sbv-aggregate-array-inputs" $ \dir -> do
  let program = do
        cgOverwriteFiles True
        cgSetDriverValues [3, 7, 11]
        tupleInput <- cgInput "tupleInput" :: SBVCodeGen (SBV (ArrayModel Word8 (ArrayModel Word8 Word32), Word8))
        adtInput   <- cgInput "adtInput"   :: SBVCodeGen (SBV CodeGenArrayBox)
        listInput  <- cgInput "listInput"  :: SBVCodeGen (SList (ArrayModel Word8 Word32))
        let (tupleOuterArray, tupleKey) = untuple tupleInput
            tupleInnerArray             = readArray tupleOuterArray tupleKey
            adtArray                    = getCGArrayBox_1 adtInput
            adtKey                      = getCGArrayBox_2 adtInput
            listHeadArray               = SL.head listInput
            tupleValue                  = readArray tupleInnerArray 0
            adtValue                    = readArray adtArray adtKey
            listValue                   = readArray listHeadArray 0
        cgOutput "tupleValue" tupleValue
        cgOutput "adtValue" adtValue
        cgOutput "listValue" listValue
        cgReturn (tupleValue + adtValue + listValue)

  stdoutText <- compileProgramAndRunGenerated dir "aggregateArrayInputs" program
  driverText <- readFile (dir </> "aggregateArrayInputs_driver.c")
  mapM_ (\fragment -> assertBool ("Expected aggregate-array driver output to contain " ++ fragment ++ ", received:\n" ++ stdoutText)
                                (fragment `isInfixOf` stdoutText))
    [ "= 0x00000015UL"
    , "tupleValue = 0x00000003UL"
    , "adtValue = 0x00000007UL"
    , "listValue = 0x0000000bUL"
    ]
  assertBool ("Expected retained descriptors for all aggregate array inputs, received:\n" ++ driverText)
             (length (filter (isInfixOf "sbv_array_output_retain_2_u8_3_u32") (lines driverText)) >= 5)

-- | Exercise transitive ownership when tuples, lists, and ADTs hide retained
-- arrays behind one or more concrete ADT fields.
transitiveAggregateArrayInputs :: Assertion
transitiveAggregateArrayInputs = withSystemTempDirectory "sbv-transitive-array-inputs" $ \dir -> do
  let program = do
        cgOverwriteFiles True
        cgSetDriverValues [3, 7, 11]
        tupleInput    <- cgInput "tupleInput"    :: SBVCodeGen (SBV (CodeGenArrayBox, Word8))
        listInput     <- cgInput "listInput"     :: SBVCodeGen (SList (CodeGenArrayBox, Word8))
        envelopeInput <- cgInput "envelopeInput" :: SBVCodeGen (SBV CodeGenArrayEnvelope)
        let (tupleBox, tupleKey) = untuple tupleInput
            (listBox, listKey)   = untuple (SL.head listInput)
            (envelopeBox, _)     = untuple (getCGArrayEnvelope_1 envelopeInput)
            tupleValue           = readArray (getCGArrayBox_1 tupleBox) tupleKey
            listValue            = readArray (getCGArrayBox_1 listBox) listKey
            envelopeValue        = readArray (getCGArrayBox_1 envelopeBox) 0
        cgOutput "tupleValue" tupleValue
        cgOutput "listValue" listValue
        cgOutput "envelopeValue" envelopeValue
        cgReturn (tupleValue + listValue + envelopeValue)

  stdoutText <- compileProgramAndRunGenerated dir "transitiveAggregateArrayInputs" program
  headerText <- readFile (dir </> "transitiveAggregateArrayInputs.h")
  mapM_ (\fragment -> assertBool ("Expected transitive aggregate-array output to contain " ++ fragment ++ ", received:\n" ++ stdoutText)
                                (fragment `isInfixOf` stdoutText))
    [ "= 0x00000015UL"
    , "tupleValue = 0x00000003UL"
    , "listValue = 0x00000007UL"
    , "envelopeValue = 0x0000000bUL"
    ]
  assertBool ("Expected tuple ownership to cross concrete ADT fields, received:\n" ++ headerText)
             (    "sbv_adt_owned_clone_SBVADT_CodeGenArrayBox(source.field1)" `isInfixOf` headerText
              && "sbv_adt_owned_release_SBVADT_CodeGenArrayBox(&value->field1)" `isInfixOf` headerText
             )

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

-- | Exercise text, list, and set allocation inside retained array callbacks,
-- including an exact list element that shares both the GMP and list arenas.
managedStructuredLambdaArrays :: Assertion
managedStructuredLambdaArrays = withSystemTempDirectory "sbv-managed-structured-lambda-arrays" $ \dir -> do
  let program = do
        cgOverwriteFiles True
        cgSetDriverValues [2]
        key <- cgInput "key" :: SBVCodeGen SWord8
        let textSource = lambdaArray (\index ->
                           ite (index .== 2) (literal "hit") (literal "miss") SL.++ literal "!")
                         :: SArray Word8 String
            listSource = lambdaArray (\index ->
                           SL.singleton (sFromIntegral index :: SInteger) SL.++ literal [100])
                         :: SArray Word8 [Integer]
            setSource = lambdaArray (\index ->
                          SS.insert (sFromIntegral index :: SInteger) (SS.singleton 100))
                        :: SArray Word8 (RCSet Integer)
        cgOutput "textValue" (readArray textSource key)
        cgOutput "listValue" (readArray listSource key)
        cgReturn (readArray setSource key)

  stdoutText <- compileProgramAndRunGenerated dir "managedStructuredLambdaArrays" program
  mapM_ (\fragment -> assertBool ("Expected managed structured-lambda output to contain " ++ show fragment ++ ", received:\n" ++ stdoutText)
                                  (fragment `isInfixOf` stdoutText))
    [ ") ={100, 2}"
    , "textValue =hit!"
    , "listValue =[2, 100]"
    ]

-- | Return a retained lambda array whose callback constructs a tuple with
-- fresh text and list storage, then read it after the generated call returns.
escapingManagedLambdaArray :: Assertion
escapingManagedLambdaArray = withSystemTempDirectory "sbv-escaping-managed-lambda-array" $ \dir -> do
  let program = do
        cgOverwriteFiles True
        let source = lambdaArray (\index ->
                       tuple ( literal "item" SL.++ literal "!"
                             , SL.singleton (sFromIntegral index :: SWord16) SL.++ literal [99]
                             ))
                     :: SArray Word8 (String, [Word16])
        cgReturn source

  stdoutText <- compileProgramAndRunGenerated dir "escapingManagedLambdaArray" program
  sourceText <- readFile (dir </> "escapingManagedLambdaArray.c")
  assertBool ("Expected an escaping managed lambda array to retain its callback arenas, received:\n" ++ stdoutText)
             ("[0] =(item!, [0x0000U, 0x0063U])" `isInfixOf` stdoutText)
  assertBool ("Expected the escaping callback to clone managed results into retained storage, received:\n" ++ sourceText)
             ("sbv_function_ctx_retain_empty" `isInfixOf` sourceText
           && "sbv_function_result_clone_" `isInfixOf` sourceText)

-- | Call scalar and managed first-order 'smtFunction' definitions from array
-- lambdas, including a scalar signature whose body uses hidden managed arenas
-- and a managed callback that remains callable after its array escapes.
definedFunctionsInsideArrayLambdas :: Assertion
definedFunctionsInsideArrayLambdas = withSystemTempDirectory "sbv-defined-functions-in-array-lambdas" $ \dir -> do
  let program = do
        cgOverwriteFiles True
        cgSetDriverValues [12]
        key <- cgInput "key" :: SBVCodeGen SWord8
        let countDigits :: SWord8 -> SWord8
            countDigits = smtFunction "C lambda digit count" $ \value ->
              sFromIntegral (SL.length (SL.natToStr (sFromIntegral value :: SInteger)))

            decorate :: SString -> SString
            decorate = smtFunction "C lambda text decoration" $ \value ->
              literal "<" SL.++ value SL.++ literal ">"

            numericSource = lambdaArray countDigits :: SArray Word8 Word8
            textSource = lambdaArray (\index ->
                           decorate (ite (index .== 0) (literal "zero") (literal "other")))
                         :: SArray Word8 String
        cgOutput "digits" (readArray numericSource key)
        cgReturn textSource

  stdoutText <- compileProgramAndRunGenerated dir "definedFunctionsInsideArrayLambdas" program
  sourceText <- readFile (dir </> "definedFunctionsInsideArrayLambdas.c")
  mapM_ (\fragment -> assertBool ("Expected a defined-function lambda output to contain " ++ show fragment ++ ", received:\n" ++ stdoutText)
                                  (fragment `isInfixOf` stdoutText))
    [ "[0] =<zero>"
    , "digits = 2"
    ]
  assertBool ("Expected array callbacks to forward the function ownership context, received:\n" ++ sourceText)
             ("/* Uninterpreted function */ sbv_function_" `isInfixOf` sourceText
           && "sbv_function_ctx sbv_local_function_ctx" `isInfixOf` sourceText)

-- | Exercise retained arrays that call managed 'smtFunction' definitions in
-- separate translation units of one generated static library.
definedFunctionArrayLambdaLibrary :: Assertion
definedFunctionArrayLambdaLibrary = withSystemTempDirectory "sbv-defined-function-array-lambda-library" $ \dir -> do
  let component :: String -> SBVCodeGen ()
      component prefix = do
        cgOverwriteFiles True
        let decorate :: SString -> SString
            decorate = smtFunction ("C library lambda " ++ prefix) $ \value ->
              literal prefix SL.++ value

            source = lambdaArray (\index ->
                       decorate (SL.natToStr (sFromIntegral index :: SInteger)))
                     :: SArray Word8 String
        cgReturn source

  (_, cfg, bundle) <- compileToCLib' "definedFunctionArrayLambdaLibrary"
    [ ("firstLambda", component "first-")
    , ("secondLambda", component "second-")
    ]
  renderCgPgmBundle (Just dir) (cfg, bundle)
  stdoutText <- compileAndRunGenerated dir "definedFunctionArrayLambdaLibrary"
  mapM_ (\fragment -> assertBool ("Expected a library function-backed lambda output to contain " ++ show fragment ++ ", received:\n" ++ stdoutText)
                                  (fragment `isInfixOf` stdoutText))
    [ "firstLambda()[0] =first-0"
    , "secondLambda()[0] =second-0"
    ]

-- | Return direct and tuple-contained persistent arrays from retained
-- callbacks, read them during the generated call, and read the direct result
-- again after its outer array escapes.
arrayValuedLambdaResults :: Assertion
arrayValuedLambdaResults = withSystemTempDirectory "sbv-array-valued-lambda-results" $ \dir -> do
  let program = do
        cgOverwriteFiles True
        cgSetDriverValues [5]
        key <- cgInput "key" :: SBVCodeGen SWord8
        let inner :: SWord8 -> SArray Word8 Word32
            inner index = writeArray
                            (constArray (sFromIntegral index + 1 :: SWord32) :: SArray Word8 Word32)
                            index
                            99

            makeInner :: SWord8 -> SArray Word8 Word32
            makeInner = smtFunction "C lambda inner array" inner

            directSource   = lambdaArray inner :: SArray Word8 (ArrayModel Word8 Word32)
            functionSource = lambdaArray makeInner :: SArray Word8 (ArrayModel Word8 Word32)
            boxedSource    = lambdaArray (\index -> tuple (inner index, sFromIntegral index + 10 :: SWord16))
                           :: SArray Word8 (ArrayModel Word8 Word32, Word16)
            directInner   = readArray directSource key
            functionInner = readArray functionSource key
            (boxedInner, marker) = untuple (readArray boxedSource key)
        cgOutput "directStored"  (readArray directInner key)
        cgOutput "directDefault" (readArray directInner (key + 1))
        cgOutput "functionStored" (readArray functionInner key)
        cgOutput "boxedStored"   (readArray boxedInner key)
        cgOutput "marker"        marker
        cgReturn directSource

  stdoutText <- compileProgramAndRunGenerated dir "arrayValuedLambdaResults" program
  sourceText <- readFile (dir </> "arrayValuedLambdaResults.c")
  mapM_ (\fragment -> assertBool ("Expected an array-valued lambda output to contain " ++ show fragment ++ ", received:\n" ++ stdoutText)
                                  (fragment `isInfixOf` stdoutText))
    [ ")[0] =[0] =0x00000063UL"
    , "directStored = 0x00000063UL"
    , "directDefault = 0x00000006UL"
    , "functionStored = 0x00000063UL"
    , "boxedStored = 0x00000063UL"
    , "marker = 0x000fU"
    ]
  assertBool ("Expected array callback results to cross through retained descriptors, received:\n" ++ sourceText)
             ("sbv_array_stored_export_2_u8_3_u32(&sbv_local_array_ctx" `isInfixOf` sourceText
           && "SBVArrayOutput_2_u8_3_u32 * sbv_array_lambda_" `isInfixOf` sourceText)

-- | Exercise array-valued callback results in independent translation units
-- of a generated static library.
arrayValuedLambdaLibrary :: Assertion
arrayValuedLambdaLibrary = withSystemTempDirectory "sbv-array-valued-lambda-library" $ \dir -> do
  let component :: Word32 -> SBVCodeGen ()
      component value = do
        cgOverwriteFiles True
        let source = lambdaArray (\index ->
                       writeArray (constArray (literal value) :: SArray Word8 Word32) index (literal value + 1))
                     :: SArray Word8 (ArrayModel Word8 Word32)
        cgReturn source

  (_, cfg, bundle) <- compileToCLib' "arrayValuedLambdaLibrary"
    [ ("firstNestedArray", component 20)
    , ("secondNestedArray", component 30)
    ]
  renderCgPgmBundle (Just dir) (cfg, bundle)
  stdoutText <- compileAndRunGenerated dir "arrayValuedLambdaLibrary"
  mapM_ (\fragment -> assertBool ("Expected a library array-valued lambda output to contain " ++ show fragment ++ ", received:\n" ++ stdoutText)
                                  (fragment `isInfixOf` stdoutText))
    [ "firstNestedArray()[0] =[0] =0x00000015UL"
    , "secondNestedArray()[0] =[0] =0x0000001fUL"
    ]

-- | Lambda-lift closed array callbacks from a defined function and from an
-- outer array callback whose result is itself a selected callback array.
nestedStructuredArrayLambdas :: Assertion
nestedStructuredArrayLambdas = withSystemTempDirectory "sbv-nested-structured-array-lambdas" $ \dir -> do
  let program = do
        cgOverwriteFiles True
        cgSetDriverValues [1, 5, 1]
        chooseFirst <- cgInput "chooseFirst" :: SBVCodeGen SBool
        key         <- cgInput "key"         :: SBVCodeGen SWord8
        outerKey    <- cgInput "outerKey"    :: SBVCodeGen SWord8
        let choose :: SBool -> SArray Word8 Word16
            choose = smtFunction "C nested lambda choice" $ \condition ->
                       ite condition
                           (lambdaArray (\index -> sFromIntegral index + 10))
                           (lambdaArray (\index -> sFromIntegral index + 20))

            recursiveChoose :: SWord8 -> SArray Word8 Word16
            recursiveChoose = smtFunctionNoTermination "C recursive nested lambda choice" $ \count ->
                                ite (count .== 0)
                                    (lambdaArray (\index -> sFromIntegral index + 60))
                                    (recursiveChoose (count - 1))

            nested = lambdaArray (\outer ->
                       ite (outer .== 0)
                           (lambdaArray (\index -> sFromIntegral index + 30))
                           (lambdaArray (\index -> sFromIntegral index + 40)))
                     :: SArray Word8 (ArrayModel Word8 Word16)

            deep = lambdaArray (\_ ->
                     lambdaArray (\_ ->
                       lambdaArray (\index -> sFromIntegral index + 50)))
                   :: SArray Word8 (ArrayModel Word8 (ArrayModel Word8 Word16))

            chosen      = choose chooseFirst
            selected    = readArray chosen key
            nestedInner = readArray nested outerKey
            deepMiddle  = readArray deep outerKey
            deepInner   = readArray deepMiddle outerKey
            recursive   = recursiveChoose outerKey

        cgOutput "selected"       selected
        cgOutput "nestedSelected" (readArray nestedInner key)
        cgOutput "deepSelected"   (readArray deepInner key)
        cgOutput "recursive"      (readArray recursive key)
        cgReturn chosen

  stdoutText <- compileProgramAndRunGenerated dir "nestedStructuredArrayLambdas" program
  sourceText <- readFile (dir </> "nestedStructuredArrayLambdas.c")
  mapM_ (\fragment -> assertBool ("Expected nested structured-lambda output to contain " ++ fragment ++ ", received:\n" ++ stdoutText)
                                 (fragment `isInfixOf` stdoutText))
    [ ")[0] =0x000aU"
    , "selected = 0x000fU"
    , "nestedSelected = 0x002dU"
    , "deepSelected = 0x0037U"
    , "recursive = 0x0041U"
    ]
  assertBool ("Expected nested callbacks to receive lexical-scope-qualified names, received:\n" ++ sourceText)
             ("_nested_l" `isInfixOf` sourceText)

-- | Exercise lambda-lifted callbacks from private defined functions in
-- independent translation units of a generated static library.
nestedStructuredArrayLambdaLibrary :: Assertion
nestedStructuredArrayLambdaLibrary = withSystemTempDirectory "sbv-nested-structured-array-lambda-library" $ \dir -> do
  let component :: Word16 -> SBVCodeGen ()
      component offset = do
        cgOverwriteFiles True
        let choose :: SBool -> SArray Word8 Word16
            choose = smtFunction "C library nested lambda" $ \condition ->
                       ite condition
                           (lambdaArray (\index -> sFromIntegral index + literal offset))
                           (lambdaArray (\index -> sFromIntegral index + literal offset + 100))
        cgReturn (choose (literal True))

  (_, cfg, bundle) <- compileToCLib' "nestedStructuredArrayLambdaLibrary"
    [ ("firstNestedLambda", component 10)
    , ("secondNestedLambda", component 20)
    ]
  renderCgPgmBundle (Just dir) (cfg, bundle)
  stdoutText <- compileAndRunGenerated dir "nestedStructuredArrayLambdaLibrary"
  mapM_ (\fragment -> assertBool ("Expected nested structured-lambda library output to contain " ++ fragment ++ ", received:\n" ++ stdoutText)
                                 (fragment `isInfixOf` stdoutText))
    [ "firstNestedLambda()[0] =0x000aU"
    , "secondNestedLambda()[0] =0x0014U"
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

-- | Exercise structured lowering of a multi-argument 'smtFunction', including
-- collision-free C encoding of a quoted SMT identifier.
definedSBVFunction :: Assertion
definedSBVFunction = withSystemTempDirectory "sbv-defined-function" $ \dir -> do
  let program = do
        cgOverwriteFiles True
        cgSetDriverValues [3, 4, 5]
        left  <- cgInput "left"  :: SBVCodeGen SWord32
        right <- cgInput "right" :: SBVCodeGen SWord32
        wide  <- cgInput "wide"  :: SBVCodeGen (SWord 673)
        let combine  = smtFunction "defined function/@1" $ \x y -> ite (x .< y) (x + y) (x * y)
            increment = smtFunction "wide defined function" (+ 1)
        cgOutput "wideResult" (increment wide)
        cgReturn (combine left right)

  stdoutText <- compileProgramAndRunGenerated dir "definedSBVFunction" program
  sourceText <- readFile (dir </> "definedSBVFunction.c")
  assertBool ("Expected defined-function output to contain 0x00000007UL, received:\n" ++ stdoutText)
             ("0x00000007UL" `isInfixOf` stdoutText)
  assertBool ("Expected the quoted SMT function name to use a private encoded C identifier, received:\n" ++ sourceText)
             ("static SWord32 sbv_function_" `isInfixOf` sourceText
           && "/* Uninterpreted function */ sbv_function_" `isInfixOf` sourceText)
  assertBool ("Expected a defined function body to contribute its wide-bit-vector runtime, received:\n" ++ sourceText)
             ("static SWord673 sbv_function_" `isInfixOf` sourceText
           && "sbv_bv_u673_add" `isInfixOf` sourceText)

-- | Exercise an acyclic diamond of 'smtFunction' calls whose lexical name
-- ordering requires prototypes for callees emitted after their caller.
composedDefinedSBVFunctions :: Assertion
composedDefinedSBVFunctions = withSystemTempDirectory "sbv-composed-defined-functions" $ \dir -> do
  let program = do
        cgOverwriteFiles True
        cgSetDriverValues [4]
        input <- cgInput "input" :: SBVCodeGen SWord32
        let base :: SWord32 -> SWord32
            base = smtFunction "C function base" (+ 1)

            twice :: SWord32 -> SWord32
            twice = smtFunction "C function twice" $ \value -> base value * 2

            plusThree :: SWord32 -> SWord32
            plusThree = smtFunction "C function plus three" $ \value -> base value + 3

            diamond :: SWord32 -> SWord32
            diamond = smtFunction "C function diamond" $ \value -> twice value + plusThree value
        cgReturn (diamond input)

  stdoutText <- compileProgramAndRunGenerated dir "composedDefinedSBVFunctions" program
  sourceText <- readFile (dir </> "composedDefinedSBVFunctions.c")
  assertBool ("Expected composed defined-function output to contain 0x00000012UL, received:\n" ++ stdoutText)
             ("0x00000012UL" `isInfixOf` stdoutText)
  assertBool ("Expected private prototypes before the composed defined-function bodies, received:\n" ++ sourceText)
             (length (filter ("static SWord32 sbv_function_" `isInfixOf`) (lines sourceText)) == 8)

-- | Exercise private by-value C signatures for 'smtFunction' definitions over
-- a tuple and a scalar-only ADT, including projection and reconstruction.
structuralDefinedSBVFunctions :: Assertion
structuralDefinedSBVFunctions = withSystemTempDirectory "sbv-structural-defined-functions" $ \dir -> do
  let program = do
        cgOverwriteFiles True
        let adjustTuple :: SBV (Word8, Word16) -> SBV (Word8, Word16)
            adjustTuple = smtFunction "C structural tuple" $ \value ->
                            let (first, second) = untuple value
                            in tuple (first + 1, second + 2)

            adjustADT :: SCodeGenADT Word8 -> SCodeGenADT Word8
            adjustADT = smtFunction "C structural ADT" $ \value ->
                          sCGPair (getCGPair_1 value + 1) (getCGPair_2 value + 2)

        cgOutput "tupleResult" (adjustTuple (literal (4, 10)))
        cgReturn (adjustADT (literal (CGPair 7 9)))

  stdoutText <- compileProgramAndRunGenerated dir "structuralDefinedSBVFunctions" program
  mapM_ (\fragment -> assertBool ("Expected structural defined-function output to contain " ++ fragment ++ ", received:\n" ++ stdoutText)
                                 (fragment `isInfixOf` stdoutText))
    [ "CGPair(8, 0x000bU)"
    , "tupleResult =(5, 0x000cU)"
    ]

-- | Exercise transitive ownership-arena threading through composed
-- 'smtFunction' definitions producing strings and exact GMP integers.
managedScalarDefinedSBVFunctions :: Assertion
managedScalarDefinedSBVFunctions = withSystemTempDirectory "sbv-managed-scalar-defined-functions" $ \dir -> do
  let program = do
        cgOverwriteFiles True
        cgSetDriverValues [4, 5]
        inputText    <- cgInput "inputText"    :: SBVCodeGen SString
        inputInteger <- cgInput "inputInteger" :: SBVCodeGen SInteger
        let addSuffix :: SString -> SString
            addSuffix = smtFunction "C managed string suffix" $ \value -> value SL.++ literal "!"

            decorate :: SString -> SString
            decorate = smtFunction "C managed string decorate" $ \value -> literal "<" SL.++ addSuffix value SL.++ literal ">"

            increment :: SInteger -> SInteger
            increment = smtFunction "C managed integer increment" (+ 1)

            squareIncrement :: SInteger -> SInteger
            squareIncrement = smtFunction "C managed integer square" $ \value -> increment value * increment value

        cgOutput "decorated" (decorate inputText)
        cgReturn (squareIncrement inputInteger)

  stdoutText <- compileProgramAndRunGenerated dir "managedScalarDefinedSBVFunctions" program
  sourceText <- readFile (dir </> "managedScalarDefinedSBVFunctions.c")
  mapM_ (\fragment -> assertBool ("Expected managed scalar defined-function output to contain " ++ fragment ++ ", received:\n" ++ stdoutText)
                                 (fragment `isInfixOf` stdoutText))
    [ ") =36"
    , "decorated =<sbv4!>"
    ]
  assertBool "Expected private defined-function calls to thread the shared ownership context"
             ("sbv_function_ctx *const sbv_local_parent_function_ctx" `isInfixOf` sourceText
           && "(&sbv_local_function_ctx," `isInfixOf` sourceText)

-- | Private bodies must request the shared floor helper and math linkage even
-- when their entry point contains only a function call or array lookup.
scopedMappedRealFloor :: Assertion
scopedMappedRealFloor = mapM_ check [(library, useLambda, width) | library <- [False, True], useLambda <- [False, True], width <- [8, 64]]
 where check (library, useLambda, width) = withSystemTempDirectory "sbv-scoped-real-floor" $ \dir -> do
         let functionName = "scopedRealFloor"
             floorHalf :: SReal -> SInteger
             floorHalf value = sRealToSIntegerFloor (value / 2)
             program = do
               cgOverwriteFiles True
               cgSRealType CgLongDouble
               cgIntegerSize width
               cgSetDriverValues [-5]
               value <- cgInput "value"
               let result = if useLambda
                               then readArray (lambdaArray floorHalf) value
                               else smtFunction "C long-double floor" floorHalf value
               cgReturn (result .== -3)
         (_, cfg, bundle) <- if library
                               then compileToCLib' functionName [("floorComponent", program)]
                               else compileToC' functionName ((:[]) <$> program)
         renderCgPgmBundle (Just dir) (cfg, bundle)
         outputText <- compileAndRunGenerated dir functionName
         assertBool outputText (") = 1" `isInfixOf` outputText)

-- | Check overflow-safe statement blocks in conditionals, private functions,
-- and closed array lambdas. Every five-bit input is compared against equivalent
-- unweighted predicates, including sums that exceed the entire unsigned range.
scopedPseudoBoolean :: Assertion
scopedPseudoBoolean = mapM_ check [(library, scope) | library <- [False, True], scope <- [0 :: Int, 1, 2]]
 where check (library, scope) = withSystemTempDirectory "sbv-scoped-pseudo-boolean" $ \dir -> do
         let functionName = "scopedPseudoBoolean"
             evaluateBits :: SWord8 -> SBool
             evaluateBits value =
               let bits     = map (sTestBit value) [0, 1, 2]
                   weighted = zip [maxBound, maxBound, maxBound] bits
               in ite (sTestBit value 3)
                      (pbLe weighted maxBound .== pbAtMost bits 1)
                      (pbEq weighted maxBound .== pbExactly bits 1)
                  .&& (pbGe weighted maxBound .== sOr bits)
             evaluateScoped value = case scope of
               0 -> evaluateBits value
               1 -> smtFunction "C scoped pseudo-Boolean" evaluateBits value
               _ -> readArray (lambdaArray evaluateBits) value
             program = do
               cgOverwriteFiles True
               cgIntegerSize 8
               cgSetDriverValues [0..31]
               inputs <- cgInputArr 32 "inputs"
               cgReturn (sAnd (map evaluateScoped inputs))
         (_, cfg, bundle) <- if library
                               then compileToCLib' functionName [("scopedComponent", program)]
                               else compileToC' functionName ((:[]) <$> program)
         renderCgPgmBundle (Just dir) (cfg, bundle)
         outputText <- compileAndRunGenerated dir functionName
         assertBool outputText (") = 1" `isInfixOf` outputText)

-- | Exercise composed 'smtFunction' definitions over exact-element lists and
-- sets, requiring coordinated list, set, and GMP ownership arenas.
collectionDefinedSBVFunctions :: Assertion
collectionDefinedSBVFunctions = withSystemTempDirectory "sbv-collection-defined-functions" $ \dir -> do
  let program = do
        cgOverwriteFiles True
        let addPrefix :: SList Integer -> SList Integer
            addPrefix = smtFunction "C managed list prefix" $ \values -> literal [0] SL.++ values

            finishList :: SList Integer -> SList Integer
            finishList = smtFunction "C managed list finish" $ \values -> addPrefix values SL.++ literal [3]

            addThree :: SSet Integer -> SSet Integer
            addThree = smtFunction "C managed set three" $ SS.insert 3

            finishSet :: SSet Integer -> SSet Integer
            finishSet = smtFunction "C managed set finish" $ \values -> SS.insert 4 (addThree values)

            finishCollections :: SBV ([Integer], RCSet Integer) -> SBV ([Integer], RCSet Integer)
            finishCollections = smtFunction "C managed collection tuple" $ \collections ->
                                  let (values, members) = untuple collections
                                  in tuple (finishList values, finishSet members)

        cgOutput "listResult" (finishList (literal [1, 2]))
        cgReturn (finishCollections (tuple (literal [1, 2], SS.fromList [1, 2])))

  stdoutText <- compileProgramAndRunGenerated dir "collectionDefinedSBVFunctions" program
  mapM_ (\fragment -> assertBool ("Expected collection defined-function output to contain " ++ fragment ++ ", received:\n" ++ stdoutText)
                                 (fragment `isInfixOf` stdoutText))
    [ ") =([0, 1, 2, 3], {1, 2, 3, 4})"
    , "listResult =[0, 1, 2, 3]"
    ]

-- | Exercise persistent array roots passed through composed 'smtFunction'
-- calls and returned inside a tuple containing its eventual lookup key.
persistentArrayDefinedSBVFunctions :: Assertion
persistentArrayDefinedSBVFunctions = withSystemTempDirectory "sbv-persistent-array-defined-functions" $ \dir -> do
  let program = do
        cgOverwriteFiles True
        let storeAt :: SArray Word8 Word32 -> SWord8 -> SWord32 -> SArray Word8 Word32
            storeAt = smtFunction "C managed array store" writeArray

            storeTwice :: SArray Word8 Word32 -> SArray Word8 Word32
            storeTwice = smtFunction "C managed array stores" $ \values ->
                           storeAt (storeAt values 1 11) 2 22

            package :: SArray Word8 Word32 -> SBV (ArrayModel Word8 Word32, Word8)
            package = smtFunction "C managed array package" $ \values -> tuple (storeTwice values, literal 2)

            base = constArray 5 :: SArray Word8 Word32
            (updated, selectedKey) = untuple (package base)

        cgOutput "atOne"    (readArray updated 1)
        cgOutput "fallback" (readArray updated 7)
        cgReturn (readArray updated selectedKey)

  stdoutText <- compileProgramAndRunGenerated dir "persistentArrayDefinedSBVFunctions" program
  mapM_ (\fragment -> assertBool ("Expected persistent-array defined-function output to contain " ++ fragment ++ ", received:\n" ++ stdoutText)
                                 (fragment `isInfixOf` stdoutText))
    [ ") = 0x00000016UL"
    , "atOne = 0x0000000bUL"
    , "fallback = 0x00000005UL"
    ]

-- | Exercise managed and recursive ADTs returned through composed
-- 'smtFunction' calls, including stabilization of recursive stack literals.
ownedADTDefinedSBVFunctions :: Assertion
ownedADTDefinedSBVFunctions = withSystemTempDirectory "sbv-owned-adt-defined-functions" $ \dir -> do
  let program = do
        cgOverwriteFiles True
        cgSetDriverValues [1, 1]
        let extendCollections :: SCodeGenCollections -> SCodeGenCollections
            extendCollections = smtFunction "C managed ADT collections" $ \value ->
              let values                   = getCGCollections_1 value
                  members                  = getCGCollections_2 value
                  nested                   = getCGCollections_3 value
                  (nestedValues, nestedSet) = untuple nested
              in sCGCollections
                   (values SL.++ literal [7])
                   (SS.insert 8 members)
                   (tuple (nestedValues SL.++ literal [9], SS.insert 10 nestedSet))

            wrapTree :: SCodeGenTree -> SCodeGenTree
            wrapTree = smtFunction "C managed ADT wrap" $ \tree -> sCGNode tree (sCGLeaf 99)

            wrapTreeTwice :: SCodeGenTree -> SCodeGenTree
            wrapTreeTwice = smtFunction "C managed ADT wrap twice" $ \tree -> wrapTree (wrapTree tree)

        collections <- cgInput "collectionsInput" :: SBVCodeGen SCodeGenCollections
        tree        <- cgInput "treeInput"        :: SBVCodeGen SCodeGenTree
        cgOutput "collections" (extendCollections collections)
        cgReturn (wrapTreeTwice tree)

  stdoutText <- compileProgramAndRunGenerated dir "ownedADTDefinedSBVFunctions" program
  sourceText <- readFile (dir </> "ownedADTDefinedSBVFunctions.c")
  mapM_ (\fragment -> assertBool ("Expected owned-ADT defined-function output to contain " ++ fragment ++ ", received:\n" ++ stdoutText)
                                 (fragment `isInfixOf` stdoutText))
    [ ") =CGNode(CGNode("
    , "CGLeaf(99)), CGLeaf(99))"
    , "collections =CGCollections([1, 2, 3, 7], {2, 3, 4, 8}, ([3, 4, 5, 9], {4, 5, 6, 10}))"
    ]
  assertBool ("Expected private owned ADT results to use stable arena clones, received:\n"
           ++ unlines (filter ("sbv_function" `isInfixOf`) (lines sourceText)))
             ("sbv_function_result_clone_" `isInfixOf` sourceText)
  assertBool "Expected private owned ADT result storage to be released"
             ("sbv_function_result_ctx_end(&sbv_local_function_result_ctx);" `isInfixOf` sourceText)

-- | An inactive branch must not dereference the null child returned by a
-- mismatched recursive-ADT selector. Exercise Ite, Boolean short-circuiting,
-- and a managed result in acyclic functions, standalone and in a library.
guardedAcyclicDefinedFunctions :: Assertion
guardedAcyclicDefinedFunctions = mapM_ check [(library, sample) | library <- [False, True], sample <- [1, 0]]
 where check (library, sample) = withSystemTempDirectory "sbv-guarded-acyclic-functions" $ \dir -> do
         let functionName = "guardedAcyclicFunctions"
             program = do
               cgOverwriteFiles True
               cgSetDriverValues [sample]
               chooseLeaf <- cgInput "chooseLeaf" :: SBVCodeGen SBool
               let guardedLeft :: SCodeGenTree -> SWord8
                   guardedLeft = smtFunction "C guarded acyclic left" $ \tree ->
                     ite (isCGLeaf tree) (getCGLeaf_1 tree) (getCGLeaf_1 (getCGNode_1 tree))

                   guardedAnd :: SCodeGenTree -> SBool
                   guardedAnd = smtFunction "C guarded acyclic and" $ \tree ->
                     isCGNode tree .&& getCGLeaf_1 (getCGNode_1 tree) .== 7

                   guardedOr :: SCodeGenTree -> SBool
                   guardedOr = smtFunction "C guarded acyclic or" $ \tree ->
                     isCGLeaf tree .|| getCGLeaf_1 (getCGNode_1 tree) .== 7

                   guardedImplies :: SCodeGenTree -> SBool
                   guardedImplies = smtFunction "C guarded acyclic implication" $ \tree ->
                     isCGNode tree .=> getCGLeaf_1 (getCGNode_1 tree) .== 7

                   guardedTree :: SCodeGenTree -> SCodeGenTree
                   guardedTree = smtFunction "C guarded acyclic tree" $ \tree ->
                     ite (isCGLeaf tree) (sCGLeaf (getCGLeaf_1 tree)) (sCGLeaf (getCGLeaf_1 (getCGNode_1 tree)))

                   rootTree = ite chooseLeaf (sCGLeaf 7) (sCGNode (sCGLeaf 7) (sCGLeaf 9))
               cgOutput "selectedTree" (guardedTree rootTree)
               cgReturn $ sAnd [guardedLeft rootTree .== 7, guardedAnd rootTree .== sNot chooseLeaf, guardedOr rootTree, guardedImplies rootTree]
         (_, cfg, bundle) <- if library
                               then compileToCLib' functionName [("guardedComponent", program)]
                               else compileToC' functionName ((:[]) <$> program)
         renderCgPgmBundle (Just dir) (cfg, bundle)
         outputText <- compileAndRunGenerated dir functionName
         assertBool outputText (") = 1" `isInfixOf` outputText && "selectedTree =CGLeaf(7)" `isInfixOf` outputText)

-- | Demand-driven evaluation must protect partial selectors both in public
-- entry points and in retained array callbacks, including owned branch results.
guardedProgramEvaluation :: Bool -> Assertion
guardedProgramEvaluation useLambda = mapM_ check [(library, sample) | library <- [False, True], sample <- [1, 0]]
 where check (library, sample) = withSystemTempDirectory "sbv-guarded-evaluation" $ \dir -> do
         let functionName = "guardedEvaluation"
             evaluateTree :: SBool -> SBV (CodeGenTree, Bool)
             evaluateTree chooseLeaf =
               let rootTree = ite chooseLeaf (sCGLeaf 7) (sCGNode (sCGLeaf 7) (sCGLeaf 9))
                   child    = getCGLeaf_1 (getCGNode_1 rootTree)
                   selected = ite (isCGLeaf rootTree) (sCGLeaf (getCGLeaf_1 rootTree)) (sCGLeaf child)
                   valid    = sAnd [ (isCGNode rootTree .&& child .== 7) .== sNot chooseLeaf
                                   , isCGLeaf rootTree .|| child .== 7
                                   , isCGNode rootTree .=> child .== 7
                                   ]
               in tuple (selected, valid)
             program = do
               cgOverwriteFiles True
               cgSetDriverValues [sample]
               chooseLeaf <- cgInput "chooseLeaf" :: SBVCodeGen SBool
               let (selected, valid) = untuple $ if useLambda
                                                  then readArray (lambdaArray evaluateTree) chooseLeaf
                                                  else evaluateTree chooseLeaf
               cgOutput "selectedTree" selected
               cgReturn valid
         (_, cfg, bundle) <- if library
                               then compileToCLib' functionName [("guardedComponent", program)]
                               else compileToC' functionName ((:[]) <$> program)
         renderCgPgmBundle (Just dir) (cfg, bundle)
         outputText <- compileAndRunGenerated dir functionName
         assertBool outputText (") = 1" `isInfixOf` outputText && "selectedTree =CGLeaf(7)" `isInfixOf` outputText)

-- | Preconditions must run before dependent outputs, and must not disappear
-- when an entry point has no outputs. A rejected leaf must report the named
-- constraint instead of crashing in the node-only output selector.
guardedRuntimeChecks :: Assertion
guardedRuntimeChecks = mapM_ check [(library, noResult, sample) | library <- [False, True], noResult <- [False, True], sample <- [0, 1]]
 where check (library, noResult, sample) = withSystemTempDirectory "sbv-guarded-checks" $ \dir -> do
         let functionName = "guardedChecks"
             program = do
               cgOverwriteFiles True
               cgSetDriverValues [sample]
               chooseLeaf <- cgInput "chooseLeaf" :: SBVCodeGen SBool
               let rootTree = ite chooseLeaf (sCGLeaf 7) (sCGNode (sCGLeaf 7) (sCGLeaf 9))
               namedConstraint "node required" (isCGNode rootTree)
               unless noResult $ cgReturn (getCGLeaf_1 (getCGNode_1 rootTree))
         (_, cfg, bundle) <- if library
                               then compileToCLib' functionName [("guardedComponent", program)]
                               else compileToC' functionName ((:[]) <$> program)
         renderCgPgmBundle (Just dir) (cfg, bundle)
         makeOptions <- generatedMakeOptions dir
         (makeExit, _, makeError) <- readProcessWithExitCode "make" (["-C", dir] ++ makeOptions) ""
         assertEqual makeError ExitSuccess makeExit
         (runExit, _, runError) <- readProcessWithExitCode (dir </> functionName ++ "_driver") [] ""
         if sample == 0
            then assertEqual runError ExitSuccess runExit
            else do assertBool "Expected a rejected input" (runExit /= ExitSuccess)
                    assertBool runError ("CONSTRAINT FAILED: node required" `isInfixOf` runError)

-- | A shared partial dependency must stay below its guard without being
-- copied exponentially into subsequent conditionals. The generated DAG has
-- only a few dozen nodes even though its expanded expression tree is large.
guardedEvaluationSharing :: Assertion
guardedEvaluationSharing = withSystemTempDirectory "sbv-guarded-sharing" $ \dir -> do
  let program = do
        cgOverwriteFiles True
        cgSetDriverValues [0]
        flags <- cgInput "flags" :: SBVCodeGen SWord32
        let rootTree = ite (sTestBit flags 31) (sCGLeaf 7) (sCGNode (sCGLeaf 7) (sCGLeaf 9))
            initial  = ite (isCGLeaf rootTree) (getCGLeaf_1 rootTree) (getCGLeaf_1 (getCGNode_1 rootTree))
            result   = foldl (\previous bitIndex -> ite (sTestBit flags bitIndex) (previous + 1) (previous + 2)) initial [0 .. 17]
        cgReturn result
  (_, cfg, bundle) <- compileToC' "guardedSharing" program
  assertBool "Guarded evaluation expanded a shared DAG exponentially" (length (show bundle) < 100000)
  renderCgPgmBundle (Just dir) (cfg, bundle)
  outputText <- compileAndRunGenerated dir "guardedSharing"
  assertBool outputText (") = 43" `isInfixOf` outputText)

-- | Finite selection demands only the chosen entry or the out-of-range
-- default. Exercise dynamic owned entries and constant-table defaults at all
-- three lowering sites, with both standalone and library entry points.
guardedTableEvaluation :: Assertion
guardedTableEvaluation = mapM_ check [ (library, scope, checked, sample)
                                   | library <- [False, True]
                                   , scope   <- [0 :: Int, 1, 2]
                                   , checked <- [False, True]
                                   , sample  <- if checked then [0, 1, 2] else [0, 1]
                                   ]
 where check (library, scope, checked, sample) = withSystemTempDirectory "sbv-guarded-tables" $ \dir -> do
         let functionName = "guardedTables"
             evaluateTable :: SWord8 -> SBV (CodeGenTree, Word8)
             evaluateTable index =
               let rootTree = ite (index .== 0) (sCGLeaf 7) (sCGNode (sCGLeaf 7) (sCGLeaf 9))
                   child    = getCGLeaf_1 (getCGNode_1 rootTree)
                   selected = select [sCGLeaf (getCGLeaf_1 rootTree), sCGLeaf child] (sCGLeaf (child + 1)) index
                   constant = select [7, 9] (child + 1) index
               in tuple (selected, constant)
             program = do
               cgOverwriteFiles True
               cgPerformRTCs checked
               cgSetDriverValues [sample]
               index <- cgInput "index" :: SBVCodeGen SWord8
               let result = case scope of
                     0 -> evaluateTable index
                     1 -> smtFunction "C guarded table function" evaluateTable index
                     _ -> readArray (lambdaArray evaluateTable) index
                   (selected, constant) = untuple result
                   expected = ite (index .< 2) 7 8
               cgOutput "selectedTree" selected
               cgReturn (getCGLeaf_1 selected .== expected .&& constant .== ite (index .== 1) 9 expected)
         (_, cfg, bundle) <- if library
                               then compileToCLib' functionName [("guardedComponent", program)]
                               else compileToC' functionName ((:[]) <$> program)
         renderCgPgmBundle (Just dir) (cfg, bundle)
         outputText <- compileAndRunGenerated dir functionName
         assertBool outputText (") = 1" `isInfixOf` outputText)

-- | Check the original index before machine-index narrowing. Large exact,
-- signed-wide, and unsigned-wide indices must select the default, not alias
-- slot zero; unselected partial entries remain protected in all three cases.
guardedTableIndices :: Assertion
guardedTableIndices = mapM_ check [-1, 0, 1, 2, 2 ^ (80 :: Int)]
 where check sample = withSystemTempDirectory "sbv-guarded-table-indices" $ \dir -> do
         let program = do
               cgOverwriteFiles True
               cgPerformRTCs True
               cgSetDriverValues [sample]
               index <- cgInput "index" :: SBVCodeGen SInteger
               let rootTree = ite (index .== 0) (sCGLeaf 7) (sCGNode (sCGLeaf 7) (sCGLeaf 9))
                   child    = getCGLeaf_1 (getCGNode_1 rootTree)
                   entries  = [sCGLeaf (getCGLeaf_1 rootTree), sCGLeaf child]
                   fallback = sCGLeaf (child + 1)
                   exact    = select entries fallback index
                   signed   = select entries fallback (sFromIntegral index :: SInt 673)
                   unsigned = select entries fallback (sFromIntegral index :: SWord 673)
                   expected = ite (index .>= 0 .&& index .< 2) 7 8
               cgReturn $ sAnd [getCGLeaf_1 selected .== expected | selected <- [exact, signed, unsigned]]
         outputText <- compileProgramAndRunGenerated dir "guardedTableIndices" program
         assertBool outputText (") = 1" `isInfixOf` outputText)

-- | Exercise self-recursion, mutually recursive Boolean short-circuiting, and
-- an owned recursive list result. Each base case must avoid evaluating the
-- recursive branch in the generated C program.
recursiveDefinedSBVFunctions :: Assertion
recursiveDefinedSBVFunctions = withSystemTempDirectory "sbv-recursive-defined-functions" $ \dir -> do
  let program = do
        cgOverwriteFiles True
        cgSetDriverValues [5]
        input <- cgInput "input" :: SBVCodeGen SWord8
        let countdown :: SWord8 -> SWord8
            countdown = smtFunctionNoTermination "C recursive countdown" $ \value ->
                          ite (value .== 0) 0 (1 + countdown (value - 1))

            isEven :: SWord8 -> SBool
            isEven = smtFunctionNoTermination "C mutually recursive even" $ \value ->
                       value .== 0 .|| isOdd (value - 1)

            isOdd :: SWord8 -> SBool
            isOdd = smtFunctionNoTermination "C mutually recursive odd" $ \value ->
                      value ./= 0 .&& isEven (value - 1)

            implicationChain :: SWord8 -> SBool
            implicationChain = smtFunctionNoTermination "C recursive implication" $ \value ->
                                 value ./= 0 .=> implicationChain (value - 1)

            tableCount :: SWord8 -> SWord8
            tableCount = smtFunctionNoTermination "C recursive local table" $ \value ->
                           ite (value .== 0) 0
                               (select [value, value + 1] 3 (ite (value .== 1) 1 0 :: SWord8) + tableCount (value - 1))

            countdownList :: SWord8 -> SList Word8
            countdownList = smtFunctionNoTermination "C recursive list" $ \value ->
                              ite (value .== 0)
                                  (literal [] :: SList Word8)
                                  (value SL..: countdownList (value - 1))

            factorial :: SInteger -> SInteger
            factorial = smtFunctionNoTermination "C recursive exact factorial" $ \value ->
                          ite (value .<= 1) 1 (value * factorial (value - 1))

            mcCarthy91 :: SInteger -> SInteger
            mcCarthy91 = smtFunctionNoTermination "C nested recursive McCarthy 91" $ \value ->
                           ite (value .> 100) (value - 10) (mcCarthy91 (mcCarthy91 (value + 11)))
        cgOutput "steps"       (countdown input)
        cgOutput "even"        (isEven input)
        cgOutput "odd"         (isOdd input)
        cgOutput "implication" (implicationChain input)
        cgOutput "tableCount"  (tableCount input)
        cgOutput "factorial"   (factorial 5)
        cgOutput "mcCarthy91"  (mcCarthy91 87)
        cgReturn (countdownList input)

  stdoutText <- compileProgramAndRunGenerated dir "recursiveDefinedSBVFunctions" program
  sourceText <- readFile (dir </> "recursiveDefinedSBVFunctions.c")
  mapM_ (\fragment -> assertBool ("Expected recursive defined-function output to contain " ++ fragment ++ ", received:\n" ++ stdoutText)
                                 (fragment `isInfixOf` stdoutText))
    [ ") =[5, 4, 3, 2, 1]"
    , "steps = 5"
    , "even = 0"
    , "odd = 1"
    , "implication = 1"
    , "tableCount = 16"
    , "factorial =120"
    , "mcCarthy91 =91"
    ]
  assertBool ("Expected recursive calls to remain inside generated control flow, received:\n" ++ sourceText)
             ("if(" `isInfixOf` sourceText
           && length (filter ("/* Uninterpreted function */ sbv_function_" `isInfixOf`) (lines sourceText)) >= 4)

-- | Exercise recursive private functions in independent translation units of
-- a generated static library.
recursiveDefinedSBVFunctionLibrary :: Assertion
recursiveDefinedSBVFunctionLibrary = withSystemTempDirectory "sbv-recursive-defined-function-library" $ \dir -> do
  let component :: Word16 -> SBVCodeGen ()
      component offset = do
        cgOverwriteFiles True
        let sumTo :: SWord8 -> SWord16
            sumTo = smtFunctionNoTermination "C library recursive sum" $ \value ->
                      ite (value .== 0) 0 (sFromIntegral value + sumTo (value - 1))
        cgReturn (literal offset + sumTo 4)

  (_, cfg, bundle) <- compileToCLib' "recursiveDefinedSBVFunctionLibrary"
    [ ("firstRecursive",  component 10)
    , ("secondRecursive", component 20)
    ]
  renderCgPgmBundle (Just dir) (cfg, bundle)
  stdoutText <- compileAndRunGenerated dir "recursiveDefinedSBVFunctionLibrary"
  mapM_ (\fragment -> assertBool ("Expected recursive library output to contain " ++ fragment ++ ", received:\n" ++ stdoutText)
                                 (fragment `isInfixOf` stdoutText))
    [ "firstRecursive() = 0x0014U"
    , "secondRecursive() = 0x001eU"
    ]

-- | Construct and update persistent arrays recursively, then use the returned
-- arrays after their defining C stack frames have unwound.
recursivePersistentArrayFunctions :: Assertion
recursivePersistentArrayFunctions = withSystemTempDirectory "sbv-recursive-persistent-array-functions" $ \dir -> do
  let program = do
        cgOverwriteFiles True
        cgSetDriverValues [3]
        input <- cgInput "input" :: SBVCodeGen SWord8
        let build :: SWord8 -> SArray Word8 Word8
            build = smtFunctionNoTermination "C recursive array build" $ \value ->
                      ite (value .== 0)
                          (constArray 7)
                          (writeArray (build (value - 1)) value (value + 10))

            fill :: SWord8 -> SArray Word8 Word8 -> SArray Word8 Word8
            fill = smtFunctionNoTermination "C recursive array fill" $ \value array ->
                     ite (value .== 0)
                         array
                         (fill (value - 1) (writeArray array value (value + 20)))

            built  = build input
            filled = fill input built

        cgOutput "builtAtOne"   (readArray built 1)
        cgOutput "builtAtInput" (readArray built input)
        cgOutput "filledAtOne"  (readArray filled 1)
        cgOutput "fallback"     (readArray filled 9)
        cgReturn filled

  stdoutText <- compileProgramAndRunGenerated dir "recursivePersistentArrayFunctions" program
  sourceText <- readFile (dir </> "recursivePersistentArrayFunctions.c")
  mapM_ (\fragment -> assertBool ("Expected recursive persistent-array output to contain " ++ fragment ++ ", received:\n" ++ stdoutText)
                                 (fragment `isInfixOf` stdoutText))
    [ ")[0] =7"
    , "builtAtOne = 11"
    , "builtAtInput = 13"
    , "filledAtOne = 21"
    , "fallback = 7"
    ]
  assertBool ("Expected recursive array nodes to be declared outside guarded branches, received:\n" ++ sourceText)
             ("sbv_array_node_2_u8_2_u8 sbv_local_array_s" `isInfixOf` sourceText
           && "sbv_array_stored_export_2_u8_2_u8(&sbv_local_array_ctx" `isInfixOf` sourceText)

-- | Construct, traverse, and return a recursive ADT through private recursive
-- functions after every child-producing C stack frame has unwound.
recursiveADTDefinedSBVFunctions :: Assertion
recursiveADTDefinedSBVFunctions = withSystemTempDirectory "sbv-recursive-adt-defined-functions" $ \dir -> do
  let program = do
        cgOverwriteFiles True
        cgSetDriverValues [3]
        input <- cgInput "input" :: SBVCodeGen SWord8
        let build :: SWord8 -> SCodeGenTree
            build = smtFunctionNoTermination "C recursive ADT build" $ \value ->
                      ite (value .== 0)
                          (literal (CGNode (CGLeaf 4) (CGLeaf 5)))
                          (sCGNode (build (value - 1)) (sCGLeaf value))

            leftmost :: SCodeGenTree -> SWord8
            leftmost = smtFunctionNoTermination "C recursive ADT leftmost" $ \tree ->
                         ite (isCGLeaf tree)
                             (getCGLeaf_1 tree)
                             (leftmost (getCGNode_1 tree))

            leafSum :: SCodeGenTree -> SWord16
            leafSum = smtFunctionNoTermination "C recursive ADT leaf sum" $ \tree ->
                        ite (isCGLeaf tree)
                            (sFromIntegral (getCGLeaf_1 tree))
                            (leafSum (getCGNode_1 tree) + leafSum (getCGNode_2 tree))

            buildEven :: SWord8 -> SCodeGenEven
            buildEven = smtFunctionNoTermination "C mutually recursive ADT even" $ \value ->
                          ite (value .== 0)
                              (sCGEvenEnd 0)
                              (sCGEvenStep (buildOdd (value - 1)))

            buildOdd :: SWord8 -> SCodeGenOdd
            buildOdd = smtFunctionNoTermination "C mutually recursive ADT odd" $ sCGOddStep . buildEven

            result = build input

        cgOutput "leftmost" (leftmost result)
        cgOutput "leafSum"  (leafSum result)
        cgOutput "mutual"   (buildEven input)
        cgReturn result

  stdoutText <- compileProgramAndRunGenerated dir "recursiveADTDefinedSBVFunctions" program
  sourceText <- readFile (dir </> "recursiveADTDefinedSBVFunctions.c")
  mapM_ (\fragment -> assertBool ("Expected recursive-ADT function output to contain " ++ fragment ++ ", received:\n" ++ stdoutText)
                                 (fragment `isInfixOf` stdoutText))
    [ ") =CGNode(CGNode(CGNode(CGNode(CGLeaf(4), CGLeaf(5)), CGLeaf(1)), CGLeaf(2)), CGLeaf(3))"
    , "leftmost = 4"
    , "leafSum = 0x000fU"
    , "mutual =CGEvenStep(CGOddStep(CGEvenStep(CGOddStep(CGEvenStep(CGOddStep(CGEvenEnd(0)))))))"
    ]
  assertBool ("Expected recursive ADT fields to use function-scoped backing values, received:\n" ++ sourceText)
             ("SBVADT_CodeGenTree sbv_local_adt_recursive_" `isInfixOf` sourceText
           && "sbv_function_result_clone_adt_" `isInfixOf` sourceText
           && any (\line -> "const SBVADT_CodeGenTree l1_s" `isInfixOf` line
                          && "= (SBVADT_CodeGenTree)" `isInfixOf` line)
                  (lines sourceText))

-- | Exercise private recursive ADT builders in independent translation units
-- of a generated static library.
recursiveADTDefinedSBVFunctionLibrary :: Assertion
recursiveADTDefinedSBVFunctionLibrary = withSystemTempDirectory "sbv-recursive-adt-defined-function-library" $ \dir -> do
  let component :: Word8 -> SBVCodeGen ()
      component offset = do
        cgOverwriteFiles True
        let build :: SWord8 -> SCodeGenTree
            build = smtFunctionNoTermination "C library recursive ADT build" $ \value ->
                      ite (value .== 0)
                          (sCGLeaf (literal offset))
                          (sCGNode (build (value - 1)) (sCGLeaf (literal offset + value)))
        cgReturn (build 2)

  (_, cfg, bundle) <- compileToCLib' "recursiveADTDefinedSBVFunctionLibrary"
    [ ("firstRecursiveADT", component 10)
    , ("secondRecursiveADT", component 20)
    ]
  renderCgPgmBundle (Just dir) (cfg, bundle)
  stdoutText <- compileAndRunGenerated dir "recursiveADTDefinedSBVFunctionLibrary"
  mapM_ (\fragment -> assertBool ("Expected recursive-ADT library output to contain " ++ fragment ++ ", received:\n" ++ stdoutText)
                                 (fragment `isInfixOf` stdoutText))
    [ "firstRecursiveADT() =CGNode(CGNode(CGLeaf(10), CGLeaf(11)), CGLeaf(12))"
    , "secondRecursiveADT() =CGNode(CGNode(CGLeaf(20), CGLeaf(21)), CGLeaf(22))"
    ]

-- | Compile SBV's firstified higher-order list operations, including an
-- explicit symbolic closure environment, into ordinary private C functions.
higherOrderListFunctions :: Assertion
higherOrderListFunctions = withSystemTempDirectory "sbv-higher-order-list-functions" $ \dir -> do
  let program = do
        cgOverwriteFiles True
        cgSetDriverValues [10, 5]
        values <- cgInput "values" :: SBVCodeGen (SList Word8)
        offset <- cgInput "offset" :: SBVCodeGen SWord8
        let mapped   = SL.map (+ (1 :: SWord8)) values
            filtered = SL.filter (\value -> value .> (11 :: SWord8)) mapped
            folded   = SL.foldl ((+) @SWord8) 0 mapped
            paired   = SL.zipWith ((+) @SWord8) values mapped

            closureShift :: Closure SWord8 (SWord8 -> SWord8)
            closureShift = Closure { closureEnv = offset
                                   , closureFun = (+)
                                   }

            shifted = SL.map closureShift values

        cgOutput "mapped"   mapped
        cgOutput "filtered" filtered
        cgOutput "folded"   folded
        cgOutput "paired"   paired
        cgReturn shifted

  stdoutText <- compileProgramAndRunGenerated dir "higherOrderListFunctions" program
  sourceText <- readFile (dir </> "higherOrderListFunctions.c")
  mapM_ (\fragment -> assertBool ("Expected firstified higher-order output to contain " ++ fragment ++ ", received:\n" ++ stdoutText)
                                 (fragment `isInfixOf` stdoutText))
    [ ") =[15, 16, 17]"
    , "mapped =[11, 12, 13]"
    , "filtered =[12, 13]"
    , "folded = 36"
    , "paired =[21, 23, 25]"
    ]
  assertBool ("Expected higher-order instances to become private first-order C functions, received:\n" ++ sourceText)
             ("/* Uninterpreted function */ sbv_function_" `isInfixOf` sourceText)

-- | Exercise independently specialized higher-order functions in separate
-- translation units of a generated static library.
higherOrderListFunctionLibrary :: Assertion
higherOrderListFunctionLibrary = withSystemTempDirectory "sbv-higher-order-list-function-library" $ \dir -> do
  let component :: Word8 -> SBVCodeGen ()
      component offset = do
        cgOverwriteFiles True
        cgSetDriverValues [10]
        values <- cgInput "values" :: SBVCodeGen (SList Word8)
        cgReturn (SL.map (\(value :: SWord8) -> value + literal offset) values)

  (_, cfg, bundle) <- compileToCLib' "higherOrderListFunctionLibrary"
    [ ("addTen", component 10)
    , ("addTwenty", component 20)
    ]
  renderCgPgmBundle (Just dir) (cfg, bundle)
  stdoutText <- compileAndRunGenerated dir "higherOrderListFunctionLibrary"
  mapM_ (\fragment -> assertBool ("Expected higher-order library output to contain " ++ fragment ++ ", received:\n" ++ stdoutText)
                                 (fragment `isInfixOf` stdoutText))
    [ "addTen(((SBVList_u8) {(const SWord8[]) {10, 11, 12}, 3})) =[20, 21, 22]"
    , "addTwenty(((SBVList_u8) {(const SWord8[]) {10, 11, 12}, 3})) =[30, 31, 32]"
    ]

-- | Exercise unnamed and named hard constraints as generated-C precondition
-- checks, including a Boolean input used only by a constraint and an escaped
-- UTF-8 diagnostic name.
explicitHardConstraints :: Assertion
explicitHardConstraints = withSystemTempDirectory "sbv-explicit-hard-constraints" $ \dir -> do
  let constraintName = "value is \"seven\" (100%) \955"
      program driverValues = do
        cgOverwriteFiles True
        cgSetDriverValues driverValues
        enabled <- cgInput "enabled" :: SBVCodeGen SBool
        value   <- cgInput "value"   :: SBVCodeGen SWord8
        constrain enabled
        namedConstraint constraintName (value .== 7)
        cgReturn (value + 1)

      validDir   = dir </> "valid"
      invalidDir = dir </> "invalid"

  validOutput <- compileProgramAndRunGenerated validDir "explicitHardConstraints" (program [1, 7])
  assertBool ("Expected constrained output to contain 8, received:\n" ++ validOutput)
             (") = 8" `isInfixOf` validOutput)

  (_, invalidCfg, invalidBundle) <- compileToC' "explicitHardConstraints" (program [1, 6])
  renderCgPgmBundle (Just invalidDir) (invalidCfg, invalidBundle)
  makeOptions <- generatedMakeOptions invalidDir
  (makeExit, _, makeError) <- readProcessWithExitCode "make" (["-C", invalidDir] ++ makeOptions) ""
  assertEqual makeError ExitSuccess makeExit
  (runExit, _, runError) <- readProcessWithExitCode (invalidDir </> "explicitHardConstraints_driver") [] ""
  assertBool "Expected a violated hard constraint to terminate the generated driver"
             (case runExit of ExitFailure _ -> True; ExitSuccess -> False)
  assertBool ("Expected the named constraint diagnostic, received:\n" ++ runError)
             (("CONSTRAINT FAILED: " ++ constraintName) `isInfixOf` runError)

-- | Check that constraint forms requiring solver optimization or SMT-only
-- attributes receive focused diagnostics instead of being silently weakened.
unsupportedConstraintFeatures :: Assertion
unsupportedConstraintFeatures = do
  softResult <- try (do
    (_, _, bundle) <- compileToC' "softConstraint" $ do
      value <- cgInput "value" :: SBVCodeGen SBool
      softConstrain value
      cgReturn value
    evaluate (length (show bundle))) :: IO (Either ErrorCall Int)
  case softResult of
    Left exception -> assertBool ("Expected a soft-constraint diagnostic, received:\n" ++ displayException exception)
                                 ("Soft constraints" `isInfixOf` displayException exception)
    Right _        -> assertBool "Expected C generation to reject a soft constraint" False

  attributeResult <- try (do
    (_, _, bundle) <- compileToC' "attributedConstraint" $ do
      value <- cgInput "value" :: SBVCodeGen SBool
      constrainWithAttribute [(":weight", "2")] value
      cgReturn value
    evaluate (length (show bundle))) :: IO (Either ErrorCall Int)
  case attributeResult of
    Left exception -> assertBool ("Expected a constraint-attribute diagnostic, received:\n" ++ displayException exception)
                                 ("Constraint attributes: :weight" `isInfixOf` displayException exception)
    Right _        -> assertBool "Expected C generation to reject an SMT-only constraint attribute" False

-- | Exercise a sole 'cgReturnArr' group through the generated output-parameter
-- ABI while preserving the return elements' declaration order.
nonAtomicReturnGroup :: Assertion
nonAtomicReturnGroup = withSystemTempDirectory "sbv-non-atomic-return-group" $ \dir -> do
  let program = do
        cgOverwriteFiles True
        cgSetDriverValues [4]
        input <- cgInput "input" :: SBVCodeGen SWord16
        cgReturnArr [input + 1, input + 2, input + 3]

  stdoutText <- compileProgramAndRunGenerated dir "nonAtomicReturnGroup" program
  headerText <- readFile (dir </> "nonAtomicReturnGroup.h")
  mapM_ (\fragment -> assertBool ("Expected non-atomic return output to contain " ++ fragment ++ ", received:\n" ++ stdoutText)
                                 (fragment `isInfixOf` stdoutText))
    [ "result_0[0] = 0x0005U"
    , "result_0[1] = 0x0006U"
    , "result_0[2] = 0x0007U"
    ]
  assertBool "Expected a sole array return group to use a void output-parameter ABI"
             ("void nonAtomicReturnGroup(" `isInfixOf` headerText
           && "SWord16 *result_0" `isInfixOf` headerText)

-- | Exercise multiple ordered return groups containing a scalar, an owned
-- symbolic list, and a fixed-size C array.
multipleReturnGroups :: Assertion
multipleReturnGroups = withSystemTempDirectory "sbv-multiple-return-groups" $ \dir -> do
  let program = do
        cgOverwriteFiles True
        cgSetDriverValues [4]
        input <- cgInput "input" :: SBVCodeGen SWord16
        cgReturn (input + 1)
        cgReturn (literal ([10, 11] :: [Word16]))
        cgReturn (sFromIntegral input + 20 :: SInteger)
        cgReturnArr [input + 2, input + 3]

  stdoutText <- compileProgramAndRunGenerated dir "multipleReturnGroups" program
  headerText <- readFile (dir </> "multipleReturnGroups.h")
  mapM_ (\fragment -> assertBool ("Expected multiple-return output to contain " ++ fragment ++ ", received:\n" ++ stdoutText)
                                 (fragment `isInfixOf` stdoutText))
    [ "result_0 = 0x0005U"
    , "result_1 =[0x000aU, 0x000bU]"
    , "result_2 =24"
    , "result_3[0] = 0x0006U"
    , "result_3[1] = 0x0007U"
    ]
  assertBool "Expected multiple return groups to use ordered output parameters"
             ("void multipleReturnGroups(" `isInfixOf` headerText
           && "SWord16 *result_0" `isInfixOf` headerText
           && "SWord16 *result_3" `isInfixOf` headerText)

-- | Fixed-size symbolic-array inputs use public callback descriptors rather
-- than private array nodes. Distinct seeds must initialize each callback, and
-- managed defaults and returned arrays have independent ownership.
groupedArrayInputs :: Bool -> Assertion
groupedArrayInputs library = withSystemTempDirectory "sbv-grouped-array-inputs" $ \dir -> do
  let program = do
        cgOverwriteFiles True
        cgSetDriverValues [3, 7, 11, 15]
        native <- cgInputArr 2 "native" :: SBVCodeGen [SArray Word8 Word16]
        exact  <- cgInputArr 2 "exact"  :: SBVCodeGen [SArray Word8 [Integer]]
        cgOutputArr "nativeValues" [readArray value 0 | value <- native]
        cgOutputArr "exactHeads" [SL.head (readArray value 0) | value <- exact]
        cgReturnArr native
        cgReturnArr exact
  outputText <- runGroupedInputProgram dir "groupedArrayInputs" library program
  headerText <- readFile (dir </> "groupedArrayInputs.h")
  mapM_ (\fragment -> assertBool outputText (fragment `isInfixOf` outputText))
    [ "nativeValues[0] = 0x0003U"
    , "nativeValues[1] = 0x0007U"
    , "exactHeads[0] = 11"
    , "exactHeads[1] = 15"
    , "result_0[1][0] =0x0007U"
    , "result_1[1][0] =[15, 16, 17]"
    ]
  assertBool "Expected public callback descriptors for grouped array inputs"
             ("const SBVArrayInput_2_u8_3_u16 *native" `isInfixOf` headerText)

-- | A hand-written caller can pass callback groups without private runtime
-- nodes. Returned groups retain each context independently across later calls.
groupedArrayInputOwnership :: Assertion
groupedArrayInputOwnership = withSystemTempDirectory "sbv-grouped-array-ownership" $ \dir -> do
  _ <- compileToCLib (Just dir) "arrayGroupLibrary"
    [("copyArrayGroup", do
        cgOverwriteFiles True
        cgGenerateDriver False
        values <- cgInputArr 2 "values" :: SBVCodeGen [SArray Word8 Word16]
        cgReturnArr values)]
  compileAndRunCaller dir "arrayGroupLibrary" $ unlines
    [ "#include \"arrayGroupLibrary.h\""
    , "#include <assert.h>"
    , "static unsigned live_contexts;"
    , "static SWord16 lookup(const void *context, SWord8 key)"
    , "{ return *(const SWord16 *) context + key; }"
    , "static const void *retain(const void *context)"
    , "{ SWord16 *copy = malloc(sizeof(*copy)); assert(copy != NULL); *copy = *(const SWord16 *) context; ++live_contexts; return copy; }"
    , "static void release(const void *context)"
    , "{ --live_contexts; free((void *) context); }"
    , "int main(void)"
    , "{"
    , "  for (unsigned i = 0; i < 32; ++i) {"
    , "    SWord16 data[] = {7, 23};"
    , "    const SBVArrayInput_2_u8_3_u16 inputs[] = {{lookup, &data[0], retain, release}, {lookup, &data[1], retain, release}};"
    , "    SBVArrayOutput_2_u8_3_u16 first[2], second[2];"
    , "    copyArrayGroup(inputs, first);"
    , "    data[0] = 99; data[1] = 101;"
    , "    const SBVArrayInput_2_u8_3_u16 borrowed[] = {sbv_array_output_as_input_2_u8_3_u16(first[1]), sbv_array_output_as_input_2_u8_3_u16(first[0])};"
    , "    copyArrayGroup(borrowed, second);"
    , "    for (unsigned j = 0; j < 2; ++j) sbv_array_output_release_2_u8_3_u16(&first[j]);"
    , "    assert(live_contexts == 2);"
    , "    assert(sbv_array_output_read_2_u8_3_u16(second[0], 1) == 24);"
    , "    assert(sbv_array_output_read_2_u8_3_u16(second[1], 1) == 8);"
    , "    for (unsigned j = 0; j < 2; ++j) sbv_array_output_release_2_u8_3_u16(&second[j]);"
    , "    assert(live_contexts == 0);"
    , "  }"
    , "  return 0;"
    , "}"
    ]

-- | Managed input groups need per-element initialization, including nested
-- exact values and retained arrays, followed by exactly one owner cleanup.
groupedManagedInputs :: Bool -> Assertion
groupedManagedInputs library = withSystemTempDirectory "sbv-grouped-managed-inputs" $ \dir -> do
  let program = do
        cgOverwriteFiles True
        cgSetDriverValues [3, 7, 11, 15, 21, 25, 1, 5, 31, 35]
        lists  <- cgInputArr 2 "lists"  :: SBVCodeGen [SList Integer]
        sets   <- cgInputArr 2 "sets"   :: SBVCodeGen [SSet Rational]
        pairs  <- cgInputArr 2 "pairs"  :: SBVCodeGen [SBV (Integer, [Integer])]
        adts   <- cgInputArr 2 "adts"   :: SBVCodeGen [SCodeGenCollections]
        arrays <- cgInputArr 2 "arrays" :: SBVCodeGen [SList (ArrayModel Word8 Word16)]
        cgOutputArr "listHeads" (map SL.head lists)
        cgOutputArr "pairIntegers" (map (fst . untuple) pairs)
        cgOutputArr "arrayHeads" [readArray (SL.head value) 0 | value <- arrays]
        cgReturnArr lists
        cgReturnArr sets
        cgReturnArr pairs
        cgReturnArr adts
        cgReturnArr arrays
  outputText <- runGroupedInputProgram dir "groupedManagedInputs" library program
  mapM_ (\fragment -> assertBool outputText (fragment `isInfixOf` outputText))
    [ "listHeads[0] = 3"
    , "listHeads[1] = 7"
    , "pairIntegers[0] = 21"
    , "pairIntegers[1] = 25"
    , "arrayHeads[0] = 0x001fU"
    , "arrayHeads[1] = 0x0023U"
    , "result_0[1] = [7, 8, 9]"
    ]

-- | Exercise the same grouped-input program through standalone generation
-- and two translation units sharing one library header and combined driver.
runGroupedInputProgram :: FilePath -> String -> Bool -> SBVCodeGen () -> IO String
runGroupedInputProgram dir programName library program
  | library = do
      (_, cfg, bundle) <- compileToCLib' programName [(programName ++ "First", program), (programName ++ "Second", program)]
      renderCgPgmBundle (Just dir) (cfg, bundle)
      compileAndRunGenerated dir programName
  | True = compileProgramAndRunGenerated dir programName program

-- | Exercise deep ownership and element-wise cleanup for non-atomic return
-- groups containing lists, exact integers, and persistent arrays.
managedReturnGroups :: Assertion
managedReturnGroups = withSystemTempDirectory "sbv-managed-return-groups" $ \dir -> do
  let program = do
        cgOverwriteFiles True
        cgSetDriverValues [4]
        input <- cgInput "input" :: SBVCodeGen SWord16
        let baseArray = constArray 5 :: SArray Word8 Word16
        cgReturnArr [ literal ([1, 2] :: [Word16])
                    , literal ([3, 4] :: [Word16])
                    ]
        cgReturnArr [ sFromIntegral input + 30 :: SInteger
                    , sFromIntegral input + 31
                    ]
        cgReturnArr [baseArray, writeArray baseArray 0 9]

  stdoutText <- compileProgramAndRunGenerated dir "managedReturnGroups" program
  headerText <- readFile (dir </> "managedReturnGroups.h")
  sourceText <- readFile (dir </> "managedReturnGroups.c")
  driverText <- readFile (dir </> "managedReturnGroups_driver.c")
  mapM_ (\fragment -> assertBool ("Expected managed return-group output to contain " ++ fragment ++ ", received:\n" ++ stdoutText)
                                 (fragment `isInfixOf` stdoutText))
    [ "result_0[0] = [0x0001U, 0x0002U]"
    , "result_0[1] = [0x0003U, 0x0004U]"
    , "result_1[0] = 34"
    , "result_1[1] = 35"
    , "result_2[0][0] =0x0005U"
    , "result_2[1][0] =0x0009U"
    ]
  assertBool "Expected exact and persistent-array groups to expose mutable output arrays"
             ("mpz_t *result_1" `isInfixOf` headerText
           && "SBVArrayOutput_2_u8_3_u16 *result_2" `isInfixOf` headerText)
  assertBool ("Expected managed group elements to be cloned and released independently, received:\n"
           ++ unlines (filter ("sbv_" `isInfixOf`) (lines (sourceText ++ driverText))))
             ("sbv_output_0[0] = sbv_list_clone_u16" `isInfixOf` sourceText
           && "sbv_list_release_u16(&sbv_driver_output_0[0]);" `isInfixOf` driverText
           && "sbv_array_output_release_2_u8_3_u16(&sbv_driver_output_2[0]);" `isInfixOf` driverText)

-- | Exercise grouped return ABIs across multiple generated library
-- translation units.
groupedReturnLibrary :: Assertion
groupedReturnLibrary = withSystemTempDirectory "sbv-grouped-return-library" $ \dir -> do
  let component increment seed = do
        cgOverwriteFiles True
        cgSetDriverValues [seed]
        input <- cgInput "input" :: SBVCodeGen SWord16
        cgReturnArr [input + literal increment, input + literal increment + 1]
        cgReturn (literal ([increment, increment + 1] :: [Word16]))

  (_, cfg, bundle) <- compileToCLib' "groupedReturnLibrary"
    [ ("firstGroups",  component 1 4)
    , ("secondGroups", component 2 8)
    ]
  renderCgPgmBundle (Just dir) (cfg, bundle)
  stdoutText <- compileAndRunGenerated dir "groupedReturnLibrary"
  headerText <- readFile (dir </> "groupedReturnLibrary.h")
  mapM_ (\fragment -> assertBool ("Expected grouped library output to contain " ++ fragment ++ ", received:\n" ++ stdoutText)
                                 (fragment `isInfixOf` stdoutText))
    [ "result_0[0] = 0x0005U"
    , "result_0[1] = 0x0006U"
    , "result_1 =[0x0001U, 0x0002U]"
    , "result_0[0] = 0x000aU"
    , "result_0[1] = 0x000bU"
    , "result_1 =[0x0002U, 0x0003U]"
    ]
  assertBool "Expected both library components to publish grouped output parameters"
             ("void firstGroups(" `isInfixOf` headerText
           && "void secondGroups(" `isInfixOf` headerText
           && length (filter ("SWord16 *result_0" `isInfixOf`) (lines headerText)) == 2)

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

-- | Exercise structural object equality and deep ownership for array keys and
-- values containing lists, sets, strings, tuples, and concrete ADTs.
managedAggregateArrays :: Assertion
managedAggregateArrays = withSystemTempDirectory "sbv-managed-aggregate-arrays" $ \dir -> do
  let program = do
        cgOverwriteFiles True
        cgSetDriverValues [4, 10, 12]
        source      <- cgInput "source"      :: SBVCodeGen (SArray [Word16] CodeGenNativeCollections)
        key         <- cgInput "key"         :: SBVCodeGen (SList Word16)
        exactSource <- cgInput "exactSource" :: SBVCodeGen (SArray Word8 (String, Integer))
        let storedADT    = sCGNativeCollections
                               (literal ([90, 91] :: [Word16]))
                               (SS.fromList [92, 93])
            updatedADT   = writeArray source key storedADT
            stringKey    = literal "stored" :: SString
            defaultTuple = tuple (literal "default" :: SString, literal ([1, 2] :: [Integer]))
            storedTuple  = tuple (literal "stored-value" :: SString, literal ([7, 8] :: [Integer]))
            tupleArray   = writeArray (constArray defaultTuple :: SArray String (String, [Integer])) stringKey storedTuple
            setKey       = SS.fromList [5, 6] :: SSet Word16
            storedList   = literal ([7, 8] :: [Word16])
            setArray     = writeArray (constArray (literal ([1, 2] :: [Word16])) :: SArray (RCSet Word16) [Word16]) setKey storedList
            enumArray    = writeArray (constArray 3 :: SArray CodeGenEnum Word8) sCGBlue 9
        cgOutput "matchedADT" (readArray updatedADT key .=== storedADT)
        cgOutput "matchedSet" (readArray setArray setKey .=== storedList)
        cgOutput "matchedEnum" (readArray enumArray sCGBlue .== (9 :: SWord8))
        cgOutput "storedADT" (readArray updatedADT key)
        cgOutput "tupleArray" tupleArray
        cgOutput "storedTuple" (readArray tupleArray stringKey)
        cgOutput "setArray" setArray
        cgOutput "enumArray" enumArray
        cgOutput "exactSourceCopy" exactSource
        cgReturn updatedADT

  stdoutText <- compileProgramAndRunGenerated dir "managedAggregateArrays" program
  headerText <- readFile (dir </> "managedAggregateArrays.h")
  sourceText <- readFile (dir </> "managedAggregateArrays.c")
  driverText <- readFile (dir </> "managedAggregateArrays_driver.c")
  mapM_ (\fragment -> assertBool ("Expected managed aggregate-array output to contain " ++ show fragment ++ ", received:\n" ++ stdoutText)
                                (fragment `isInfixOf` stdoutText))
    [ "matchedADT = 1"
    , "matchedSet = 1"
    , "matchedEnum = 1"
    , "storedADT =CGNativeCollections([0x005aU, 0x005bU], {0x005cU, 0x005dU})"
    , "storedTuple =(stored-value, [7, 8])"
    , "tupleArray[0] =(default, [1, 2])"
    , "setArray[0] =[0x0001U, 0x0002U]"
    , "enumArray[0] =3"
    , "exactSourceCopy[0] =(sbv12, 13)"
    ]
  assertBool "Expected exported arrays to own aggregate keys and values"
             ("sbv_list_clone_u16(source->key)" `isInfixOf` sourceText
           && "sbv_adt_owned_clone_SBVADT_CodeGenNativeCollections(source->value)" `isInfixOf` sourceText
           && "sbv_string_clone(source->key)" `isInfixOf` sourceText
           && "sbv_tuple_owned_clone_" `isInfixOf` sourceText
           && "sbv_set_clone_u16(source->key)" `isInfixOf` sourceText
           && "sbv_list_clone_u16(source->value)" `isInfixOf` sourceText
           && "sbv_adt_owned_clone_SBVADT_CodeGenEnum(source->key)" `isInfixOf` sourceText
           && "sbv_adt_owned_release_SBVADT_CodeGenNativeCollections" `isInfixOf` sourceText)
  assertBool "Expected managed callback defaults to use deep retain and release helpers"
             ("sbv_adt_owned_clone_SBVADT_CodeGenNativeCollections" `isInfixOf` headerText
           && "sbv_local_array_retain_" `isInfixOf` driverText
           && "sbv_local_array_release_" `isInfixOf` driverText
           && "sbv_tuple_owned_clone_" `isInfixOf` driverText
           && "sbv_tuple_owned_release_" `isInfixOf` driverText)

-- | Exercise guarded aggregate-array declarations and owned return values
-- shared by multiple generated library translation units.
managedAggregateArrayLibrary :: Assertion
managedAggregateArrayLibrary = withSystemTempDirectory "sbv-managed-aggregate-array-library" $ \dir -> do
  let component :: Integer -> Word16 -> SBVCodeGen ()
      component seed keyValue = do
        cgOverwriteFiles True
        cgSetDriverValues [seed]
        source <- cgInput "source" :: SBVCodeGen (SArray (RCSet Word16) CodeGenNativeCollections)
        let key   = SS.singleton (literal keyValue)
            value = sCGNativeCollections
                      (literal ([keyValue, keyValue + 1] :: [Word16]))
                      (SS.fromList [keyValue + 2, keyValue + 3])
        cgReturn (writeArray source key value)

  (_, cfg, bundle) <- compileToCLib' "managedAggregateArrayLibrary"
    [ ("firstManagedArray",  component 1 20)
    , ("secondManagedArray", component 4 30)
    ]
  renderCgPgmBundle (Just dir) (cfg, bundle)
  stdoutText <- compileAndRunGenerated dir "managedAggregateArrayLibrary"
  headerText <- readFile (dir </> "managedAggregateArrayLibrary.h")
  mapM_ (\fragment -> assertBool ("Expected managed aggregate-array library output to contain " ++ show fragment ++ ", received:\n" ++ stdoutText)
                                (fragment `isInfixOf` stdoutText))
    [ "firstManagedArray(source)[0] =CGNativeCollections([0x0001U, 0x0002U, 0x0003U]"
    , "secondManagedArray(source)[0] =CGNativeCollections([0x0004U, 0x0005U, 0x0006U]"
    ]
  assertBool "Expected one reusable guarded aggregate-array ABI"
             ("SBVArrayOutput_9_set_3_u16_39_adt_SBVADT_x5f_CodeGenNativeCollections" `isInfixOf` headerText
           && "sbv_array_output_release_9_set_3_u16_39_adt_SBVADT_x5f_CodeGenNativeCollections" `isInfixOf` headerText)

-- | Exercise static and runtime-local finite tables containing text, lists,
-- sets, and ADTs with managed collection fields.
managedAggregateTables :: Assertion
managedAggregateTables = withSystemTempDirectory "sbv-managed-aggregate-tables" $ \dir -> do
  let program = do
        cgOverwriteFiles True
        cgSetDriverValues [1, 5]
        selector <- cgInput "selector" :: SBVCodeGen SWord8
        source   <- cgInput "source"   :: SBVCodeGen (SList Word16)
        let staticText :: SString
            staticText  = select [literal "zero", literal "one"] (literal "other") selector
            staticList  = select [literal ([1, 2] :: [Word16]), literal ([3, 4] :: [Word16])]
                                 (literal ([9] :: [Word16])) selector
            dynamicList = select [source, source SL.++ SL.singleton 9]
                                 (literal ([10] :: [Word16])) selector
            staticSet :: SSet Word16
            staticSet   = select [SS.fromList [1, 2], SS.fromList [3, 4]]
                                 (SS.singleton 9) selector
            firstADT    = sCGNativeCollections source (SS.singleton 20)
            secondADT   = sCGNativeCollections (source SL.++ SL.singleton 21) (SS.fromList [22, 23])
            selectedADT = select [firstADT, secondADT] (sCGNativeCollections SL.nil SS.empty) selector
        cgOutput "staticText" staticText
        cgOutput "staticList" staticList
        cgOutput "dynamicList" dynamicList
        cgOutput "staticSet" staticSet
        cgOutput "selectedADT" selectedADT
        cgReturn selectedADT

  stdoutText <- compileProgramAndRunGenerated dir "managedAggregateTables" program
  sourceText <- readFile (dir </> "managedAggregateTables.c")
  mapM_ (\fragment -> assertBool ("Expected managed aggregate-table output to contain " ++ show fragment ++ ", received:\n" ++ stdoutText)
                                (fragment `isInfixOf` stdoutText))
    [ ") =CGNativeCollections([0x0005U, 0x0006U, 0x0007U, 0x0015U], {0x0016U, 0x0017U})"
    , "staticText =one"
    , "staticList =[0x0003U, 0x0004U]"
    , "dynamicList =[0x0005U, 0x0006U, 0x0007U, 0x0009U]"
    , "staticSet ={0x0003U, 0x0004U}"
    , "selectedADT =CGNativeCollections([0x0005U, 0x0006U, 0x0007U, 0x0015U], {0x0016U, 0x0017U})"
    ]
  assertBool "Expected ready aggregates to use automatic tables and dynamic entries to remain guarded"
             (    "const SString table" `isInfixOf` sourceText
              && "const SBVList_u16 table" `isInfixOf` sourceText
              && "const SBVSet_u16 table" `isInfixOf` sourceText
              && "switch((uint64_t)" `isInfixOf` sourceText
              && not ("static const SString table" `isInfixOf` sourceText)
              && not ("static const SBVList_u16 table" `isInfixOf` sourceText)
              && not ("static const SBVSet_u16 table" `isInfixOf` sourceText)
              && not ("static const SBVADT_CodeGenNativeCollections table" `isInfixOf` sourceText)
             )

-- | Exercise finite tables whose cells and default are retained arrays, both
-- when entries are already demanded by earlier outputs and when the lookup
-- must initialize only the selected entry.
arrayValuedTables :: Bool -> Assertion
arrayValuedTables readyEntries = withSystemTempDirectory "sbv-array-valued-tables" $ \dir -> do
  let program = do
        cgOverwriteFiles True
        cgPerformRTCs True
        cgSetDriverValues [1, 3]
        selector <- cgInput "selector" :: SBVCodeGen SWord8
        key      <- cgInput "key"      :: SBVCodeGen SWord8
        let first     = writeArray (constArray 10) key 11 :: SArray Word8 Word32
            second    = writeArray (constArray 20) key 21 :: SArray Word8 Word32
            fallback  = constArray 30                  :: SArray Word8 Word32
            selected  = select [first, second] fallback selector
            defaulted = select [first, second] fallback (selector + 2)
        when readyEntries $ do cgOutput "first" first
                               cgOutput "second" second
        cgOutput "selected" selected
        cgOutput "defaultValue" (readArray defaulted key)
        cgReturn (readArray selected key)

  stdoutText <- compileProgramAndRunGenerated dir "arrayValuedTables" program
  sourceText <- readFile (dir </> "arrayValuedTables.c")
  assertBool ("Expected the selected array value, received:\n" ++ stdoutText) ("0x00000015UL" `isInfixOf` stdoutText)
  assertBool ("Expected the out-of-range default array value, received:\n" ++ stdoutText) ("defaultValue = 0x0000001eUL" `isInfixOf` stdoutText)
  if readyEntries
     then assertBool ("Expected retained array-valued table storage, received:\n" ++ sourceText)
                     (    "SBVArrayOutput_2_u8_3_u32 * const table" `isInfixOf` sourceText
                      && "sbv_array_stored_export_2_u8_3_u32(&sbv_local_array_ctx" `isInfixOf` sourceText
                      && "sbv_local_array_descriptor_" `isInfixOf` sourceText
                     )
     else assertBool "Expected guarded array initialization followed by an owned output export"
                     (    "switch((uint64_t)" `isInfixOf` sourceText
                      && "sbv_array_export_2_u8_3_u32(" `isInfixOf` sourceText
                      && "sbv_local_array_s" `isInfixOf` sourceText
                     )

-- | Exercise managed finite-table results returned independently from
-- multiple generated library translation units.
managedAggregateTableLibrary :: Assertion
managedAggregateTableLibrary = withSystemTempDirectory "sbv-managed-aggregate-table-library" $ \dir -> do
  let component :: Integer -> Word16 -> SBVCodeGen ()
      component driverSeed base = do
        cgOverwriteFiles True
        cgSetDriverValues [driverSeed]
        selector <- cgInput "selector" :: SBVCodeGen SWord8
        cgReturn (select [ literal ([base, base + 1] :: [Word16])
                         , literal ([base + 2, base + 3] :: [Word16])
                         ] (literal ([] :: [Word16])) selector)

  (_, cfg, bundle) <- compileToCLib' "managedAggregateTableLibrary"
    [ ("firstManagedTable",  component 0 10)
    , ("secondManagedTable", component 1 20)
    ]
  renderCgPgmBundle (Just dir) (cfg, bundle)
  stdoutText <- compileAndRunGenerated dir "managedAggregateTableLibrary"
  mapM_ (\fragment -> assertBool ("Expected managed aggregate-table library output to contain " ++ show fragment ++ ", received:\n" ++ stdoutText)
                                (fragment `isInfixOf` stdoutText))
    [ "[0x000aU, 0x000bU]"
    , "[0x0016U, 0x0017U]"
    ]

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

-- | Exercise borrowed nested tuple strings and independently owned tuple
-- outputs and returns.
ownedTextTuples :: Assertion
ownedTextTuples = withSystemTempDirectory "sbv-owned-text-tuples" $ \dir -> do
  let program = do
        cgOverwriteFiles True
        cgSetDriverValues [4]
        source <- cgInput "source" :: SBVCodeGen (SBV (String, (String, Word8)))
        let (first, nested)  = untuple source
            (second, count) = untuple nested
            result          = tuple (first SL.++ literal ":" SL.++ second, tuple (second SL.++ literal "!", count + 1))
        cgOutput "sourceCopy" source
        cgOutput "result" result
        cgReturn result

  stdoutText <- compileProgramAndRunGenerated dir "ownedTextTuples" program
  headerText <- readFile (dir </> "ownedTextTuples.h")
  mapM_ (\fragment -> assertBool ("Expected owned text-tuple output to contain " ++ show fragment ++ ", received:\n" ++ stdoutText)
                                (fragment `isInfixOf` stdoutText))
    [ ") =(sbv4:sbv5, (sbv5!, 7))"
    , "sourceCopy =(sbv4, (sbv5, 6))"
    , "result =(sbv4:sbv5, (sbv5!, 7))"
    ]
  assertBool "Expected recursive string ownership in generated tuple helpers"
             ("sbv_string_clone(source.field1)" `isInfixOf` headerText
           && "sbv_string_release(&value->field1)" `isInfixOf` headerText)

-- | Exercise guarded string-tuple ownership helpers shared by multiple
-- generated library translation units.
ownedTextTupleLibrary :: Assertion
ownedTextTupleLibrary = withSystemTempDirectory "sbv-owned-text-tuple-library" $ \dir -> do
  let component suffix resultValue seed = do
        cgOverwriteFiles True
        cgSetDriverValues [seed]
        source <- cgInput "source" :: SBVCodeGen SString
        cgReturn (tuple (source SL.++ suffix, literal resultValue :: SWord8))

  (_, cfg, bundle) <- compileToCLib' "ownedTextTupleLibrary"
    [ ("firstTextTuple",  component (literal "!") 9 4)
    , ("secondTextTuple", component (literal "?") 8 5)
    ]
  renderCgPgmBundle (Just dir) (cfg, bundle)
  stdoutText <- compileAndRunGenerated dir "ownedTextTupleLibrary"
  mapM_ (\fragment -> assertBool ("Expected text-tuple library output to contain " ++ show fragment ++ ", received:\n" ++ stdoutText)
                                (fragment `isInfixOf` stdoutText))
    [ "(sbv4!, 9)"
    , "(sbv5?, 8)"
    ]

-- | Exercise recursively nested tuple ownership across strings, exact-element
-- lists, and exact-element finite sets.
ownedCollectionTuples :: Assertion
ownedCollectionTuples = withSystemTempDirectory "sbv-owned-collection-tuples" $ \dir -> do
  let program = do
        cgOverwriteFiles True
        cgSetDriverValues [10]
        source <- cgInput "source" :: SBVCodeGen (SBV (String, ([Integer], RCSet Rational)))
        let (prefix, nested)  = untuple source
            (values, members) = untuple nested
            result            = tuple (prefix SL.++ literal "!", tuple (values SL.++ literal ([14] :: [Integer]), SS.insert 15 members))
        cgOutput "sourceCopy" source
        cgOutput "result" result
        cgReturn result

  stdoutText <- compileProgramAndRunGenerated dir "ownedCollectionTuples" program
  headerText <- readFile (dir </> "ownedCollectionTuples.h")
  mapM_ (\fragment -> assertBool ("Expected owned collection-tuple output to contain " ++ show fragment ++ ", received:\n" ++ stdoutText)
                                (fragment `isInfixOf` stdoutText))
    [ ") =(sbv10!, ([11, 12, 13, 14], {12, 13, 14, 15}))"
    , "sourceCopy =(sbv10, ([11, 12, 13], {12, 13, 14}))"
    , "result =(sbv10!, ([11, 12, 13, 14], {12, 13, 14, 15}))"
    ]
  assertBool "Expected recursive collection ownership in generated tuple helpers"
             ("sbv_list_clone_integer(source.field1)" `isInfixOf` headerText
           && "sbv_list_release_integer(&value->field1)" `isInfixOf` headerText
           && "sbv_set_clone_rational(source.field2)" `isInfixOf` headerText
           && "sbv_set_release_rational(&value->field2)" `isInfixOf` headerText)

-- | Exercise guarded collection-tuple declarations and exact-element
-- ownership helpers shared by multiple generated library translation units.
ownedCollectionTupleLibrary :: Assertion
ownedCollectionTupleLibrary = withSystemTempDirectory "sbv-owned-collection-tuple-library" $ \dir -> do
  let component :: Integer -> Integer -> SBVCodeGen ()
      component seed extra = do
        cgOverwriteFiles True
        cgSetDriverValues [seed]
        source <- cgInput "source" :: SBVCodeGen (SBV ([Integer], RCSet Rational))
        let (values, members) = untuple source
        cgReturn (tuple (values SL.++ literal [extra], SS.insert (fromInteger extra) members))

  (_, cfg, bundle) <- compileToCLib' "ownedCollectionTupleLibrary"
    [ ("firstCollectionTuple",  component 3 9)
    , ("secondCollectionTuple", component 5 10)
    ]
  renderCgPgmBundle (Just dir) (cfg, bundle)
  stdoutText <- compileAndRunGenerated dir "ownedCollectionTupleLibrary"
  mapM_ (\fragment -> assertBool ("Expected collection-tuple library output to contain " ++ show fragment ++ ", received:\n" ++ stdoutText)
                                (fragment `isInfixOf` stdoutText))
    [ "([3, 4, 5, 9], {4, 5, 6, 9})"
    , "([5, 6, 7, 10], {6, 7, 8, 10})"
    ]

-- | Exercise sequence and finite-set operations over recursively nested,
-- by-value tuple elements and return both descriptors through an owned tuple.
tupleValuedCollections :: Assertion
tupleValuedCollections = withSystemTempDirectory "sbv-tuple-valued-collections" $ \dir -> do
  let program = do
        cgOverwriteFiles True
        cgSetDriverValues [1, 4]
        values  <- cgInput "values"  :: SBVCodeGen (SList (Word16, Word8))
        members <- cgInput "members" :: SBVCodeGen (SSet (Word16, Word8))
        let extra    = tuple (literal 9 :: SWord16, literal 10 :: SWord8)
            joined   = values SL.++ SL.singleton extra
            inserted = SS.insert extra members
        cgOutput "listSameObject" (values .=== values)
        cgOutput "containsExtra" (extra `SS.member` inserted)
        cgOutput "joined" joined
        cgOutput "inserted" inserted
        cgReturn (tuple (joined, inserted))

  stdoutText <- compileProgramAndRunGenerated dir "tupleValuedCollections" program
  headerText <- readFile (dir </> "tupleValuedCollections.h")
  mapM_ (\fragment -> assertBool ("Expected tuple-valued collection output to contain " ++ show fragment ++ ", received:\n" ++ stdoutText)
                                (fragment `isInfixOf` stdoutText))
    [ "listSameObject = 1"
    , "containsExtra = 1"
    , "joined =[(0x0001U, 2), (0x0002U, 3), (0x0003U, 4), (0x0009U, 10)]"
    , "inserted ={(0x0004U, 5), (0x0005U, 6), (0x0006U, 7), (0x0009U, 10)}"
    ]
  assertBool "Expected tuple forward declarations before collection descriptors"
             ("typedef struct SBVTuple_" `isInfixOf` headerText
           && "const SBVTuple_" `isInfixOf` headerText)

-- | Exercise guarded tuple-element list and set descriptors shared by
-- multiple generated library translation units.
tupleValuedCollectionLibrary :: Assertion
tupleValuedCollectionLibrary = withSystemTempDirectory "sbv-tuple-valued-collection-library" $ \dir -> do
  let component :: Integer -> Word16 -> Word8 -> SBVCodeGen ()
      component seed first second = do
        cgOverwriteFiles True
        cgSetDriverValues [seed, seed + 3]
        values  <- cgInput "values"  :: SBVCodeGen (SList (Word16, Word8))
        members <- cgInput "members" :: SBVCodeGen (SSet (Word16, Word8))
        let extra = tuple (literal first, literal second)
        cgReturn (tuple (values SL.++ SL.singleton extra, SS.insert extra members))

  (_, cfg, bundle) <- compileToCLib' "tupleValuedCollectionLibrary"
    [ ("firstTupleCollections",  component 1 9 10)
    , ("secondTupleCollections", component 2 10 11)
    ]
  renderCgPgmBundle (Just dir) (cfg, bundle)
  stdoutText <- compileAndRunGenerated dir "tupleValuedCollectionLibrary"
  mapM_ (\fragment -> assertBool ("Expected tuple-valued collection library output to contain " ++ show fragment ++ ", received:\n" ++ stdoutText)
                                (fragment `isInfixOf` stdoutText))
    [ "[(0x0001U, 2), (0x0002U, 3), (0x0003U, 4), (0x0009U, 10)]"
    , "[(0x0002U, 3), (0x0003U, 4), (0x0004U, 5), (0x000aU, 11)]"
    ]

-- | Exercise deep ownership and structural equality for collection elements
-- that are tuples containing strings, exact values, and nested collections.
managedTupleValuedCollections :: Assertion
managedTupleValuedCollections = withSystemTempDirectory "sbv-managed-tuple-valued-collections" $ \dir -> do
  let program = do
        cgOverwriteFiles True
        cgSetDriverValues [1, 4, 7]
        values  <- cgInput "values"  :: SBVCodeGen (SList (String, Integer))
        members <- cgInput "members" :: SBVCodeGen (SSet (String, Integer))
        nested  <- cgInput "nested"  :: SBVCodeGen (SList ([Integer], RCSet Rational))
        let extra       = tuple (literal "extra" :: SString, literal 9 :: SInteger)
            nestedExtra = tuple (literal ([9, 10] :: [Integer]), SS.singleton (literal 11 :: SRational))
            joined      = values SL.++ SL.singleton extra
            inserted    = SS.insert extra members
            nestedJoin  = nested SL.++ SL.singleton nestedExtra
        cgOutput "listSameObject" (values .=== values)
        cgOutput "nestedSameObject" (nested .=== nested)
        cgOutput "containsExtra" (extra `SS.member` inserted)
        cgOutput "joined" joined
        cgOutput "inserted" inserted
        cgOutput "nestedJoin" nestedJoin
        cgReturn (tuple (joined, tuple (inserted, nestedJoin)))

  stdoutText <- compileProgramAndRunGenerated dir "managedTupleValuedCollections" program
  headerText <- readFile (dir </> "managedTupleValuedCollections.h")
  mapM_ (\fragment -> assertBool ("Expected managed tuple-valued collection output to contain " ++ show fragment ++ ", received:\n" ++ stdoutText)
                                (fragment `isInfixOf` stdoutText))
    [ "listSameObject = 1"
    , "nestedSameObject = 1"
    , "containsExtra = 1"
    , "joined =[(sbv1, 2), (sbv2, 3), (sbv3, 4), (extra, 9)]"
    , "inserted ={(sbv4, 5), (sbv5, 6), (sbv6, 7), (extra, 9)}"
    , "([9, 10], {11})"
    ]
  assertBool "Expected collection ownership to recurse through managed tuple elements"
             ("sbv_tuple_owned_clone_" `isInfixOf` headerText
           && "sbv_tuple_owned_release_" `isInfixOf` headerText
           && "sbv_string_clone(source.field1)" `isInfixOf` headerText
           && "sbv_list_clone_integer(source.field1)" `isInfixOf` headerText
           && "sbv_set_clone_rational(source.field2)" `isInfixOf` headerText)

-- | Exercise guarded ownership helpers for managed tuple-valued collections
-- shared by multiple generated library translation units.
managedTupleValuedCollectionLibrary :: Assertion
managedTupleValuedCollectionLibrary = withSystemTempDirectory "sbv-managed-tuple-valued-collection-library" $ \dir -> do
  let component :: Integer -> String -> Integer -> SBVCodeGen ()
      component seed textValue extraValue = do
        cgOverwriteFiles True
        cgSetDriverValues [seed, seed + 3]
        values  <- cgInput "values"  :: SBVCodeGen (SList (String, Integer))
        members <- cgInput "members" :: SBVCodeGen (SSet (String, Integer))
        let extra = tuple (literal textValue :: SString, literal extraValue :: SInteger)
        cgReturn (tuple (values SL.++ SL.singleton extra, SS.insert extra members))

  (_, cfg, bundle) <- compileToCLib' "managedTupleValuedCollectionLibrary"
    [ ("firstManagedTupleCollections",  component 1 "first" 9)
    , ("secondManagedTupleCollections", component 2 "second" 10)
    ]
  renderCgPgmBundle (Just dir) (cfg, bundle)
  stdoutText <- compileAndRunGenerated dir "managedTupleValuedCollectionLibrary"
  mapM_ (\fragment -> assertBool ("Expected managed tuple-valued collection library output to contain " ++ show fragment ++ ", received:\n" ++ stdoutText)
                                (fragment `isInfixOf` stdoutText))
    [ "[(sbv1, 2), (sbv2, 3), (sbv3, 4), (first, 9)]"
    , "[(sbv2, 3), (sbv3, 4), (sbv4, 5), (second, 10)]"
    ]

-- | Exercise string-valued symbolic collections and ADTs with direct string,
-- list-of-string, and set-of-string fields through operations and owned ABI
-- results.
textAggregateCollections :: Assertion
textAggregateCollections = withSystemTempDirectory "sbv-text-aggregate-collections" $ \dir -> do
  let program = do
        cgOverwriteFiles True
        cgSetDriverValues [1, 4, 6]
        values  <- cgInput "values"  :: SBVCodeGen (SList String)
        members <- cgInput "members" :: SBVCodeGen (SSet String)
        source  <- cgInput "source"  :: SBVCodeGen SCodeGenText
        let extra         = literal "extra" :: SString
            sourceName    = getCGText_1 source
            sourceValues  = getCGText_2 source
            sourceMembers = getCGText_3 source
            joined        = values SL.++ SL.singleton extra
            inserted      = SS.insert extra members
            result        = sCGText
                              (sourceName SL.++ literal "!")
                              (sourceValues SL.++ SL.singleton extra)
                              (SS.insert extra sourceMembers)
        cgOutput "sameValues" (values .=== values)
        cgOutput "sameMembers" (members .=== members)
        cgOutput "sameSource" (source .== source)
        cgOutput "containsExtra" (extra `SS.member` inserted)
        cgOutput "joined" joined
        cgOutput "inserted" inserted
        cgOutput "result" result
        cgReturn result

  stdoutText <- compileProgramAndRunGenerated dir "textAggregateCollections" program
  headerText <- readFile (dir </> "textAggregateCollections.h")
  mapM_ (\fragment -> assertBool ("Expected text-aggregate output to contain " ++ show fragment ++ ", received:\n" ++ stdoutText)
                                (fragment `isInfixOf` stdoutText))
    [ "sameValues = 1"
    , "sameMembers = 1"
    , "sameSource = 1"
    , "containsExtra = 1"
    , "joined =[sbv1, sbv2, sbv3, extra]"
    , "inserted ={sbv4, sbv5, sbv6, extra}"
    , "CGText(sbv6!, [sbv7, sbv8, sbv9, extra], {sbv8, sbv9, sbv10, extra})"
    ]
  assertBool "Expected ownership to recurse through direct and collection text fields"
             (    "struct SBVList_string { const SString *data; size_t length; };" `isInfixOf` headerText
              && "struct SBVSet_string { const SString *data; size_t length; bool is_complement; };" `isInfixOf` headerText
              && "sbv_string_clone(source.payload.constructor1.field1)" `isInfixOf` headerText
              && "sbv_string_release(&value->payload.constructor1.field1)" `isInfixOf` headerText
              && "sbv_list_clone_string(source.payload.constructor1.field2)" `isInfixOf` headerText
              && "sbv_set_clone_string(source.payload.constructor1.field3)" `isInfixOf` headerText
             )

-- | Exercise independently owned text-containing ADT results emitted by
-- multiple generated library translation units.
textAggregateLibrary :: Assertion
textAggregateLibrary = withSystemTempDirectory "sbv-text-aggregate-library" $ \dir -> do
  let component :: Integer -> SBVCodeGen ()
      component seed = do
        cgOverwriteFiles True
        cgSetDriverValues [seed]
        source <- cgInput "source" :: SBVCodeGen SCodeGenText
        cgReturn source

  (_, cfg, bundle) <- compileToCLib' "textAggregateLibrary"
    [ ("firstTextAggregate",  component 2)
    , ("secondTextAggregate", component 4)
    ]
  renderCgPgmBundle (Just dir) (cfg, bundle)
  stdoutText <- compileAndRunGenerated dir "textAggregateLibrary"
  mapM_ (\fragment -> assertBool ("Expected text-aggregate library output to contain " ++ show fragment ++ ", received:\n" ++ stdoutText)
                                (fragment `isInfixOf` stdoutText))
    [ "CGText(sbv2, [sbv3, sbv4, sbv5], {sbv4, sbv5, sbv6})"
    , "CGText(sbv4, [sbv5, sbv6, sbv7], {sbv6, sbv7, sbv8})"
    ]

-- | Exercise every direct list/set nesting pair admitted by SBV through
-- symbolic operations, printing, and recursively owned tuple outputs and
-- returns. Sets of sets are not SBV values because 'RCSet' has no 'Ord'
-- instance.
directlyNestedCollections :: Assertion
directlyNestedCollections = withSystemTempDirectory "sbv-directly-nested-collections" $ \dir -> do
  let program = do
        cgOverwriteFiles True
        cgSetDriverValues [1, 2, 4]
        nestedLists <- cgInput "nestedLists" :: SBVCodeGen (SList [Word16])
        listOfSets  <- cgInput "listOfSets"  :: SBVCodeGen (SList (RCSet Word16))
        setOfLists  <- cgInput "setOfLists"  :: SBVCodeGen (SSet [Word16])
        let extraList     = literal ([90, 91] :: [Word16])
            extraSet      = SS.fromList [92, 93] :: SSet Word16
            joinedLists   = nestedLists SL.++ SL.singleton extraList
            joinedSets    = listOfSets SL.++ SL.singleton extraSet
            insertedLists = SS.insert extraList setOfLists
            result        = tuple (joinedLists, tuple (joinedSets, insertedLists))
        cgOutput "sameNestedLists" (nestedLists .=== nestedLists)
        cgOutput "sameListOfSets" (listOfSets .=== listOfSets)
        cgOutput "sameSetOfLists" (setOfLists .=== setOfLists)
        cgOutput "joinedLists" joinedLists
        cgOutput "joinedSets" joinedSets
        cgOutput "insertedLists" insertedLists
        cgReturn result

  stdoutText <- compileProgramAndRunGenerated dir "directlyNestedCollections" program
  headerText <- readFile (dir </> "directlyNestedCollections.h")
  mapM_ (\fragment -> assertBool ("Expected directly nested collection output to contain " ++ show fragment ++ ", received:\n" ++ stdoutText)
                                (fragment `isInfixOf` stdoutText))
    [ "sameNestedLists = 1"
    , "sameListOfSets = 1"
    , "sameSetOfLists = 1"
    , "[0x005aU, 0x005bU]"
    , "{0x005cU, 0x005dU}"
    ]
  assertBool "Expected mutually forward-declared descriptors and recursive ownership helpers"
             (    "typedef struct SBVList_u16 SBVList_u16;" `isInfixOf` headerText
              && "typedef struct SBVSet_u16 SBVSet_u16;" `isInfixOf` headerText
              && "struct SBVList_set_3_u16 { const SBVSet_u16 *data; size_t length; };" `isInfixOf` headerText
              && "struct SBVSet_list_3_u16 { const SBVList_u16 *data; size_t length; bool is_complement; };" `isInfixOf` headerText
              && "sbv_list_clone_list_3_u16" `isInfixOf` headerText
              && "sbv_list_clone_set_3_u16" `isInfixOf` headerText
              && "sbv_set_clone_list_3_u16" `isInfixOf` headerText
             )

-- | Exercise independently owned list-of-set results emitted by multiple
-- generated library translation units.
directlyNestedCollectionLibrary :: Assertion
directlyNestedCollectionLibrary = withSystemTempDirectory "sbv-directly-nested-collection-library" $ \dir -> do
  let component :: Integer -> Word16 -> SBVCodeGen ()
      component seed extra = do
        cgOverwriteFiles True
        cgSetDriverValues [seed]
        values <- cgInput "values" :: SBVCodeGen (SList (RCSet Word16))
        cgReturn (values SL.++ SL.singleton (SS.fromList [extra, extra + 1]))

  (_, cfg, bundle) <- compileToCLib' "directlyNestedCollectionLibrary"
    [ ("firstNestedCollection",  component 2 90)
    , ("secondNestedCollection", component 4 92)
    ]
  renderCgPgmBundle (Just dir) (cfg, bundle)
  stdoutText <- compileAndRunGenerated dir "directlyNestedCollectionLibrary"
  mapM_ (\fragment -> assertBool ("Expected nested-collection library output to contain " ++ show fragment ++ ", received:\n" ++ stdoutText)
                                (fragment `isInfixOf` stdoutText))
    [ "{0x005aU, 0x005bU}"
    , "{0x005cU, 0x005dU}"
    ]

-- | Exercise lists and sets whose elements are managed or recursive ADTs,
-- including deep ownership and both symbolic equality modes.
adtValuedCollections :: Assertion
adtValuedCollections = withSystemTempDirectory "sbv-adt-valued-collections" $ \dir -> do
  let program = do
        cgOverwriteFiles True
        cgSetDriverValues [1, 2, 4]
        values <- cgInput "values" :: SBVCodeGen (SList CodeGenCollections)
        trees  <- cgInput "trees"  :: SBVCodeGen (SSet CodeGenTree)
        colors <- cgInput "colors" :: SBVCodeGen (SSet CodeGenEnum)
        let extraValue = sCGCollections
                           (literal ([9, 10] :: [Integer]))
                           (SS.singleton (literal 11 :: SRational))
                           (tuple (literal ([12] :: [Integer]), SS.singleton (literal 13 :: SRational)))
            extraTree  = sCGLeaf 99
            joined     = values SL.++ SL.singleton extraValue
            inserted   = SS.insert extraTree trees
            colored    = SS.insert sCGBlue colors
            allColors  = SS.fromList [CGRed, CGGreen, CGBlue]
        cgOutput "sameValues" (values .=== values)
        cgOutput "containsExtraTree" (extraTree `SS.member` inserted)
        cgOutput "containsBlue" (sCGBlue `SS.member` colored)
        cgOutput "sameColorUniverse" (allColors .== (SS.full :: SSet CodeGenEnum))
        cgOutput "joined" joined
        cgOutput "inserted" inserted
        cgOutput "colored" colored
        cgReturn (tuple (joined, inserted))

  stdoutText <- compileProgramAndRunGenerated dir "adtValuedCollections" program
  headerText <- readFile (dir </> "adtValuedCollections.h")
  sourceText <- readFile (dir </> "adtValuedCollections.c")
  mapM_ (\fragment -> assertBool ("Expected ADT-valued collection output to contain " ++ show fragment ++ ", received:\n" ++ stdoutText)
                                (fragment `isInfixOf` stdoutText))
    [ "sameValues = 1"
    , "containsExtraTree = 1"
    , "containsBlue = 1"
    , "sameColorUniverse = 1"
    , "CGCollections([9, 10], {11}, ([12], {13}))"
    , "CGLeaf(99)"
    , "CGBlue"
    ]
  assertBool "Expected ADT forward declarations before collection descriptors"
             ("typedef struct SBVADT_CodeGenCollections SBVADT_CodeGenCollections;" `isInfixOf` headerText
           && "const SBVADT_CodeGenCollections *data" `isInfixOf` headerText)
  assertBool "Expected collection ownership and equality to dispatch through ADT helpers"
             ("sbv_adt_owned_clone_SBVADT_CodeGenCollections" `isInfixOf` headerText
           && "sbv_adt_owned_release_SBVADT_CodeGenTree" `isInfixOf` headerText
           && "sbv_adt_object_equal_SBVADT_CodeGenCollections" `isInfixOf` sourceText
           && "sbv_adt_equal_SBVADT_CodeGenTree" `isInfixOf` sourceText)

-- | Exercise guarded recursive-ADT collection helpers shared by multiple
-- generated library translation units.
adtValuedCollectionLibrary :: Assertion
adtValuedCollectionLibrary = withSystemTempDirectory "sbv-adt-valued-collection-library" $ \dir -> do
  let component :: Integer -> Word8 -> SBVCodeGen ()
      component seed extraValue = do
        cgOverwriteFiles True
        cgSetDriverValues [seed]
        values <- cgInput "values" :: SBVCodeGen (SList CodeGenTree)
        cgReturn (values SL.++ SL.singleton (sCGLeaf (literal extraValue)))

  (_, cfg, bundle) <- compileToCLib' "adtValuedCollectionLibrary"
    [ ("firstADTCollections",  component 1 98)
    , ("secondADTCollections", component 2 99)
    ]
  renderCgPgmBundle (Just dir) (cfg, bundle)
  stdoutText <- compileAndRunGenerated dir "adtValuedCollectionLibrary"
  mapM_ (\fragment -> assertBool ("Expected ADT-valued collection library output to contain " ++ show fragment ++ ", received:\n" ++ stdoutText)
                                (fragment `isInfixOf` stdoutText))
    [ "CGLeaf(98)"
    , "CGLeaf(99)"
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

-- | Exercise direct and tuple-nested exact-element collections through ADT
-- construction, access, equality, outputs, and an independently owned return.
collectionADTs :: Assertion
collectionADTs = withSystemTempDirectory "sbv-collection-adts" $ \dir -> do
  let program = do
        cgOverwriteFiles True
        cgSetDriverValues [1]
        source <- cgInput "source" :: SBVCodeGen SCodeGenCollections
        let values                   = getCGCollections_1 source
            members                  = getCGCollections_2 source
            nested                   = getCGCollections_3 source
            (nestedValues, nestedSet) = untuple nested
            result                   = sCGCollections
                                         (values SL.++ literal ([4] :: [Integer]))
                                         (SS.insert 5 members)
                                         (tuple (nestedValues SL.++ literal ([6] :: [Integer]), SS.insert 7 nestedSet))
        cgOutput "sourceCopy" source
        cgOutput "sameValue" (source .== source)
        cgOutput "result" result
        cgReturn result

  stdoutText <- compileProgramAndRunGenerated dir "collectionADTs" program
  headerText <- readFile (dir </> "collectionADTs.h")
  mapM_ (\fragment -> assertBool ("Expected collection ADT output to contain " ++ show fragment ++ ", received:\n" ++ stdoutText)
                                (fragment `isInfixOf` stdoutText))
    [ ") =CGCollections([1, 2, 3, 4], {2, 3, 4, 5}, ([3, 4, 5, 6], {4, 5, 6, 7}))"
    , "sourceCopy =CGCollections([1, 2, 3], {2, 3, 4}, ([3, 4, 5], {4, 5, 6}))"
    , "sameValue = 1"
    , "result =CGCollections([1, 2, 3, 4], {2, 3, 4, 5}, ([3, 4, 5, 6], {4, 5, 6, 7}))"
    ]
  assertBool "Expected direct and tuple-nested collection ownership in ADT helpers"
             ("sbv_list_clone_integer(source.payload.constructor2.field1)" `isInfixOf` headerText
           && "sbv_set_release_rational(&value->payload.constructor2.field2)" `isInfixOf` headerText
           && "sbv_tuple_owned_set_" `isInfixOf` headerText)

-- | Exercise recursive pointer ownership whose terminal constructor contains
-- exact-element list and set fields, including recursive structural equality.
recursiveCollectionADTs :: Assertion
recursiveCollectionADTs = withSystemTempDirectory "sbv-recursive-collection-adts" $ \dir -> do
  let program = do
        cgOverwriteFiles True
        cgSetDriverValues [1]
        source <- cgInput "source" :: SBVCodeGen SCodeGenCollectionTree
        cgOutput "sameTree" (source .== source)
        cgOutput "treeCopy" source
        cgReturn source

  stdoutText <- compileProgramAndRunGenerated dir "recursiveCollectionADTs" program
  sourceText <- readFile (dir </> "recursiveCollectionADTs.c")
  mapM_ (\fragment -> assertBool ("Expected recursive collection ADT output to contain " ++ show fragment ++ ", received:\n" ++ stdoutText)
                                (fragment `isInfixOf` stdoutText))
    [ "CGCollectionBranch(CGCollectionBranch("
    , "CGCollectionLeaf([1, 2, 3], {2, 3, 4})"
    , "sameTree = 1"
    ]
  assertBool "Expected private recursive equality to use collection semantics after their runtimes"
             ("sbv_list_integer_equal" `isInfixOf` sourceText
           && "sbv_set_rational_equal" `isInfixOf` sourceText)

-- | Exercise guarded collection-owning ADT helpers shared by multiple
-- generated library translation units.
collectionADTLibrary :: Assertion
collectionADTLibrary = withSystemTempDirectory "sbv-collection-adt-library" $ \dir -> do
  let component :: Integer -> SBVCodeGen ()
      component seed = do
        cgOverwriteFiles True
        cgSetDriverValues [seed]
        source <- cgInput "source" :: SBVCodeGen SCodeGenNativeCollections
        cgReturn source

  (_, cfg, bundle) <- compileToCLib' "collectionADTLibrary"
    [ ("firstCollectionADT",  component 1)
    , ("secondCollectionADT", component 3)
    ]
  renderCgPgmBundle (Just dir) (cfg, bundle)
  stdoutText <- compileAndRunGenerated dir "collectionADTLibrary"
  mapM_ (\fragment -> assertBool ("Expected collection ADT library output to contain " ++ show fragment ++ ", received:\n" ++ stdoutText)
                                (fragment `isInfixOf` stdoutText))
    [ "CGNativeCollections([0x0001U, 0x0002U, 0x0003U], {0x0002U, 0x0003U, 0x0004U})"
    , "CGNativeCollections([0x0003U, 0x0004U, 0x0005U], {0x0004U, 0x0005U, 0x0006U})"
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
  sourceText <- readFile (dir </> "recursiveADTs.c")
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
             ("== NULL) abort();" `isInfixOf` sourceText)

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
