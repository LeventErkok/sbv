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
import Data.List (isInfixOf)
import Data.SBV.Internals
import qualified Data.SBV.Char as SC
import qualified Data.SBV.List as SL
import qualified Data.SBV.Set as SS
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
  , testCase "compile and execute characters and strings" characterStrings
  , testCase "compile strings with mapped integers" mappedIntegerStrings
  , testCase "return owned strings from a generated library" ownedStringLibrary
  , testCase "compile and execute symbolic lists" symbolicLists
  , testCase "compile arbitrary-width symbolic lists" wideSymbolicLists
  , testCase "compile arbitrary floating-point symbolic lists" arbitraryFloatLists
  , testCase "preserve native floating-point list equality" nativeFloatLists
  , testCase "compile lists with mapped numeric elements" mappedNumericLists
  , testCase "return owned lists from a generated library" ownedListLibrary
  , testCase "reject lists of exact GMP values" exactGMPLists
  , testCase "compile and execute symbolic sets" symbolicSets
  , testCase "compare finite and cofinite Boolean sets" finiteUniverseSets
  , testCase "compile arbitrary-width symbolic sets" wideSymbolicSets
  , testCase "compile character symbolic sets" characterSets
  , testCase "compile arbitrary floating-point symbolic sets" arbitraryFloatSets
  , testCase "preserve native floating-point set equality" nativeFloatSets
  , testCase "compile sets with mapped numeric elements" mappedNumericSets
  , testCase "return owned sets from a generated library" ownedSetLibrary
  , testCase "reject sets of exact GMP values" exactGMPSets
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
             ("typedef struct { const SWord16 *data; size_t length; } SBVList_u16;" `isInfixOf` headerText)
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
             ("typedef struct { const SWord673 *data; size_t length; } SBVList_u673;" `isInfixOf` headerText)

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
             ("typedef struct { const SFP7_19 *data; size_t length; } SBVList_fp_e7_s19;" `isInfixOf` generated)
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

-- | Report the current deep-ownership boundary explicitly when a list stores
-- exact GMP-backed values.
exactGMPLists :: Assertion
exactGMPLists = do
  result <- try (do
    (_, _, bundle) <- compileToC' "exactGMPLists" $ do
      values <- cgInput "values" :: SBVCodeGen (SList Integer)
      cgReturn values
    evaluate (length (show bundle))) :: IO (Either ErrorCall Int)
  case result of
    Left exception -> assertBool ("Expected an exact-list ownership diagnostic, received:\n" ++ displayException exception)
                                 ("Lists with element kinds SInteger" `isInfixOf` displayException exception)
    Right _        -> assertBool "Expected exact GMP list elements to be rejected" False

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
             ("typedef struct { const SWord16 *data; size_t length; bool is_complement; } SBVSet_u16;" `isInfixOf` headerText)
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
             ("typedef struct { const SWord673 *data; size_t length; bool is_complement; } SBVSet_u673;" `isInfixOf` headerText)

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
             ("typedef struct { const SChar *data; size_t length; bool is_complement; } SBVSet_char;" `isInfixOf` headerText)

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
             ("typedef struct { const SFP7_19 *data; size_t length; bool is_complement; } SBVSet_fp_e7_s19;" `isInfixOf` generated)
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

-- | Report the current deep-ownership boundary explicitly when a set stores
-- exact GMP-backed values.
exactGMPSets :: Assertion
exactGMPSets = do
  result <- try (do
    (_, _, bundle) <- compileToC' "exactGMPSets" $ do
      values <- cgInput "values" :: SBVCodeGen (SSet Integer)
      cgReturn values
    evaluate (length (show bundle))) :: IO (Either ErrorCall Int)
  case result of
    Left exception -> assertBool ("Expected an exact-set ownership diagnostic, received:\n" ++ displayException exception)
                                 ("Sets with element kinds SInteger" `isInfixOf` displayException exception)
    Right _        -> assertBool "Expected exact GMP set elements to be rejected" False

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
