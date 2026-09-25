-----------------------------------------------------------------------------
-- |
-- Module    : TestSuite.Crypto.AES
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Test suite for Documentation.SBV.Examples.Crypto.AES
-----------------------------------------------------------------------------

{-# OPTIONS_GHC -Wall -Werror #-}

{-# LANGUAGE DataKinds #-}

module TestSuite.Crypto.AES(tests) where

import Data.List (intercalate)
import System.Exit (ExitCode(..))
import System.FilePath ((</>))
import System.IO.Temp (withSystemTempDirectory)
import System.Process (readProcessWithExitCode)
import Test.Tasty.HUnit (assertEqual)

import Data.SBV.Internals
import Data.SBV.Tools.CodeGen (compileToC, compileToCLib)
import Documentation.SBV.Examples.Crypto.AES

import Utils.CCodeGen (generatedMakeOptions)
import Utils.SBVTestFramework

-- Test suite
tests :: TestTree
tests = testGroup "Crypto.AES" [
   goldenVsStringShow "aes128Enc" $ thd <$> compileToC'    "aes128Enc" (aes128EncDec True)
 , goldenVsStringShow "aes128Dec" $ thd <$> compileToC'    "aes128Dec" (aes128EncDec False)
 , goldenVsStringShow "aes128Lib" $ thd <$> compileToCLib' "aes128Lib" aes128Comps
 , testCase "generated standalone encryption" standaloneEncryption
 , testCase "generated AES128 library" $ libraryVector 128 aes128Key aes128CT
 , testCase "generated AES192 library" $ libraryVector 192 aes192Key aes192CT
 , testCase "generated AES256 library" $ libraryVector 256 aes256Key aes256CT
 ]
 where aes128EncDec d = do pt  <- cgInputArr 4 "pt"
                           key <- cgInputArr 4 "key"
                           cgSetDriverValues $ repeat 0
                           let (encKs, decKs) = aesKeySchedule key
                               res | d    = aesEncrypt pt encKs
                                   | True = aesDecrypt pt decKs
                           cgOutputArr "ct" res
       aes128Comps = [(f, setVals c) | (f, _, c) <- aesLibComponents 128]
       setVals c = cgSetDriverValues (repeat 0) >> c
       thd (_, _, r) = r

-- | Exercise the exact code-generation action shown in the documentation.
standaloneEncryption :: Assertion
standaloneEncryption = withSystemTempDirectory "sbv-aes-block" $ \dir -> do
  compileToC (Just dir) "aes128BlockEncrypt" (aes128BlockEncrypt >> cgOverwriteFiles True)
  runCaller dir "aes128BlockEncrypt" "aes128BlockEncrypt.o"
    [ cArray "pt" commonPT
    , cArray "key" aes128Key
    , cArray "expected" aes128CT
    , "SWord32 ct[4];"
    , "aes128BlockEncrypt(pt, key, ct);"
    , "assert(memcmp(ct, expected, sizeof expected) == 0);"
    ]

-- | Compose the generated key-schedule and block functions in C, checking
-- encryption and both decryption paths against the standard's test vectors.
-- Using an independent caller ensures that the key schedules are computed
-- by generated C, rather than supplied as precomputed Haskell driver values.
libraryVector :: Int -> Key -> [SWord 32] -> Assertion
libraryVector size key ciphertext = withSystemTempDirectory "sbv-aes-library" $ \dir -> do
  _ <- compileToCLib (Just dir) libraryName
         [(functionName, cgSetDriverValues values >> program >> cgOverwriteFiles True)
         | (functionName, values, program) <- aesLibComponents size]
  runCaller dir libraryName (libraryName ++ ".a")
    [ cArray "pt" commonPT
    , cArray "key" key
    , cArray "expected" ciphertext
    -- The public inverse-schedule wrapper reverses each group of key words.
    , cArray "invKey" (concatMap reverse (chop4 (extractFinalKey key)))
    , "SWord32 encKS[" ++ show expandedWords ++ "], decKS[" ++ show expandedWords ++ "], invKS[" ++ show expandedWords ++ "];"
    , "SWord32 ct[4], recovered[4];"
    , prefix ++ "KeySchedule(key, encKS, decKS);"
    , prefix ++ "BlockEncrypt(pt, encKS, ct);"
    , "assert(memcmp(ct, expected, sizeof expected) == 0);"
    , prefix ++ "BlockDecrypt(expected, decKS, recovered);"
    , "assert(memcmp(recovered, pt, sizeof pt) == 0);"
    , prefix ++ "InvKeySchedule(invKey, invKS);"
    , prefix ++ "OTFDecrypt(expected, invKS, recovered);"
    , "assert(memcmp(recovered, pt, sizeof pt) == 0);"
    ]
 where prefix = "aes" ++ show size
       libraryName = prefix ++ "Lib"
       expandedWords = 4 * (size `div` 32 + 7)

-- | Render the existing concrete test vectors as C arrays.
cArray :: String -> [SWord 32] -> String
cArray arrayName values = "const SWord32 " ++ arrayName ++ "[] = {"
                       ++ intercalate ", " ["0x" ++ hex8 value ++ "UL" | value <- values] ++ "};"

-- | Build and run a caller using the generated Makefile's compiler and flags.
-- Keep assertions enabled, and preserve optional sanitizer instrumentation.
runCaller :: FilePath -> String -> FilePath -> [String] -> Assertion
runCaller dir header dependency body = do
  writeFile (dir </> "caller.c") $ unlines $
    [ "#undef NDEBUG"
    , "#include <assert.h>"
    , "#include <string.h>"
    , "#include \"" ++ header ++ ".h\""
    , "int main(void) {"
    ] ++ map ("  " ++) body ++ ["  return 0;", "}"]
  writeFile (dir </> "caller.mk") $ unlines
    [ "caller: caller.c " ++ header ++ ".h " ++ dependency
    , "\t${CC} ${CCFLAGS} caller.c " ++ dependency ++ " ${LDFLAGS} ${SBV_LIBS} -o $@"
    ]
  makeOptions <- generatedMakeOptions dir
  (buildExit, buildOutput, buildError) <- readProcessWithExitCode "make"
    (["-C", dir, "caller"] ++ makeOptions) ""
  assertEqual (buildOutput ++ buildError) ExitSuccess buildExit
  (runExit, runOutput, runError) <- readProcessWithExitCode (dir </> "caller") [] ""
  assertEqual (runOutput ++ runError) ExitSuccess runExit
