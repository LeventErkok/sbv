-----------------------------------------------------------------------------
-- |
-- Module    : TestSuite.CodeGeneration.ArbitraryBits
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Compile-and-run tests for C lowering of arbitrary-width bit-vectors.
-----------------------------------------------------------------------------

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeApplications #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module TestSuite.CodeGeneration.ArbitraryBits (tests) where

import Data.List                 (isInfixOf)
import Data.Proxy                (Proxy(..))
import Numeric                   (showHex)
import System.Exit               (ExitCode(..))
import System.FilePath           ((</>))
import System.IO.Temp            (withSystemTempDirectory)
import System.Process            (readProcessWithExitCode)
import Test.Tasty.HUnit          (assertBool, assertEqual)

import Data.SBV.Internals

import Utils.SBVTestFramework hiding ((#), bvExtract)

-- | Arbitrary-width C backend tests.
tests :: TestTree
tests = testGroup "CodeGeneration.ArbitraryBits"
  [ testCase "compile and execute 673-bit arithmetic" wide673
  , testCase "compile and execute signed 673-bit arithmetic" signed673
  , testCase "compile and execute non-aligned join/extract" joinExtract
  ]

-- | Exercise unsigned 673-bit arithmetic, shifts, rotation, and division.
wide673 :: Assertion
wide673 = withSystemTempDirectory "sbv-wide673" $ \dir -> do
  let program = do
        cgOverwriteFiles True
        cgSetDriverValues [x, y]
        a <- cgInput "a" :: SBVCodeGen (SWord 673)
        b <- cgInput "b" :: SBVCodeGen (SWord 673)
        let symbolicResult = rotateL (((a + b) * (a - b)) `xor` shiftR a 67) 193
        cgReturn (symbolicResult `sQuot` (b + 1))
  compileAndRun dir "wide673" program (asHex 11 result)
 where w        = 673
       modulus  = 2 ^ w
       mask     = modulus - 1
       x        = 2 ^ (672 :: Int) + 9
       y        = 17
       add a b  = (a + b) .&. mask
       sub a b  = (a - b) .&. mask
       mul a b  = (a * b) .&. mask
       shr a n  = a `shiftR` n
       rotl a n = let r = n `mod` w in ((a `shiftLInteger` r) .|. (a `shiftR` (w - r))) .&. mask
       expectedZ = rotl (mul (add x y) (sub x y) `xor` shr x 67) 193
       result   = expectedZ `quot` add y 1
       shiftLInteger a n = a * (2 ^ n)

-- | Exercise signed 673-bit ordering, quotient, remainder, and arithmetic shift.
signed673 :: Assertion
signed673 = withSystemTempDirectory "sbv-signed673" $ \dir -> do
  let program = do
        cgOverwriteFiles True
        cgSetDriverValues [x, y]
        a <- cgInput "a" :: SBVCodeGen (SInt 673)
        b <- cgInput "b" :: SBVCodeGen (SInt 673)
        let q = a `sQuot` b
            r = a `sRem`  b
        cgReturn $ ite (a .< b) (q + r) (shiftR a 130)
  compileAndRun dir "signed673" program (asHex 11 expectedRaw)
 where modulus    = 2 ^ (673 :: Int)
       x          = negate (2 ^ (671 :: Int)) + 12345
       y          = -17
       expectedRaw = ((x `quot` y) + (x `rem` y)) `mod` modulus

-- | Exercise non-aligned concatenation and extraction across limb boundaries.
joinExtract :: Assertion
joinExtract = withSystemTempDirectory "sbv-join-extract" $ \dir -> do
  let program = do
        cgOverwriteFiles True
        cgSetDriverValues [hi, lo]
        a <- cgInput "high" :: SBVCodeGen (SWord 337)
        b <- cgInput "low"  :: SBVCodeGen (SWord 336)
        let joined = a # b :: SWord 673
        cgReturn (bvExtract (Proxy @511) (Proxy @128) joined :: SWord 384)
  compileAndRun dir "joinExtract" program (asHex 6 expected)
 where hi       = 2 ^ (336 :: Int) + 0x123456789abcdef
       lo       = 2 ^ (335 :: Int) + 0xfedcba987654321
       expectedJoined = hi * 2 ^ (336 :: Int) + lo
       expected = (expectedJoined `shiftR` 128) .&. (2 ^ (384 :: Int) - 1)

-- | Generate, compile, and execute a C program, checking its encoded result.
compileAndRun :: FilePath -> String -> SBVCodeGen () -> String -> Assertion
compileAndRun dir functionName program expected = do
  (_, cfg, bundle) <- compileToC' functionName program
  renderCgPgmBundle (Just dir) (cfg, bundle)

  let source = dir </> functionName ++ ".c"
      driver = dir </> functionName ++ "_driver.c"
      exe    = dir </> functionName ++ "_driver"
  (ccExit, _, ccErr) <- readProcessWithExitCode "cc" ["-std=c11", "-Wall", "-Werror", source, driver, "-o", exe] ""
  assertEqual ccErr ExitSuccess ccExit

  (runExit, out, runErr) <- readProcessWithExitCode exe [] ""
  assertEqual runErr ExitSuccess runExit
  assertBool ("Expected generated output to contain " ++ expected ++ ", received:\n" ++ out) (expected `isInfixOf` out)

-- | Render the fixed-limb hexadecimal form printed by generated drivers.
asHex :: Int -> Integer -> String
asHex limbCount value = "0x" ++ replicate (16 * limbCount - length h) '0' ++ h
 where h = showHex value ""
