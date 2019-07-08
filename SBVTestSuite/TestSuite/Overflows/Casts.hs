-----------------------------------------------------------------------------
-- |
-- Module    : TestSuite.Overflows.Casts
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Test suite for overflow checking
-----------------------------------------------------------------------------

{-# LANGUAGE Rank2Types          #-}
{-# LANGUAGE ScopedTypeVariables #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module TestSuite.Overflows.Casts(tests) where

import Data.SBV
import Data.SBV.Tools.Overflow

import Utils.SBVTestFramework

type C a b = SBV a -> (SBV b, (SBool, SBool))

getBounds :: (Bounded a, Integral a) => a -> Maybe (Integer, Integer)
getBounds x = Just (fromIntegral (minBound `asTypeOf` x), fromIntegral (maxBound `asTypeOf` x))

-- Test suite
tests :: TestTree
tests = testGroup "Overflows" [testGroup "Casts" ts]
  where ts = [ testGroup "w8"  [ testCase "w8"  $ assertIsThm $ chk (getBounds (undefined :: Word8 )) (sFromIntegralO :: C Word8   Word8)
                               , testCase "w16" $ assertIsThm $ chk (getBounds (undefined :: Word16)) (sFromIntegralO :: C Word8   Word16)
                               , testCase "w32" $ assertIsThm $ chk (getBounds (undefined :: Word32)) (sFromIntegralO :: C Word8   Word32)
                               , testCase "w64" $ assertIsThm $ chk (getBounds (undefined :: Word64)) (sFromIntegralO :: C Word8   Word64)
                               , testCase "i8"  $ assertIsThm $ chk (getBounds (undefined :: Int8  )) (sFromIntegralO :: C Word8   Int8)
                               , testCase "i16" $ assertIsThm $ chk (getBounds (undefined :: Int16 )) (sFromIntegralO :: C Word8   Int16)
                               , testCase "i32" $ assertIsThm $ chk (getBounds (undefined :: Int32 )) (sFromIntegralO :: C Word8   Int32)
                               , testCase "i64" $ assertIsThm $ chk (getBounds (undefined :: Int64 )) (sFromIntegralO :: C Word8   Int64)
                               , testCase "i"   $ assertIsThm $ chk Nothing                           (sFromIntegralO :: C Word8   Integer)
                               ]
             , testGroup "w16" [ testCase "w8"  $ assertIsThm $ chk (getBounds (undefined :: Word8 )) (sFromIntegralO :: C Word16  Word8)
                               , testCase "w16" $ assertIsThm $ chk (getBounds (undefined :: Word16)) (sFromIntegralO :: C Word16  Word16)
                               , testCase "w32" $ assertIsThm $ chk (getBounds (undefined :: Word32)) (sFromIntegralO :: C Word16  Word32)
                               , testCase "w64" $ assertIsThm $ chk (getBounds (undefined :: Word64)) (sFromIntegralO :: C Word16  Word64)
                               , testCase "i8"  $ assertIsThm $ chk (getBounds (undefined :: Int8  )) (sFromIntegralO :: C Word16  Int8)
                               , testCase "i16" $ assertIsThm $ chk (getBounds (undefined :: Int16 )) (sFromIntegralO :: C Word16  Int16)
                               , testCase "i32" $ assertIsThm $ chk (getBounds (undefined :: Int32 )) (sFromIntegralO :: C Word16  Int32)
                               , testCase "i64" $ assertIsThm $ chk (getBounds (undefined :: Int64 )) (sFromIntegralO :: C Word16  Int64)
                               , testCase "i"   $ assertIsThm $ chk Nothing                           (sFromIntegralO :: C Word16  Integer)
                               ]
             , testGroup "w32" [ testCase "w8"  $ assertIsThm $ chk (getBounds (undefined :: Word8 )) (sFromIntegralO :: C Word32  Word8)
                               , testCase "w16" $ assertIsThm $ chk (getBounds (undefined :: Word16)) (sFromIntegralO :: C Word32  Word16)
                               , testCase "w32" $ assertIsThm $ chk (getBounds (undefined :: Word32)) (sFromIntegralO :: C Word32  Word32)
                               , testCase "w64" $ assertIsThm $ chk (getBounds (undefined :: Word64)) (sFromIntegralO :: C Word32  Word64)
                               , testCase "i8"  $ assertIsThm $ chk (getBounds (undefined :: Int8  )) (sFromIntegralO :: C Word32  Int8)
                               , testCase "i16" $ assertIsThm $ chk (getBounds (undefined :: Int16 )) (sFromIntegralO :: C Word32  Int16)
                               , testCase "i32" $ assertIsThm $ chk (getBounds (undefined :: Int32 )) (sFromIntegralO :: C Word32  Int32)
                               , testCase "i64" $ assertIsThm $ chk (getBounds (undefined :: Int64 )) (sFromIntegralO :: C Word32  Int64)
                               , testCase "i"   $ assertIsThm $ chk Nothing                           (sFromIntegralO :: C Word32  Integer)
                               ]
             , testGroup "w64" [ testCase "w8"  $ assertIsThm $ chk (getBounds (undefined :: Word8 )) (sFromIntegralO :: C Word64  Word8)
                               , testCase "w16" $ assertIsThm $ chk (getBounds (undefined :: Word16)) (sFromIntegralO :: C Word64  Word16)
                               , testCase "w32" $ assertIsThm $ chk (getBounds (undefined :: Word32)) (sFromIntegralO :: C Word64  Word32)
                               , testCase "w64" $ assertIsThm $ chk (getBounds (undefined :: Word64)) (sFromIntegralO :: C Word64  Word64)
                               , testCase "i8"  $ assertIsThm $ chk (getBounds (undefined :: Int8  )) (sFromIntegralO :: C Word64  Int8)
                               , testCase "i16" $ assertIsThm $ chk (getBounds (undefined :: Int16 )) (sFromIntegralO :: C Word64  Int16)
                               , testCase "i32" $ assertIsThm $ chk (getBounds (undefined :: Int32 )) (sFromIntegralO :: C Word64  Int32)
                               , testCase "i64" $ assertIsThm $ chk (getBounds (undefined :: Int64 )) (sFromIntegralO :: C Word64  Int64)
                               , testCase "i"   $ assertIsThm $ chk Nothing                           (sFromIntegralO :: C Word64  Integer)
                               ]
             , testGroup "i8"  [ testCase "w8"  $ assertIsThm $ chk (getBounds (undefined :: Word8 )) (sFromIntegralO :: C Int8    Word8)
                               , testCase "w16" $ assertIsThm $ chk (getBounds (undefined :: Word16)) (sFromIntegralO :: C Int8    Word16)
                               , testCase "w32" $ assertIsThm $ chk (getBounds (undefined :: Word32)) (sFromIntegralO :: C Int8    Word32)
                               , testCase "w64" $ assertIsThm $ chk (getBounds (undefined :: Word64)) (sFromIntegralO :: C Int8    Word64)
                               , testCase "i8"  $ assertIsThm $ chk (getBounds (undefined :: Int8  )) (sFromIntegralO :: C Int8    Int8)
                               , testCase "i16" $ assertIsThm $ chk (getBounds (undefined :: Int16 )) (sFromIntegralO :: C Int8    Int16)
                               , testCase "i32" $ assertIsThm $ chk (getBounds (undefined :: Int32 )) (sFromIntegralO :: C Int8    Int32)
                               , testCase "i64" $ assertIsThm $ chk (getBounds (undefined :: Int64 )) (sFromIntegralO :: C Int8    Int64)
                               , testCase "i"   $ assertIsThm $ chk Nothing                           (sFromIntegralO :: C Int8    Integer)
                               ]
             , testGroup "i16" [ testCase "w8"  $ assertIsThm $ chk (getBounds (undefined :: Word8 )) (sFromIntegralO :: C Int16   Word8)
                               , testCase "w16" $ assertIsThm $ chk (getBounds (undefined :: Word16)) (sFromIntegralO :: C Int16   Word16)
                               , testCase "w32" $ assertIsThm $ chk (getBounds (undefined :: Word32)) (sFromIntegralO :: C Int16   Word32)
                               , testCase "w64" $ assertIsThm $ chk (getBounds (undefined :: Word64)) (sFromIntegralO :: C Int16   Word64)
                               , testCase "i8"  $ assertIsThm $ chk (getBounds (undefined :: Int8  )) (sFromIntegralO :: C Int16   Int8)
                               , testCase "i16" $ assertIsThm $ chk (getBounds (undefined :: Int16 )) (sFromIntegralO :: C Int16   Int16)
                               , testCase "i32" $ assertIsThm $ chk (getBounds (undefined :: Int32 )) (sFromIntegralO :: C Int16   Int32)
                               , testCase "i64" $ assertIsThm $ chk (getBounds (undefined :: Int64 )) (sFromIntegralO :: C Int16   Int64)
                               , testCase "i"   $ assertIsThm $ chk Nothing                           (sFromIntegralO :: C Int16   Integer)
                               ]
             , testGroup "i32" [ testCase "w8"  $ assertIsThm $ chk (getBounds (undefined :: Word8 )) (sFromIntegralO :: C Int32   Word8)
                               , testCase "w16" $ assertIsThm $ chk (getBounds (undefined :: Word16)) (sFromIntegralO :: C Int32   Word16)
                               , testCase "w32" $ assertIsThm $ chk (getBounds (undefined :: Word32)) (sFromIntegralO :: C Int32   Word32)
                               , testCase "w64" $ assertIsThm $ chk (getBounds (undefined :: Word64)) (sFromIntegralO :: C Int32   Word64)
                               , testCase "i8"  $ assertIsThm $ chk (getBounds (undefined :: Int8  )) (sFromIntegralO :: C Int32   Int8)
                               , testCase "i16" $ assertIsThm $ chk (getBounds (undefined :: Int16 )) (sFromIntegralO :: C Int32   Int16)
                               , testCase "i32" $ assertIsThm $ chk (getBounds (undefined :: Int32 )) (sFromIntegralO :: C Int32   Int32)
                               , testCase "i64" $ assertIsThm $ chk (getBounds (undefined :: Int64 )) (sFromIntegralO :: C Int32   Int64)
                               , testCase "i"   $ assertIsThm $ chk Nothing                           (sFromIntegralO :: C Int32   Integer)
                               ]
             , testGroup "i64" [ testCase "w8"  $ assertIsThm $ chk (getBounds (undefined :: Word8 )) (sFromIntegralO :: C Int64   Word8)
                               , testCase "w16" $ assertIsThm $ chk (getBounds (undefined :: Word16)) (sFromIntegralO :: C Int64   Word16)
                               , testCase "w32" $ assertIsThm $ chk (getBounds (undefined :: Word32)) (sFromIntegralO :: C Int64   Word32)
                               , testCase "w64" $ assertIsThm $ chk (getBounds (undefined :: Word64)) (sFromIntegralO :: C Int64   Word64)
                               , testCase "i8"  $ assertIsThm $ chk (getBounds (undefined :: Int8  )) (sFromIntegralO :: C Int64   Int8)
                               , testCase "i16" $ assertIsThm $ chk (getBounds (undefined :: Int16 )) (sFromIntegralO :: C Int64   Int16)
                               , testCase "i32" $ assertIsThm $ chk (getBounds (undefined :: Int32 )) (sFromIntegralO :: C Int64   Int32)
                               , testCase "i64" $ assertIsThm $ chk (getBounds (undefined :: Int64 )) (sFromIntegralO :: C Int64   Int64)
                               , testCase "i"   $ assertIsThm $ chk Nothing                           (sFromIntegralO :: C Int64   Integer)
                               ]
             , testGroup "i"   [ testCase "w8"  $ assertIsThm $ chk (getBounds (undefined :: Word8 )) (sFromIntegralO :: C Integer Word8)
                               , testCase "w16" $ assertIsThm $ chk (getBounds (undefined :: Word16)) (sFromIntegralO :: C Integer Word16)
                               , testCase "w32" $ assertIsThm $ chk (getBounds (undefined :: Word32)) (sFromIntegralO :: C Integer Word32)
                               , testCase "w64" $ assertIsThm $ chk (getBounds (undefined :: Word64)) (sFromIntegralO :: C Integer Word64)
                               , testCase "i8"  $ assertIsThm $ chk (getBounds (undefined :: Int8  )) (sFromIntegralO :: C Integer Int8)
                               , testCase "i16" $ assertIsThm $ chk (getBounds (undefined :: Int16 )) (sFromIntegralO :: C Integer Int16)
                               , testCase "i32" $ assertIsThm $ chk (getBounds (undefined :: Int32 )) (sFromIntegralO :: C Integer Int32)
                               , testCase "i64" $ assertIsThm $ chk (getBounds (undefined :: Int64 )) (sFromIntegralO :: C Integer Int64)
                               , testCase "i"   $ assertIsThm $ chk Nothing                           (sFromIntegralO :: C Integer Integer)
                               ]
             ]

chk :: forall a b. (SymVal a, SymVal b, Integral a, Integral b) => Maybe (Integer, Integer) -> (SBV a -> (SBV b, (SBool, SBool))) -> Predicate
chk mb cvt = do (x :: SBV a) <- free "x"

                let (_ :: SBV b, (uf, ov)) = cvt x

                    ix :: SInteger
                    ix = sFromIntegral x

                    (ufCorrect, ovCorrect) = case mb of
                                               Nothing       -> (uf .== sFalse,            ov .== sFalse)
                                               Just (lb, ub) -> (uf .<=> ix .< literal lb, ov .<=> ix .> literal ub)

                return $ ufCorrect .&& ovCorrect
