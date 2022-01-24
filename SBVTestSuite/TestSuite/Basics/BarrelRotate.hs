-----------------------------------------------------------------------------
-- |
-- Module    : TestSuite.Basics.BarrelRotate
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Test barrel rotates.
-----------------------------------------------------------------------------

{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications    #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module TestSuite.Basics.BarrelRotate (tests)  where

import Utils.SBVTestFramework

-- Test suite
tests :: TestTree
tests = testGroup "Basics.BarrelRotate" [
          goldenCapturedIO "barrelRotate_Left_Int8_Word8"     $ check $ checkLeft   @Int8   @Word8
        , goldenCapturedIO "barrelRotate_Left_Int8_Word16"    $ check $ checkLeft   @Int8   @Word16
        , goldenCapturedIO "barrelRotate_Left_Int8_Word32"    $ check $ checkLeft   @Int8   @Word32
        , goldenCapturedIO "barrelRotate_Left_Int8_Word64"    $ check $ checkLeft   @Int8   @Word64
        , goldenCapturedIO "barrelRotate_Left_Int16_Word8"    $ check $ checkLeft   @Int16  @Word8
        , goldenCapturedIO "barrelRotate_Left_Int16_Word16"   $ check $ checkLeft   @Int16  @Word16
        , goldenCapturedIO "barrelRotate_Left_Int16_Word32"   $ check $ checkLeft   @Int16  @Word32
        , goldenCapturedIO "barrelRotate_Left_Int16_Word64"   $ check $ checkLeft   @Int16  @Word64
        , goldenCapturedIO "barrelRotate_Left_Int32_Word8"    $ check $ checkLeft   @Int32  @Word8
        , goldenCapturedIO "barrelRotate_Left_Int32_Word16"   $ check $ checkLeft   @Int32  @Word16
        , goldenCapturedIO "barrelRotate_Left_Int32_Word32"   $ check $ checkLeft   @Int32  @Word32
        , goldenCapturedIO "barrelRotate_Left_Int32_Word64"   $ check $ checkLeft   @Int32  @Word64
        , goldenCapturedIO "barrelRotate_Left_Int64_Word8"    $ check $ checkLeft   @Int64  @Word8
        , goldenCapturedIO "barrelRotate_Left_Int64_Word16"   $ check $ checkLeft   @Int64  @Word16
        , goldenCapturedIO "barrelRotate_Left_Int64_Word32"   $ check $ checkLeft   @Int64  @Word32
        , goldenCapturedIO "barrelRotate_Left_Int64_Word64"   $ check $ checkLeft   @Int64  @Word64
        , goldenCapturedIO "barrelRotate_Left_Word8_Word8"    $ check $ checkLeft   @Word8  @Word8
        , goldenCapturedIO "barrelRotate_Left_Word8_Word16"   $ check $ checkLeft   @Word8  @Word16
        , goldenCapturedIO "barrelRotate_Left_Word8_Word32"   $ check $ checkLeft   @Word8  @Word32
        , goldenCapturedIO "barrelRotate_Left_Word8_Word64"   $ check $ checkLeft   @Word8  @Word64
        , goldenCapturedIO "barrelRotate_Left_Word16_Word8"   $ check $ checkLeft   @Word16 @Word8
        , goldenCapturedIO "barrelRotate_Left_Word16_Word16"  $ check $ checkLeft   @Word16 @Word16
        , goldenCapturedIO "barrelRotate_Left_Word16_Word32"  $ check $ checkLeft   @Word16 @Word32
        , goldenCapturedIO "barrelRotate_Left_Word16_Word64"  $ check $ checkLeft   @Word16 @Word64
        , goldenCapturedIO "barrelRotate_Left_Word32_Word8"   $ check $ checkLeft   @Word32 @Word8
        , goldenCapturedIO "barrelRotate_Left_Word32_Word16"  $ check $ checkLeft   @Word32 @Word16
        , goldenCapturedIO "barrelRotate_Left_Word32_Word32"  $ check $ checkLeft   @Word32 @Word32
        , goldenCapturedIO "barrelRotate_Left_Word32_Word64"  $ check $ checkLeft   @Word32 @Word64
        , goldenCapturedIO "barrelRotate_Left_Word64_Word8"   $ check $ checkLeft   @Word64 @Word8
        , goldenCapturedIO "barrelRotate_Left_Word64_Word16"  $ check $ checkLeft   @Word64 @Word16
        , goldenCapturedIO "barrelRotate_Left_Word64_Word32"  $ check $ checkLeft   @Word64 @Word32
        , goldenCapturedIO "barrelRotate_Left_Word64_Word64"  $ check $ checkLeft   @Word64 @Word64
        , goldenCapturedIO "barrelRotate_Right_Int8_Word8"    $ check $ checkRight  @Int8   @Word8
        , goldenCapturedIO "barrelRotate_Right_Int8_Word16"   $ check $ checkRight  @Int8   @Word16
        , goldenCapturedIO "barrelRotate_Right_Int8_Word32"   $ check $ checkRight  @Int8   @Word32
        , goldenCapturedIO "barrelRotate_Right_Int8_Word64"   $ check $ checkRight  @Int8   @Word64
        , goldenCapturedIO "barrelRotate_Right_Int16_Word8"   $ check $ checkRight  @Int16  @Word8
        , goldenCapturedIO "barrelRotate_Right_Int16_Word16"  $ check $ checkRight  @Int16  @Word16
        , goldenCapturedIO "barrelRotate_Right_Int16_Word32"  $ check $ checkRight  @Int16  @Word32
        , goldenCapturedIO "barrelRotate_Right_Int16_Word64"  $ check $ checkRight  @Int16  @Word64
        , goldenCapturedIO "barrelRotate_Right_Int32_Word8"   $ check $ checkRight  @Int32  @Word8
        , goldenCapturedIO "barrelRotate_Right_Int32_Word16"  $ check $ checkRight  @Int32  @Word16
        , goldenCapturedIO "barrelRotate_Right_Int32_Word32"  $ check $ checkRight  @Int32  @Word32
        , goldenCapturedIO "barrelRotate_Right_Int32_Word64"  $ check $ checkRight  @Int32  @Word64
        , goldenCapturedIO "barrelRotate_Right_Int64_Word8"   $ check $ checkRight  @Int64  @Word8
        , goldenCapturedIO "barrelRotate_Right_Int64_Word16"  $ check $ checkRight  @Int64  @Word16
        , goldenCapturedIO "barrelRotate_Right_Int64_Word32"  $ check $ checkRight  @Int64  @Word32
        , goldenCapturedIO "barrelRotate_Right_Int64_Word64"  $ check $ checkRight  @Int64  @Word64
        , goldenCapturedIO "barrelRotate_Right_Word8_Word8"   $ check $ checkRight  @Word8  @Word8
        , goldenCapturedIO "barrelRotate_Right_Word8_Word16"  $ check $ checkRight  @Word8  @Word16
        , goldenCapturedIO "barrelRotate_Right_Word8_Word32"  $ check $ checkRight  @Word8  @Word32
        , goldenCapturedIO "barrelRotate_Right_Word8_Word64"  $ check $ checkRight  @Word8  @Word64
        , goldenCapturedIO "barrelRotate_Right_Word16_Word8"  $ check $ checkRight  @Word16 @Word8
        , goldenCapturedIO "barrelRotate_Right_Word16_Word16" $ check $ checkRight  @Word16 @Word16
        , goldenCapturedIO "barrelRotate_Right_Word16_Word32" $ check $ checkRight  @Word16 @Word32
        , goldenCapturedIO "barrelRotate_Right_Word16_Word64" $ check $ checkRight  @Word16 @Word64
        , goldenCapturedIO "barrelRotate_Right_Word32_Word8"  $ check $ checkRight  @Word32 @Word8
        , goldenCapturedIO "barrelRotate_Right_Word32_Word16" $ check $ checkRight  @Word32 @Word16
        , goldenCapturedIO "barrelRotate_Right_Word32_Word32" $ check $ checkRight  @Word32 @Word32
        , goldenCapturedIO "barrelRotate_Right_Word32_Word64" $ check $ checkRight  @Word32 @Word64
        , goldenCapturedIO "barrelRotate_Right_Word64_Word8"  $ check $ checkRight  @Word64 @Word8
        , goldenCapturedIO "barrelRotate_Right_Word64_Word16" $ check $ checkRight  @Word64 @Word16
        , goldenCapturedIO "barrelRotate_Right_Word64_Word32" $ check $ checkRight  @Word64 @Word32
        , goldenCapturedIO "barrelRotate_Right_Word64_Word64" $ check $ checkRight  @Word64 @Word64
        ]
    where -- NB. We use CVC5 for these tests as Z3 is rather slow!
          check f gf = do r <- proveWith cvc5{verbose = True, redirectVerbose = Just gf} f
                          appendFile gf ("\nFINAL:\n" ++ show r ++ "\nDONE!\n")

          checkLeft :: forall a b. (SFiniteBits a, SFiniteBits b, SIntegral a, SIntegral b) => SBV a -> SBV b -> SBool
          checkLeft x y = x `sBarrelRotateLeft` y .== x `sRotateLeft` y

          checkRight :: forall a b. (SFiniteBits a, SFiniteBits b, SIntegral a, SIntegral b) => SBV a -> SBV b -> SBool
          checkRight x y = x `sBarrelRotateRight` y .== x `sRotateRight` y
