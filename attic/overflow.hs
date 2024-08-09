-- N-bit signed multiplication overflow detection using a N+1 bit multiplier

{-# LANGUAGE DataKinds            #-}
{-# LANGUAGE ExplicitNamespaces   #-}
{-# LANGUAGE TypeFamilies         #-}
{-# LANGUAGE UndecidableInstances #-}

{-# OPTIONS_GHC -Wall -Werror     #-}

module Main(main) where

import Data.SBV
import Data.SBV.Tools.Overflow (bvMulO)

import Data.Proxy
import Data.Kind
import Data.Type.Bool
import Data.Type.Equality

import Control.Monad

import GHC.TypeLits

type InvalidBVSMULO (n :: Nat) = 'Text "Invalid type/size with n: " ':<>: 'ShowType n
                               ':$$: 'Text ""
                               ':$$: 'Text "A valid call must pass `SInt n` argument with 0 < n <= 32769"
                               ':$$: 'Text ""
                               ':$$: 'Text "Given type falls outside of this range, or the size is not a known natural."

-- We use an SWord16 as the nonSignBitPos; and we add two of these. The function computes
-- N-2 at the largest for N bits. Two of them give us 2N-4, and to fit into SWord16,
-- we need 2N-4 <= 2^16-1, which implies N <= 32769, or N < 32770; which should be plenty enough for
-- any practical purpose. Hence the constraint below.
--
-- Alternatively, we can use Integers and not worry about this, alas Bitwuzla (which does really well
-- on bit-vector programs) does not support unbounded integers.
--
-- TODO: See if we can avoid the addition completely and somehow do a position comparision to see if it'll be N-2.
type family BVIsValidSMulO (arg :: Nat) :: Constraint where
   BVIsValidSMulO (n :: Nat) = ( BVIsNonZero n
                               , KnownNat n
                               , If (n `CmpNat` 32770 == 'LT)
                                    (() :: Constraint)
                                    (TypeError (InvalidBVSMULO n)))

-- Find the position of the first non-sign bit. i.e., the first bit that differs from the msb.
-- Position is 0 indexed. Note that if there's no differing bit, then you also get back 0.
-- This is essentially an approximation of the logarithm of the magnitude of the number.
--
-- Example for 3 bits:
--
--    000 -> 0  (no differing bit from 0; so we get 0)
--    001 -> 0
--    010 -> 1
--    011 -> 1
--    100 -> 1
--    101 -> 1
--    110 -> 0
--    111 -> 0  (no differing bit from 1; so we get 0)
nonSignBitPos :: BVIsValidSMulO n => SInt n -> SWord 16
nonSignBitPos w = case blastBE w of
                []     -> error $ "Impossible happened: Got no bits after blasing " ++ show w
                x : xs -> walk (.== sNot x) (literal (fromIntegral (length xs - 1))) xs
 where walk :: (SBool -> SBool) -> SWord 16 -> [SBool] -> SWord 16
       walk _check _i []     = 0
       walk  check  i (b:bs) = ite (check b) i (walk check (i-1) bs)

-- Algorithm using an N+1 bit multiplier
bvsmulO :: forall n. (BVIsValidSMulO n, BVIsNonZero (n+1), KnownNat (n+1)) => SInt n -> SInt n -> SBool
bvsmulO x y = sNot zeroOut .&& overflow
  where zeroOut = x .== 0 .|| y .== 0

        prod :: SInt (n+1)
        prod = sFromIntegral x * sFromIntegral y

        nv :: Int
        nv = fromIntegral $ natVal (Proxy @n)

        prodN, prodNm1 :: SBool
        prodN   = prod `sTestBit` nv
        prodNm1 = prod `sTestBit` (nv-1)

        overflow =   ((nonSignBitPos x + nonSignBitPos y) .> literal (fromIntegral (nv - 2)))
                 .|| (prodN .<+> prodNm1)

-- Text-book definition
textbook :: forall n. (BVIsNonZero n, KnownNat n, BVIsNonZero (n+n), KnownNat (n+n)) => SInt n -> SInt n -> SBool
textbook x y = prod2N ./= sFromIntegral prodN
  where prod2N :: SInt (n+n)
        prod2N = sFromIntegral x * sFromIntegral y

        prodN :: SInt n
        prodN = x * y

test :: forall proxy n. (BVIsValidSMulO n, BVIsNonZero (n+1), KnownNat (n+1), BVIsNonZero (n+n), KnownNat (n+n)) => proxy n -> Bool -> IO ()
test _ checkTextBook = do print =<< check "Against builtin"  bvMulO
                          when checkTextBook (print =<< check "Against textbook" textbook)
   where check w f = do putStrLn $ "Proving: " ++ w ++ ", N = " ++ show (natVal (Proxy @n))
                        proveWith bitwuzla $ do
                          x <- sInt "x"
                          y <- sInt "x"
                          pure $ f x y .== (bvsmulO :: SInt n -> SInt n -> SBool) x y

main :: IO ()
main = do test (Proxy @1)  True
          test (Proxy @2)  True
          test (Proxy @3)  True
          test (Proxy @4)  True
          test (Proxy @5)  True
          test (Proxy @6)  True
          test (Proxy @7)  True
          test (Proxy @8)  True
          test (Proxy @16) True
          test (Proxy @24) True
          test (Proxy @32) True
          test (Proxy @64) False
