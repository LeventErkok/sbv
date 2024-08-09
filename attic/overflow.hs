-- N-bit signed multiplication overflow detection using a N+1 bit multiplier

{-# LANGUAGE DataKinds #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module Main(main) where

import Control.Monad
import Data.Proxy

import GHC.TypeLits

import Data.SBV
import Data.SBV.Tools.Overflow (bvMulO)

-- Find the position of the first non-sign bit. i.e., the first bit that differs from the msb.
-- Position is 0 indexed. Note that if there's no differing bit, then you also get back 0.
-- This is essentially an approximation of the logarithm of the magnitude of the number.
--
-- The result is at most N-2 for an N-bit word. Later we add two of these, so the maximum
-- value we need to represent is 2N-4. This will require 1 + lg(2N-4) = 2 + log(N-1) bits.
-- To suppor the case N=0, we return a (2 + log N) bit word.
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
nonSignBitPos :: ( KnownNat n,            BVIsNonZero n
                 , KnownNat (2 + Log2 n), BVIsNonZero (2+Log2 n))
                 => SInt n -> SWord (2 + Log2 n)
nonSignBitPos w = walk 0 rest
  where (sign, rest) = case blastBE w of
                         []     -> error $ "Impossible happened, blastBE returned no bits for " ++ show w
                         (x:xs) -> (x, zip [0..] (reverse xs))

        walk sofar []          = sofar
        walk sofar ((i, b):bs) = walk (ite (b ./= sign) i sofar) bs

-- Algorithm using an N+1 bit multiplier
bvsmulO :: forall n. ( KnownNat n,          BVIsNonZero n
                     , KnownNat (n+1),      BVIsNonZero (n+1)
                     , KnownNat (2+Log2 n), BVIsNonZero (2+Log2 n))
                     => SInt n -> SInt n -> SBool
bvsmulO x y = sNot zeroOut .&& overflow
  where zeroOut = x .== 0 .|| y .== 0

        prod :: SInt (n+1)
        prod = sFromIntegral x * sFromIntegral y

        nv :: Int
        nv = fromIntegral $ natVal (Proxy @n)

        prodN, prodNm1 :: SBool
        prodN   = prod `sTestBit` nv
        prodNm1 = prod `sTestBit` (nv-1)

        overflow =   nonSignBitPos x + nonSignBitPos y .> literal (fromIntegral (nv - 2))
                 .|| prodN .<+> prodNm1

-- Text-book definition
textbook :: forall n. ( KnownNat n,      BVIsNonZero n
                      , KnownNat (n+n), BVIsNonZero (n+n)
                      ) => SInt n -> SInt n -> SBool
textbook x y = prod2N ./= sFromIntegral prodN
  where prod2N :: SInt (n+n)
        prod2N = sFromIntegral x * sFromIntegral y

        prodN :: SInt n
        prodN = x * y

test :: forall proxy n. ( KnownNat n,          BVIsNonZero n
                        , KnownNat (n+1),      BVIsNonZero (n+1)
                        , KnownNat (n+n),      BVIsNonZero (n+n)
                        , KnownNat (2+Log2 n), BVIsNonZero (2+Log2 n)
                        ) => proxy n -> Bool -> IO ()
test _ checkTextBook = do print =<< check "Against builtin"  bvMulO
                          when checkTextBook (print =<< check "Against textbook" textbook)
   where check w f = do putStrLn $ "Proving: " ++ w ++ ", N = " ++ show (natVal (Proxy @n))
                        proveWith bitwuzla{timing = PrintTiming} $ do
                          x <- sInt "x"
                          y <- sInt "y"
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
