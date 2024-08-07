-- N-bit signed multiplication overflow detection using a N+1 bit multiplier

{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE ExplicitNamespaces  #-}
{-# OPTIONS_GHC -Wall -Werror    #-}

module Main(main) where

import Data.SBV
import Data.SBV.Tools.Overflow (bvMulO)

import Data.Proxy
import GHC.TypeLits (KnownNat, type (+), natVal)

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
approxLog :: (BVIsNonZero n, KnownNat n) => SInt n -> SWord8
approxLog w = case blastBE w of
                []     -> error $ "Impossible happened: Got no bits after blasing " ++ show w
                x : xs -> walk (.== sNot x) (literal (fromIntegral (length xs - 1))) xs
 where walk :: (SBool -> SBool) -> SWord8 -> [SBool] -> SWord8
       walk _check _i []     = 0
       walk  check  i (b:bs) = ite (check b) i (walk check (i-1) bs)

-- Algorithm using an N+1 bit multiplier
bvsmulO :: forall n. (BVIsNonZero n, KnownNat n, BVIsNonZero (n+1), KnownNat (n+1)) => SInt n -> SInt n -> SBool
bvsmulO x y = sNot zeroOut .&& overflow
  where zeroOut = x .== 0 .|| y .== 0

        prod :: SInt (n+1)
        prod = sFromIntegral x * sFromIntegral y

        nv :: Int
        nv = fromIntegral $ natVal (Proxy @n)

        prodN, prodNm1 :: SBool
        prodN   = prod `sTestBit` nv
        prodNm1 = prod `sTestBit` (nv-1)

        overflow =   ((approxLog x + approxLog y) .> literal (fromIntegral (nv - 2)))
                 .|| (prodN .<+> prodNm1)

-- Text-book definition
textbook :: forall n. (BVIsNonZero n, KnownNat n, BVIsNonZero (n+n), KnownNat (n+n)) => SInt n -> SInt n -> SBool
textbook x y = prod2N ./= sFromIntegral prodN
  where prod2N :: SInt (n+n)
        prod2N = sFromIntegral x * sFromIntegral y

        prodN :: SInt n
        prodN = x * y

test :: forall proxy n. (BVIsNonZero n, KnownNat n, BVIsNonZero (n+1), KnownNat (n+1), BVIsNonZero (n+n), KnownNat (n+n)) => proxy n -> IO ()
test _ = do print =<< check "Against builtin"  bvMulO
            print =<< check "Against textbook" textbook
   where check w f = do putStrLn $ "Proving: " ++ w ++ ", N = " ++ show (natVal (Proxy @n))
                        proveWith bitwuzla $ do
                          x <- sInt "x"
                          y <- sInt "x"
                          pure $ f x y .== (bvsmulO :: SInt n -> SInt n -> SBool) x y

main :: IO ()
main = do test (Proxy @1)
          test (Proxy @2)
          test (Proxy @3)
          test (Proxy @4)
          test (Proxy @5)
          test (Proxy @6)
          test (Proxy @7)
          test (Proxy @8)
          test (Proxy @16)
          test (Proxy @24)
          -- run (Proxy @32)   -- Takes about 2 minutes
