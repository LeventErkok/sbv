-- 64-bit signed multiplication overflow detection using a 66-bit multiplier

{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE ExplicitNamespaces  #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# OPTIONS_GHC -Wall -Werror    #-}

module Main where

import Data.SBV
import Data.SBV.Tools.Overflow
import Data.Proxy
import GHC.TypeLits (KnownNat, type (+), natVal)

-- Find the position of the first non-sign bit. i.e., the first bit that differs from the msb.
-- Position is 0 indexed. Note that if there's no differing bit, then you also get back 0.
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
position :: (BVIsNonZero n, KnownNat n) => SInt n -> SWord8
position w = case blastBE w of
               []     -> error $ "Got no bits after blasing " ++ show w
               x : xs -> walk (.== sNot x) (literal (fromIntegral (length xs - 1))) xs
 where walk :: (SBool -> SBool) -> SWord8 -> [SBool] -> SWord8
       walk _check _i []     = 0
       walk  check  i (b:bs) = ite (check b) i (walk check (i-1) bs)

-- Algorithm 1: Builtin overflow detection
spec :: (BVIsNonZero n, KnownNat n) => SInt n -> SInt n -> SBool
spec = bvMulO

-- Algorithm 2: use a N+2 bit multiplier
algN2 :: forall n. (BVIsNonZero n, KnownNat n, BVIsNonZero (n+2), KnownNat (n+2)) => SInt n -> SInt n -> SBool
algN2 x y = sNot zeroOut .&& overflow
  where zeroOut = x .== 0 .|| y .== 0

        prod :: SInt (n+2)
        prod = sFromIntegral x * sFromIntegral y

        nv :: Int
        nv = fromIntegral $ natVal (Proxy @n)

        prodNp1, prodN, prodNm1 :: SBool
        prodNp1 = prod `sTestBit` (nv+1)
        prodN   = prod `sTestBit` nv
        prodNm1 = prod `sTestBit` (nv-1)

        prodTop3 :: [SBool]
        prodTop3 = [prodNp1, prodN, prodNm1]

        overflow =   ((position x + position y) .> literal (fromIntegral (nv - 2)))
                 .|| (    (prodTop3 ./= [sFalse, sFalse, sFalse])
                      .&& (prodTop3 ./= [sTrue,  sTrue,  sTrue ])
                     )

-- Algorithm 3: use an N+1 bit multiplier
algN1 :: forall n. (BVIsNonZero n, KnownNat n, BVIsNonZero (n+1), KnownNat (n+1)) => SInt n -> SInt n -> SBool
algN1 x y = sNot zeroOut .&& overflow
  where zeroOut = x .== 0 .|| y .== 0

        prod :: SInt (n+1)
        prod = sFromIntegral x * sFromIntegral y

        nv :: Int
        nv = fromIntegral $ natVal (Proxy @n)

        prodN, prodNm1 :: SBool
        prodN   = prod `sTestBit` nv
        prodNm1 = prod `sTestBit` (nv-1)

        prodTop2 :: [SBool]
        prodTop2 = [prodN, prodNm1]

        overflow =   ((position x + position y) .> literal (fromIntegral (nv - 2)))
                 .|| (    (prodTop2 ./= [sFalse, sFalse])
                      .&& (prodTop2 ./= [sTrue,  sTrue ])
                     )

-- Algorithm 4: Text-book definition
textbook :: forall n. (BVIsNonZero n, KnownNat n, BVIsNonZero (n+n), KnownNat (n+n)) => SInt n -> SInt n -> SBool
textbook x y = prod2N ./= sFromIntegral prodN
  where prod2N :: SInt (n+n)
        prod2N = sFromIntegral x * sFromIntegral y

        prodN :: SInt n
        prodN = x * y

-- Comparators
comp :: forall n. (BVIsNonZero n, KnownNat n) => String -> (SInt n -> SInt n -> SBool) -> (SInt n -> SInt n -> SBool) -> IO ThmResult
comp w f g = do putStrLn $ "Proving: " ++ w ++ ", N = " ++ show (natVal (Proxy @n))
                proveWith bitwuzla{timing = PrintTiming} $ do
                  x <- sInt "x"
                  y <- sInt "x"
                  pure $ f x y .== g x y

runAll :: forall n. (BVIsNonZero n, KnownNat n) => (SInt n -> SInt n -> SBool) -> (SInt n -> SInt n -> SBool) -> (SInt n -> SInt n -> SBool) -> IO ()
runAll specF n2F n1F = do print =<< comp ("Spec vs " ++ n2 ++ "-bit mult")       specF n2F
                          print =<< comp (n2 ++ "-bit vs " ++ n1 ++ "-bit mult") n2F   n1F
                          print =<< comp (n1 ++ "-bit vs text-book")             n1F   specF
   where n  = natVal (Proxy @n)
         n1 = show $ n+1
         n2 = show $ n+2

run :: forall proxy n. (KnownNat n, BVIsNonZero n, KnownNat (n+1), BVIsNonZero (n+1), KnownNat (n+2), BVIsNonZero (n+2)) => proxy n -> IO ()
run _ = runAll @n spec algN2 algN1

main :: IO ()
main = do run (Proxy @8)
          run (Proxy @16)
          run (Proxy @24)
          run (Proxy @32)
