-- 64-bit signed multiplication overflow detection using a 66-bit multiplier

{-# LANGUAGE DataKinds        #-}
{-# OPTIONS_GHC -Wall -Werror #-}

module Main where

import Data.SBV
import Data.SBV.Tools.Overflow
import GHC.TypeLits (KnownNat)

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
spec :: SInt 64 -> SInt 64 -> SBool
spec = bvMulO

-- Algorithm 2: use a 66 bit multiplier
alg66 :: SInt 64 -> SInt 64 -> SBool
alg66 x y = sNot zeroOut .&& overflow
  where m = position x
        n = position y

        zeroOut = x .== 0 .|| y .== 0

        prod :: SInt 66
        prod = sFromIntegral x * sFromIntegral y

        prod65, prod64, prod63 :: SBool
        prod65 = prod `sTestBit` 65
        prod64 = prod `sTestBit` 64
        prod63 = prod `sTestBit` 63

        prod6563 :: [SBool]
        prod6563 = [prod65, prod64, prod63]

        overflow =   ((m + n) .> 62)
                 .|| (    (prod6563 ./= [sFalse, sFalse, sFalse])
                      .&& (prod6563 ./= [sTrue,  sTrue,  sTrue ])
                     )

-- Algorithm 3: use a 65 bit multiplier
alg65 :: SInt 64 -> SInt 64 -> SBool
alg65 x y = sNot zeroOut .&& overflow
  where m = position x
        n = position y

        zeroOut = x .== 0 .|| y .== 0

        prod :: SInt 65
        prod = sFromIntegral x * sFromIntegral y

        prod64, prod63 :: SBool
        prod64 = prod `sTestBit` 64
        prod63 = prod `sTestBit` 63

        prod6463 :: [SBool]
        prod6463 = [prod64, prod63]

        overflow =   ((m + n) .> 62)
                 .|| (    (prod6463 ./= [sFalse, sFalse])
                      .&& (prod6463 ./= [sTrue,  sTrue ])
                     )

-- Algorithm 4: Text-book definition
textbook :: SInt 64 -> SInt 64 -> SBool
textbook x y = prod128 ./= sFromIntegral prod64
  where prod128 :: SInt 128
        prod128 = sFromIntegral x * sFromIntegral y

        prod64 :: SInt 64
        prod64 = x * y

-- Comparators
comp :: String -> (SInt 64 -> SInt 64 -> SBool) -> (SInt 64 -> SInt 64 -> SBool) -> IO ThmResult
comp w f g = do putStrLn $ "Proving: " ++ w ++ ":"
                proveWith bitwuzla{timing = PrintTiming} $ do
                  x <- sInt "x"
                  y <- sInt "x"
                  pure $ f x y .== g x y

main :: IO ()
main = do print =<< comp "Spec vs 66-bit mult"   spec  alg66
          print =<< comp "66-bit vs 65-bit mult" alg66 alg65
          print =<< comp "65-bit vs text-book"   alg65 textbook
