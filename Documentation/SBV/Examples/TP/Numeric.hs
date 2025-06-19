-----------------------------------------------------------------------------
-- |
-- Module    : Documentation.SBV.Examples.TP.Numeric
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Example use of inductive TP proofs, over integers.
-----------------------------------------------------------------------------

{-# LANGUAGE CPP                 #-}
{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE QuasiQuotes         #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeAbstractions    #-}
{-# LANGUAGE TypeApplications    #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module Documentation.SBV.Examples.TP.Numeric where

import Prelude hiding (sum, map, product, length, (^), replicate)

import Data.SBV
import Data.SBV.TP
import Data.SBV.List

#ifdef DOCTEST
-- $setup
-- >>> :set -XScopedTypeVariables
-- >>> import Data.SBV
-- >>> import Data.SBV.TP
-- >>> import Control.Exception
#endif

-- * Sum of constants

-- | Prove that sum of constants @c@ from @0@ to @n@ is @n*c@.
--
-- We have:
--
-- >>> runTP $ sumConstProof (uninterpret "c")
-- Inductive lemma: sumConst_correct
--   Step: Base                            Q.E.D.
--   Step: 1                               Q.E.D.
--   Step: 2                               Q.E.D.
--   Step: 3                               Q.E.D.
--   Step: 4                               Q.E.D.
--   Result:                               Q.E.D.
-- [Proven] sumConst_correct :: Ɐn ∷ Integer → Bool
sumConstProof :: SInteger -> TP (Proof (Forall "n" Integer -> SBool))
sumConstProof c = induct "sumConst_correct"
                         (\(Forall n) -> n .>= 0 .=> sum (replicate n c) .== c * n) $
                         \ih n -> [n .>= 0] |- sum (replicate (n+1) c)
                                            =: sum (c .: replicate n c)
                                            =: c + sum (replicate n c)
                                            ?? ih
                                            =: c + c*n
                                            =: c*(n+1)
                                            =: qed

-- * Sum of numbers

-- | Prove that sum of numbers from @0@ to @n@ is @n*(n-1)/2@.
--
-- >>> runTP sumProof
-- Inductive lemma: sum_correct
--   Step: Base                            Q.E.D.
--   Step: 1                               Q.E.D.
--   Step: 2                               Q.E.D.
--   Step: 3                               Q.E.D.
--   Result:                               Q.E.D.
-- [Proven] sum_correct :: Ɐn ∷ Integer → Bool
sumProof :: TP (Proof (Forall "n" Integer -> SBool))
sumProof = induct "sum_correct"
                  (\(Forall n) -> n .>= 0 .=> sum [sEnum|n, n-1 .. 0|] .== (n * (n+1)) `sEDiv` 2) $
                  \ih n -> [n .>= 0] |- sum [sEnum|n+1, n .. 0|]
                                     =: n+1 + sum [sEnum|n, n-1 .. 0|]
                                     ?? ih
                                     =: n+1 + (n * (n+1)) `sEDiv` 2
                                     =: ((n+1) * (n+2)) `sEDiv` 2
                                     =: qed

-- * Sum of squares of numbers
--
-- | Prove that sum of square of numbers from @0@ to @n@ is @n*(n+1)*(2n+1)/6@.
--
-- >>> runTP sumSquareProof
-- Inductive lemma: sumSquare_correct
--   Step: Base                            Q.E.D.
--   Step: 1                               Q.E.D.
--   Step: 2                               Q.E.D.
--   Step: 3                               Q.E.D.
--   Step: 4                               Q.E.D.
--   Step: 5                               Q.E.D.
--   Step: 6                               Q.E.D.
--   Result:                               Q.E.D.
-- [Proven] sumSquare_correct :: Ɐn ∷ Integer → Bool
sumSquareProof :: TP (Proof (Forall "n" Integer -> SBool))
sumSquareProof = do
   let sq :: SInteger -> SInteger
       sq k = k * k

       sumSquare n = sum $ map sq $ [sEnum|n, n-1 .. 0|]

   induct "sumSquare_correct"
          (\(Forall n) -> n .>= 0 .=> sumSquare n .== (n*(n+1)*(2*n+1)) `sEDiv` 6) $
          \ih n -> [n .>= 0] |- sumSquare (n+1)
                             =: sum (map sq [sEnum|n+1, n .. 0|])
                             =: sum (map sq (n+1 .: [sEnum|n, n-1 .. 0|]))
                             =: sum ((n+1)*(n+1) .: map sq [sEnum|n, n-1 .. 0|])
                             =: (n+1)*(n+1) + sum (map sq [sEnum|n, n-1 .. 0|])
                             ?? ih
                             =: (n+1)*(n+1) + (n*(n+1)*(2*n+1)) `sEDiv` 6
                             =: ((n+1)*(n+2)*(2*n+3)) `sEDiv` 6
                             =: qed

-- * Sum of cubes of numbers

-- | Prove that sum of cube of numbers from @0@ to @n@ is sum of numbers up to @n@ squared.
-- This is attributed to Nicomachus, hence the name.
--
-- We have:
--
-- >>> runTP nicomachus
-- Inductive lemma: sum_correct
--   Step: Base                            Q.E.D.
--   Step: 1                               Q.E.D.
--   Step: 2                               Q.E.D.
--   Step: 3                               Q.E.D.
--   Result:                               Q.E.D.
-- Lemma: evenHalfSquared                  Q.E.D.
-- Inductive lemma: nn1IsEven
--   Step: Base                            Q.E.D.
--   Step: 1                               Q.E.D.
--   Step: 2                               Q.E.D.
--   Step: 3                               Q.E.D.
--   Result:                               Q.E.D.
-- Lemma: sum_squared
--   Step: 1                               Q.E.D.
--   Step: 2                               Q.E.D.
--   Result:                               Q.E.D.
-- Inductive lemma: nicomachus
--   Step: Base                            Q.E.D.
--   Step: 1                               Q.E.D.
--   Step: 2                               Q.E.D.
--   Result:                               Q.E.D.
-- [Proven] nicomachus :: Ɐn ∷ Integer → Bool
nicomachus :: TP (Proof (Forall "n" Integer -> SBool))
nicomachus = do
   let (^) :: SInteger -> Integer -> SInteger
       _ ^ 0 = 1
       b ^ n = b * b ^ (n-1)
       infixr 8 ^

       sumCubed :: SInteger -> SInteger
       sumCubed = smtFunction "sumCubed" $ \n -> ite (n .<= 0) 0 (n^3 + sumCubed (n - 1))

   -- Grab the proof of regular summation formula
   sp <- sumProof

   -- Square of the summation result. This is a trivial lemma for humans, but there are lots
   -- of multiplications involved making the problem non-linear and we need to spell it out.
   ssp <- do
        -- Squaring half of an even number? You can square the number and divide by 4 instead:
        -- z3 can prove this out of the box, but without it being explicitly expressed, the
        -- following proof doesn't go through.
        evenHalfSquared <- lemma "evenHalfSquared"
                                 (\(Forall n) -> 2 `sDivides` n .=> (n `sEDiv` 2) ^ 2 .== (n ^ 2) `sEDiv` 4)
                                 []

        -- The multiplication @n * (n+1)@ is always even. It's surprising that I had to use induction here
        -- but neither z3 nor cvc5 can converge on this out-of-the-box.
        nn1IsEven <- induct "nn1IsEven"
                            (\(Forall n) -> n .>= 0 .=> 2 `sDivides` (n * (n+1))) $
                            \ih n -> [n .>= 0] |- 2 `sDivides` ((n+1) * (n+2))
                                               =: 2 `sDivides` (n*(n+1) + 2*(n+1))
                                               =: 2 `sDivides` (n*(n+1))
                                               ?? ih
                                               =: sTrue
                                               =: qed

        calc "sum_squared"
               (\(Forall @"n" n) -> n .>= 0 .=> sum [sEnum|n, n-1 .. 0|] ^ 2 .== (n^2 * (n+1)^2) `sEDiv` 4) $
               \n -> [n .>= 0] |- sum [sEnum|n, n-1 .. 0|] ^ 2
                               ?? sp `at` Inst @"n" n
                               =: ((n * (n+1)) `sEDiv` 2)^2
                               ?? nn1IsEven `at` Inst @"n" n
                               ?? evenHalfSquared `at` Inst @"n" (n * (n+1))
                               =: ((n * (n+1))^2) `sEDiv` 4
                               =: qed

   -- We can finally put it together:
   induct "nicomachus"
          (\(Forall n) -> n .>= 0 .=> sumCubed n .== sum [sEnum|n, n-1 .. 0|] ^ 2) $
          \ih n -> [n .>= 0]
                |- sumCubed (n+1)
                =: (n+1)^3 + sumCubed n
                ?? ih
                ?? ssp
                =: sum [sEnum|n+1, n .. 0|] ^ 2
                =: qed

-- * Exponents and divisibility by 7

-- | Prove that @11^n - 4^n@ is always divisible by 7.
--
-- NB. As of Feb 2025, z3 struggles with the inductive step in this proof, but cvc5 performs just fine.
--
-- We have:
--
-- >>> runTP elevenMinusFour
-- Lemma: powN                             Q.E.D.
-- Inductive lemma: elevenMinusFour
--   Step: Base                            Q.E.D.
--   Step: 1                               Q.E.D.
--   Step: 2                               Q.E.D.
--   Step: 3                               Q.E.D.
--   Step: 4                               Q.E.D.
--   Step: 5                               Q.E.D.
--   Step: 6                               Q.E.D.
--   Step: 7                               Q.E.D.
--   Step: 8                               Q.E.D.
--   Result:                               Q.E.D.
-- [Proven] elevenMinusFour :: Ɐn ∷ Integer → Bool
elevenMinusFour :: TP (Proof (Forall "n" Integer -> SBool))
elevenMinusFour = do
   let pow :: SInteger -> SInteger -> SInteger
       pow = smtFunction "pow" $ \x y -> ite (y .== 0) 1 (x * pow x (y - 1))

       emf :: SInteger -> SBool
       emf n = 7 `sDivides` (11 `pow` n - 4 `pow` n)

   -- helper
   powN <- lemma "powN" (\(Forall x) (Forall n) -> n .>= 0 .=> x `pow` (n+1) .== x * x `pow` n) []

   inductWith cvc5 "elevenMinusFour"
          (\(Forall n) -> n .>= 0 .=> emf n) $
          \ih n -> [n .>= 0]
                |- emf (n+1)
                =: 7 `sDivides` (11 `pow` (n+1) - 4 `pow` (n+1))
                ?? powN `at` (Inst @"x" 11, Inst @"n" n)
                =: 7 `sDivides` (11 * 11 `pow` n - 4 `pow` (n+1))
                ?? powN `at` (Inst @"x" 4, Inst @"n" n)
                =: 7 `sDivides` (11 * 11 `pow` n - 4 * 4 `pow` n)
                =: 7 `sDivides` (7 * 11 `pow` n + 4 * 11 `pow` n - 4 * 4 `pow` n)
                =: 7 `sDivides` (7 * 11 `pow` n + 4 * (11 `pow` n - 4 `pow` n))
                ?? ih
                =: let x = some "x" (\v -> 7*v .== 11 `pow` n - 4 `pow` n)   -- Apply the IH and grab the witness for it
                in 7 `sDivides` (7 * 11 `pow` n + 4 * 7 * x)
                =: 7 `sDivides` (7 * (11 `pow` n + 4 * x))
                =: sTrue
                =: qed

-- * A proof about factorials

-- | @sum (map (\k -> k * k!) [0 .. n]) == (n+1)! - 1@
--
-- >>> runTP sumMulFactorial
-- Lemma: fact (n+1)
--   Step: 1                               Q.E.D.
--   Step: 2                               Q.E.D.
--   Step: 3                               Q.E.D.
--   Step: 4                               Q.E.D.
--   Result:                               Q.E.D.
-- Inductive lemma: sumMulFactorial
--   Step: Base                            Q.E.D.
--   Step: 1                               Q.E.D.
--   Step: 2                               Q.E.D.
--   Step: 3                               Q.E.D.
--   Step: 4                               Q.E.D.
--   Step: 5                               Q.E.D.
--   Step: 6                               Q.E.D.
--   Step: 7                               Q.E.D.
--   Result:                               Q.E.D.
-- [Proven] sumMulFactorial :: Ɐn ∷ Integer → Bool
sumMulFactorial :: TP (Proof (Forall "n" Integer -> SBool))
sumMulFactorial = do
  let fact :: SInteger -> SInteger
      fact n = product [sEnum|n, n-1 .. 1|]

  -- This is pure expansion, but without it z3 struggles in the next lemma.
  helper <- calc "fact (n+1)"
                 (\(Forall n) -> n .>= 0 .=> fact (n+1) .== (n+1) * fact n) $
                 \n -> [n .>= 0] |- fact (n+1)
                                 =: product [sEnum|n+1, n .. 1|]
                                 =: product (n+1 .: [sEnum|n, n-1 .. 1|])
                                 =: (n+1) * product [sEnum|n, n-1 .. 1|]
                                 =: (n+1) * fact n
                                 =: qed

  induct "sumMulFactorial"
         (\(Forall n) -> n .>= 0 .=> sum (map (\k -> k * fact k) [sEnum|n, n-1 .. 0|]) .== fact (n+1) - 1) $
         \ih n -> [n .>= 0] |- sum (map (\k -> k * fact k) [sEnum|n+1, n .. 0|])
                            =: sum (map (\k -> k * fact k) (n+1 .: [sEnum|n, n-1 .. 0|]))
                            =: sum ((n+1) * fact (n+1) .: map (\k -> k * fact k) [sEnum|n, n-1 .. 0|])
                            =: (n+1) * fact (n+1) + sum (map (\k -> k * fact k) [sEnum|n, n-1 .. 0|])
                            ?? ih
                            =: (n+1) * fact (n+1) + fact (n+1) - 1
                            =: ((n+1) + 1) * fact (n+1) - 1
                            =: (n+2) * fact (n+1) - 1
                            ?? helper `at` Inst @"n" (n+1)
                            =: fact (n+2) - 1
                            =: qed

-- * A negative example

-- | The regular inductive proof on integers (i.e., proving at @0@, assuming at @n@ and proving at
-- @n+1@ will not allow you to conclude things when @n < 0@. The following example demonstrates this with the most
-- obvious example:
--
-- >>> badNonNegative `catch` (\(_ :: SomeException) -> pure ())
-- Inductive lemma: badNonNegative
--   Step: Base                            Q.E.D.
--   Step: 1
-- *** Failed to prove badNonNegative.1.
-- Falsifiable. Counter-example:
--   n = -2 :: Integer
badNonNegative :: IO ()
badNonNegative = runTP $ do
    _ <- induct "badNonNegative"
                (\(Forall @"n" (n :: SInteger)) -> n .>= 0) $
                \ih n -> [] |- n + 1 .>= 0
                            ?? ih
                            =: sTrue
                            =: qed
    pure ()
