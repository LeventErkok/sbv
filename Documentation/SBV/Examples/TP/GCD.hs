-----------------------------------------------------------------------------
-- |
-- Module    : Documentation.SBV.Examples.TP.GCD
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Proving Euclidian GCD algorithm correct.
-----------------------------------------------------------------------------

{-# LANGUAGE CPP              #-}
{-# LANGUAGE DataKinds        #-}
{-# LANGUAGE TypeAbstractions #-}
{-# LANGUAGE TypeApplications #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module Documentation.SBV.Examples.TP.GCD where

import Prelude hiding (gcd)

import Data.SBV
import Data.SBV.TP
import Data.SBV.Tuple

#ifdef DOCTEST
-- $setup
-- >>> import Data.SBV.TP
#endif

-- * Calculating GCD

-- | @nGCD@ is the version of GCD that works on non-negative integers.
--
-- Ideally, we should make this function local to @gcd@, but then we can't refer to it explicitly in our proofs.
--
-- Note on maximality: Note that, by definition @gcd 0 0 = 0@. Since any number divides @0@,
-- there is no greatest common divisor for the pair @(0, 0)@. So, maximality here is meant
-- to be in terms of divisibility. That is, any divisor of @a@ and @b@ will also divide their @gcd@.
nGCD :: SInteger -> SInteger -> SInteger
nGCD = smtFunction "nGCD" $ \a b -> ite (b .== 0) a (nGCD b (a `sEMod` b))

-- | Generalized GCD, working for all integers. We simply call @nGCD@ with the absolute value of the arguments.
gcd :: SInteger -> SInteger -> SInteger
gcd a b = nGCD (abs a) (abs b)

-- * Basic properties

-- | \(\gcd\, a\ b \geq 0\)
--
-- ==== __Proof__
-- >>> runTP gcdNonNegative
-- Inductive lemma (strong): nonNegativeNGCD
--   Step: Measure is non-negative         Q.E.D.
--   Step: 1 (2 way case split)
--     Step: 1.1                           Q.E.D.
--     Step: 1.2.1                         Q.E.D.
--     Step: 1.2.2                         Q.E.D.
--     Step: 1.Completeness                Q.E.D.
--   Result:                               Q.E.D.
-- Lemma: nonNegative                      Q.E.D.
-- [Proven] nonNegative :: Ɐa ∷ Integer → Ɐb ∷ Integer → Bool
gcdNonNegative :: TP (Proof (Forall "a" Integer -> Forall "b" Integer -> SBool))
gcdNonNegative = do
     -- We first prove over nGCD, using strong induction with the measure @a+b@.
     nn <- sInduct "nonNegativeNGCD"
                   (\(Forall a) (Forall b) -> a .>= 0 .&& b .>= 0 .=> nGCD a b .>= 0)
                   (\_a b -> b) $
                   \ih a b -> [a .>= 0, b .>= 0]
                           |- cases [ b .== 0 ==> trivial
                                    , b ./= 0 ==> nGCD a b .>= 0
                                               =: nGCD b (a `sEMod` b) .>= 0
                                               ?? ih `at` (Inst @"a" b, Inst @"b" (a `sEMod` b))
                                               =: sTrue
                                               =: qed
                                    ]

     lemma "nonNegative"
           (\(Forall a) (Forall b) -> gcd a b .>= 0)
           [proofOf nn]

-- | \(\gcd\, a\ b=0\implies a=0\land b=0\)
--
-- ==== __Proof__
-- >>> runTP gcdZero
-- Inductive lemma (strong): nGCDZero
--   Step: Measure is non-negative         Q.E.D.
--   Step: 1 (2 way case split)
--     Step: 1.1                           Q.E.D.
--     Step: 1.2.1                         Q.E.D.
--     Step: 1.2.2                         Q.E.D.
--     Step: 1.Completeness                Q.E.D.
--   Result:                               Q.E.D.
-- Lemma: gcdZero                          Q.E.D.
-- [Proven] gcdZero :: Ɐa ∷ Integer → Ɐb ∷ Integer → Bool
gcdZero :: TP (Proof (Forall "a" Integer -> Forall "b" Integer -> SBool))
gcdZero = do

  -- First prove over nGCD:
  nGCDZero <-
    sInduct "nGCDZero"
            (\(Forall @"a" a) (Forall @"b" b) -> a .>= 0 .&& b .>= 0 .&& nGCD a b .== 0 .=> a .== 0 .&& b .== 0)
            (\_a b -> b) $
            \ih a b -> [a .>= 0, b .>= 0]
                    |- (nGCD a b .== 0 .=> a .== 0 .&& b .== 0)
                    =: cases [ b .== 0 ==> trivial
                             , b .>  0 ==> (nGCD b (a `sEMod` b) .== 0 .=> a .== 0 .&& b .== 0)
                                        ?? ih `at` (Inst @"a" b, Inst @"b" (a `sEMod` b))
                                        =: sTrue
                                        =: qed
                             ]

  lemma "gcdZero"
        (\(Forall @"a" a) (Forall @"b" b) -> gcd a b .== 0 .=> a .== 0 .&& b .== 0) 
        [proofOf nGCDZero]

-- | \(\gcd\, a\ b=\gcd\, b\ a\)
--
-- ==== __Proof__
-- >>> runTP commutative
-- Lemma: nGCDCommutative
--   Step: 1                               Q.E.D.
--   Result:                               Q.E.D.
-- Lemma: commutative
--   Step: 1                               Q.E.D.
--   Result:                               Q.E.D.
-- [Proven] commutative :: Ɐa ∷ Integer → Ɐb ∷ Integer → Bool
commutative :: TP (Proof (Forall "a" Integer -> Forall "b" Integer -> SBool))
commutative = do
    -- First prove over nGCD. Simple enough proof, but quantifiers and recursive functions
    -- cause z3 to diverge. So, we have to explicitly write it out.
    nGCDComm <-
        calc "nGCDCommutative"
             (\(Forall @"a" a) (Forall @"b" b) -> a .>= 0 .&& b .>= 0 .=> nGCD a b .== nGCD b a) $
             \a b -> [a .>= 0, b .>= 0]
                  |- nGCD a b
                  =: nGCD b a
                  =: qed

    -- It's unfortunate we have to spell this out explicitly, a simple lemma call
    -- that uses the above proof doesn't converge.
    calc "commutative"
          (\(Forall a) (Forall b) -> gcd a b .== gcd b a) $
          \a b -> [] |- gcd a b
                     ?? nGCDComm
                     =: gcd b a
                     =: qed

-- | \(\gcd\,(-a)\,b = \gcd\,a\,b = \gcd\,a\,(-b)\)
--
-- ==== __Proof__
-- >>> runTP negGCD
-- Lemma: negGCD                           Q.E.D.
-- [Proven] negGCD :: Ɐa ∷ Integer → Ɐb ∷ Integer → Bool
negGCD :: TP (Proof (Forall "a" Integer -> Forall "b" Integer -> SBool))
negGCD = lemma "negGCD" (\(Forall a) (Forall b) -> let g = gcd a b in gcd (-a) b .== g .&& g .== gcd a (-b)) []

-- | \( \gcd\,a\,0 = \gcd\,0\,a = |a| \land \gcd\,0\,0 = 0\)
--
-- ==== __Proof__
-- >>> runTP zeroGCD
-- Lemma: negGCD                           Q.E.D.
-- [Proven] negGCD :: Ɐa ∷ Integer → Bool
zeroGCD :: TP (Proof (Forall "a" Integer -> SBool))
zeroGCD = lemma "negGCD" (\(Forall a) -> gcd a 0 .== gcd 0 a .&& gcd 0 a .== abs a .&& gcd 0 0 .== 0) []

-- * Divisibility

-- | Divides relation. By definition we @0@ only divides @0@. (But every number divides @0@).
dvd :: SInteger -> SInteger -> SBool
a `dvd` b = ite (a .== 0) (b .== 0) (b `sEMod` a .== 0)

-- | \(a \mid |b| \iff a \mid b\)
--
-- A number divides another exactly when it also divides its absolute value. While this property
-- seems obvious, I was unable to get z3 to prove it. Even CVC5 needs a bit of help to guide it through
-- the case split on @b@.
--
-- ==== __Proof__
-- >>> runTP dvdAbs
-- Lemma: dvdAbs_l2r
--   Step: 1 (2 way case split)
--     Step: 1.1                           Q.E.D.
--     Step: 1.2                           Q.E.D.
--     Step: 1.Completeness                Q.E.D.
--   Result:                               Q.E.D.
-- Lemma: dvdAbs_r2l
--   Step: 1 (2 way case split)
--     Step: 1.1                           Q.E.D.
--     Step: 1.2                           Q.E.D.
--     Step: 1.Completeness                Q.E.D.
--   Result:                               Q.E.D.
-- Lemma: dvdAbs                           Q.E.D.
-- [Proven] dvdAbs :: Ɐa ∷ Integer → Ɐb ∷ Integer → Bool
dvdAbs :: TP (Proof (Forall "a" Integer -> Forall "b" Integer -> SBool))
dvdAbs = do
   l2r <- calcWith cvc5 "dvdAbs_l2r"
                   (\(Forall @"a" a) (Forall @"b" b) -> a `dvd` (abs b) .=> a `dvd` b) $
                   \a b -> [a `dvd` (abs b)]
                        |- cases [ b .<  0 ==> sTrue =: qed
                                 , b .>= 0 ==> sTrue =: qed
                                 ]

   r2l <- calcWith cvc5 "dvdAbs_r2l"
                   (\(Forall @"a" a) (Forall @"b" b) -> a `dvd` b .=> a `dvd` (abs b)) $
                   \a b -> [a `dvd` b]
                        |- cases [ b .<  0 ==> sTrue =: qed
                                 , b .>= 0 ==> sTrue =: qed
                                 ]

   lemma "dvdAbs"
         (\(Forall @"a" a) (Forall @"b" b) -> a `dvd` b .== a `dvd` (abs b))
         [proofOf l2r, proofOf r2l]

-- | \(d \mid a \implies d \mid k*a\)
--
-- ==== __Proof__
-- >>> runTP dvdMul
-- Lemma: dvdMul
--   Step: 1 (2 way case split)
--     Step: 1.1                           Q.E.D.
--     Step: 1.2                           Q.E.D.
--     Step: 1.Completeness                Q.E.D.
--   Result:                               Q.E.D.
-- [Proven] dvdMul :: Ɐd ∷ Integer → Ɐa ∷ Integer → Ɐk ∷ Integer → Bool
dvdMul :: TP (Proof (Forall "d" Integer -> Forall "a" Integer -> Forall "k" Integer -> SBool))
dvdMul = calc "dvdMul"
              (\(Forall d) (Forall a) (Forall k) -> d `dvd` a .=> d `dvd` (k*a)) $
              \d a k -> [d `dvd` a]
                     |- cases [ d .== 0 ==> d `dvd` (k*a)
                                         ?? a .== 0
                                         =: sTrue
                                         =: qed
                              , d ./= 0 ==> d `dvd` (k*a)
                                         ?? a .== d * a `sEDiv` d
                                         =: d `dvd` (k * d * a `sEDiv` d)
                                         =: qed
                              ]

-- | \(d \mid (2a + 1) \implies \mathrm{isOdd}(d)\)
--
-- ==== __Proof__
-- >>> runTP dvdOddThenOdd
-- Lemma: dvdOddThenOdd
--   Step: 1 (2 way case split)
--     Step: 1.1                           Q.E.D.
--     Step: 1.2.1                         Q.E.D.
--     Step: 1.2.2                         Q.E.D.
--     Step: 1.Completeness                Q.E.D.
--   Result:                               Q.E.D.
-- [Proven] dvdOddThenOdd :: Ɐd ∷ Integer → Ɐa ∷ Integer → Bool
dvdOddThenOdd :: TP (Proof (Forall "d" Integer -> Forall "a" Integer -> SBool))
dvdOddThenOdd = calc "dvdOddThenOdd"
                     (\(Forall d) (Forall a) -> d `dvd` (2*a+1) .=> isOdd d) $
                     \d a -> [d `dvd` (2*a+1)]
                          |- cases [ isOdd  d ==> trivial
                                   , isEven d ==> (2 * (d `sEDiv` 2)) `dvd` (2*a+1)
                                               =: 2 `dvd` (2*a+1)
                                               =: contradiction
                                   ]

-- | \(\mathrm{isOdd}(d) \land d \mid 2a \implies d \mid a\)
--
-- ==== __Proof__
-- >>> runTP dvdEvenWhenOdd
-- Lemma: dvdEvenWhenOdd
-- Lemma: dvdEvenWhenOdd
--   Step: 1                               Q.E.D.
--   Step: 2                               Q.E.D.
--   Step: 3                               Q.E.D.
--   Step: 4                               Q.E.D.
--   Step: 5                               Q.E.D.
--   Step: 6                               Q.E.D.
--   Step: 7                               Q.E.D.
--   Result:                               Q.E.D.
-- [Proven] dvdEvenWhenOdd :: Ɐd ∷ Integer → Ɐa ∷ Integer → Bool
dvdEvenWhenOdd :: TP (Proof (Forall "d" Integer -> Forall "a" Integer -> SBool))
dvdEvenWhenOdd = calc "dvdEvenWhenOdd"
                      (\(Forall d) (Forall a) -> isOdd d .&& d `dvd` (2*a) .=> d `dvd` a) $
                      \d a ->  [isOdd d, d `dvd` (2*a)]
                           |-> let t = (d - 1) `sEDiv` 2
                                   m = (2*a)   `sEDiv` d
                            in sTrue

                            -- Observe that d = 2t+1 and 2a = dm
                            =: d .== 2*t + 1 .&& 2*a .== d*m

                            -- So, 2a == (2t+1)m holds
                            =: 2*a .== (2*t+1) * m

                            -- Arithmetic gives us
                            =: 2*a .== 2*t*m + m .&& 2*(a-t*m) .== m

                            -- So, we now now m is even
                            =: 2 `sDivides` m

                            -- Give that divisor a name:
                            =: let n = m `sEDiv` 2

                            -- It follows that 2a = d(2n) = 2(dn)
                            in 2*a .== d * (2 * n) .&& 2 * a .== 2 * (d * n)

                            -- From which we can conclude a = dn
                            =: a .== d * n

                            -- Thus we can deduce d must divide a
                            =: d `dvd` a

                            -- Done!
                            =: qed

-- | \(d \mid a \land d \mid b \implies d \mid (a + b)\)
--
-- ==== __Proof__
-- >>> runTP dvdSum1
-- Lemma: dvdSum1
--   Step: 1 (2 way case split)
--     Step: 1.1                           Q.E.D.
--     Step: 1.2.1                         Q.E.D.
--     Step: 1.2.2                         Q.E.D.
--     Step: 1.2.3                         Q.E.D.
--     Step: 1.Completeness                Q.E.D.
--   Result:                               Q.E.D.
-- [Proven] dvdSum1 :: Ɐd ∷ Integer → Ɐa ∷ Integer → Ɐb ∷ Integer → Bool
dvdSum1 :: TP (Proof (Forall "d" Integer -> Forall "a" Integer -> Forall "b" Integer -> SBool))
dvdSum1 =
  calc "dvdSum1"
       (\(Forall d) (Forall a) (Forall b) -> d `dvd` a .&& d `dvd` b .=> d `dvd` (a + b)) $
       \d a b -> [d `dvd` a .&& d `dvd` b]
              |- cases [ a .== 0 .|| b .== 0 ==> trivial
                       , a ./= 0 .&& b ./= 0 ==> d `dvd` (a + b)
                                              =: d `dvd` (a `sEDiv` d * d + b `sEDiv` d * d)
                                              =: d `dvd` (d * (a `sEDiv` d + b `sEDiv` d))
                                              =: sTrue
                                              =: qed
                       ]

-- | \(d \mid (a + b) \land d \mid b \implies d \mid a \)
--
-- ==== __Proof__
-- >>> runTP dvdSum2
-- Lemma: dvdSum2
--   Step: 1 (2 way case split)
--     Step: 1.1                           Q.E.D.
--     Step: 1.2.1                         Q.E.D.
--     Step: 1.2.2                         Q.E.D.
--     Step: 1.2.3                         Q.E.D.
--     Step: 1.Completeness                Q.E.D.
--   Result:                               Q.E.D.
-- [Proven] dvdSum2 :: Ɐd ∷ Integer → Ɐa ∷ Integer → Ɐb ∷ Integer → Bool
dvdSum2 :: TP (Proof (Forall "d" Integer -> Forall "a" Integer -> Forall "b" Integer -> SBool))
dvdSum2 =
  calc "dvdSum2"
       (\(Forall d) (Forall a) (Forall b) -> d `dvd` (a + b) .&& d `dvd` b .=> d `dvd` a) $
       \d a b -> [d `dvd` (a + b) .&& d `dvd` b]
              |- cases [ d .== 0 ==> trivial
                       , d ./= 0 ==> let k1 = (a + b) `sEDiv` d
                                         k2 =      b  `sEDiv` d
                                     in a `sEDiv` d
                                     =: (a + b - b) `sEDiv` d
                                     =: (k1 * d - k2 * d) `sEDiv` d
                                     =: (k1 - k2) * d `sEDiv` d
                                     =: qed
                       ]

-- * Correctness of GCD

-- | \(\gcd\,a\,b \mid a \land \gcd\,a\,b \mid b\)
--
-- GCD of two numbers divide these numbers. This is part one of the proof, where we are
-- not concerned with maximality. Our goal is to show that the calculated gcd divides both inputs.
--
-- ==== __Proof__
-- >>> runTP gcdDivides
-- Lemma: dvdAbs                           Q.E.D.
-- Lemma: helper
--   Step: 1                               Q.E.D.
--   Result:                               Q.E.D.
-- Inductive lemma (strong): dvdNGCD
--   Step: Measure is non-negative         Q.E.D.
--   Step: 1 (2 way case split)
--     Step: 1.1                           Q.E.D.
--     Step: 1.2.1                         Q.E.D.
--     Step: 1.2.2                         Q.E.D.
--     Step: 1.Completeness                Q.E.D.
--   Result:                               Q.E.D.
-- Lemma: gcdDivides                       Q.E.D.
-- [Proven] gcdDivides :: Ɐa ∷ Integer → Ɐb ∷ Integer → Bool
gcdDivides :: TP (Proof (Forall "a" Integer -> Forall "b" Integer -> SBool))
gcdDivides = do

   dAbs <- recall "dvdAbs" dvdAbs

   -- Helper about divisibility. If x|b and x| a%b, then x|a.
   helper <- calc "helper"
                  (\(Forall @"a" a) (Forall @"b" b) (Forall @"x" x) ->
                           b ./= 0 .&& x `dvd` b .&& x `dvd` (a `sEMod` b)
                       .=> -----------------------------------------------
                                       x `dvd` a
                  ) $
                  \a b x -> [b ./= 0, x `dvd` b, x `dvd` (a `sEMod` b)]
                         |- x `dvd` a
                         ?? a `sEDiv` x .== (a `sEDiv` b) * (b `sEDiv` x) + (a `sEMod` b) `sEDiv` x
                         =: sTrue
                         =: qed

   -- Use strong induction to prove divisibility over non-negative numbers.
   dNGCD <- sInduct "dvdNGCD"
                     (\(Forall @"a" a) (Forall @"b" b) -> a .>= 0 .&& b .>= 0 .=> nGCD a b `dvd` a .&& nGCD a b `dvd` b)
                     (\_a b -> b) $
                     \ih a b -> [a .>= 0, b .>= 0]
                             |- let g = nGCD a b
                             in g `dvd` a .&& g `dvd` b
                             =: cases [ b .== 0 ==> trivial
                                      , b .>  0 ==> let g' = nGCD b (a `sEMod` b)
                                                 in g' `dvd` a .&& g' `dvd` b
                                                 ?? ih `at` (Inst @"a" b, Inst @"b" (a `sEMod` b))
                                                 ?? helper
                                                 =: sTrue
                                                 =: qed
                                      ]

   -- Now generalize to arbitrary integers.
   lemma"gcdDivides"
        (\(Forall a) (Forall b) -> gcd a b `dvd` a .&& gcd a b `dvd` b)
        [proofOf dAbs, proofOf dNGCD]

-- | \(x \mid a \land x \mid b \implies x \mid \gcd\,a\,b\)
--
-- Maximality. Any divisor of the inputs divides the GCD.
--
-- ==== __Proof__
-- >>> runTP gcdMaximal
-- Lemma: dvdAbs                           Q.E.D.
-- Lemma: eDiv                             Q.E.D.
-- Lemma: helper
--   Step: 1 (x `dvd` a && x `dvd` b)      Q.E.D.
--   Step: 2                               Q.E.D.
--   Step: 3                               Q.E.D.
--   Result:                               Q.E.D.
-- Inductive lemma (strong): mNGCD
--   Step: Measure is non-negative         Q.E.D.
--   Step: 1 (2 way case split)
--     Step: 1.1                           Q.E.D.
--     Step: 1.2.1                         Q.E.D.
--     Step: 1.2.2                         Q.E.D.
--     Step: 1.Completeness                Q.E.D.
--   Result:                               Q.E.D.
-- Lemma: gcdMaximal
--   Step: 1 (2 way case split)
--     Step: 1.1.1                         Q.E.D.
--     Step: 1.1.2                         Q.E.D.
--     Step: 1.2.1                         Q.E.D.
--     Step: 1.2.2                         Q.E.D.
--     Step: 1.Completeness                Q.E.D.
--   Result:                               Q.E.D.
-- [Proven] gcdMaximal :: Ɐa ∷ Integer → Ɐb ∷ Integer → Ɐx ∷ Integer → Bool
gcdMaximal :: TP (Proof (Forall "a" Integer -> Forall "b" Integer -> Forall "x" Integer -> SBool))
gcdMaximal = do

   dAbs  <- recall "dvdAbs" dvdAbs

   eDiv <- lemma "eDiv"
                 (\(Forall @"x" x) (Forall @"y" y) -> y ./= 0 .=> x .== (x `sEDiv` y) * y + x `sEMod` y)
                 []

   -- Helper: If x|a, x|b then x|a%b.
   helper <- calc "helper"
                  (\(Forall @"a" a) (Forall @"b" b) (Forall @"x" x) ->
                           x ./= 0 .&& b ./= 0 .&& x `dvd` a .&& x `dvd` b
                       .=> -----------------------------------------------
                                     x `dvd` (a `sEMod` b)
                  ) $
                  \a b x -> [x ./= 0, b ./= 0, x `dvd` a, x `dvd` b]
                         |- x `dvd` (a `sEMod` b)
                         ?? "x `dvd` a && x `dvd` b"
                         =: let k1 = a `sDiv` x
                                k2 = b `sDiv` x
                         in x `dvd` ((k1*x) `sEMod` (k2*x))
                         ?? eDiv `at` (Inst @"x" (k1*x), Inst @"y" (k2*x))
                         =: x `dvd` ((k1*x) - ((k1*x) `sEDiv` (k2*x)) * (k2*x))
                         =: sTrue
                         =: qed

   -- Now prove maximality for non-negative integers:
   mNGCD <- sInduct "mNGCD"
                    (\(Forall @"a" a) (Forall @"b" b) (Forall @"x" x) ->
                          a .>= 0 .&& b .>= 0 .&& x `dvd` a .&& x `dvd` b .=> x `dvd` nGCD a b)
                    (\_a b _x -> b) $
                    \ih a b x -> let g = nGCD a b
                              in [a .>= 0, b .>= 0, x `dvd` a .&& x `dvd` b]
                              |- x `dvd` g
                              =: cases [ b .== 0 ==> trivial
                                       , b .>  0 ==> x `dvd` nGCD b (a `sEMod` b)
                                                  ?? ih `at` (Inst @"a" b, Inst @"b" (a `sEMod` b), Inst @"x" x)
                                                  ?? helper
                                                  =: sTrue
                                                  =: qed
                                                  ]

   -- Generalize to arbitrary integers:
   calc "gcdMaximal"
        (\(Forall @"a" a) (Forall @"b" b) (Forall @"x" x) -> x `dvd` a .&& x `dvd` b .=> x `dvd` gcd a b) $
        \a b x -> [x `dvd` a, x `dvd` b]
               |- x `dvd` gcd a b
               =: cases [ abs a .>= abs b ==> x `dvd` nGCD (abs a) (abs b)
                                           ?? mNGCD    `at` (Inst @"a" (abs a), Inst @"b" (abs b), Inst @"x" x)
                                           ?? dAbs     `at` (Inst @"a" x, Inst @"b" a)
                                           ?? dAbs     `at` (Inst @"a" x, Inst @"b" b)
                                           =: sTrue
                                           =: qed
                        , abs a .<  abs b ==> x `dvd` nGCD (abs b) (abs a)
                                           ?? mNGCD    `at` (Inst @"a" (abs b), Inst @"b" (abs a), Inst @"x" x)
                                           ?? dAbs     `at` (Inst @"a" x, Inst @"b" a)
                                           ?? dAbs     `at` (Inst @"a" x, Inst @"b" b)
                                           =: sTrue
                                           =: qed
                        ]

-- | \(\gcd\,a\,b \mid a \land \gcd\,a\,b \mid b \land (x \mid a \land x \mid b \implies x \mid \gcd\,a\,b)\)
--
-- Putting it all together: GCD divides both arguments, and its maximal.
--
-- ==== __Proof__
-- >>> runTP gcdCorrect
-- Lemma: gcdDivides                       Q.E.D.
-- Lemma: gcdMaximal                       Q.E.D.
-- Lemma: gcdCorrect
--   Step: 1                               Q.E.D.
--   Step: 2                               Q.E.D.
--   Result:                               Q.E.D.
-- [Proven] gcdCorrect :: Ɐa ∷ Integer → Ɐb ∷ Integer → Bool
gcdCorrect :: TP (Proof (Forall "a" Integer -> Forall "b" Integer -> SBool))
gcdCorrect = do
  divides <- recall "gcdDivides" gcdDivides
  maximal <- recall "gcdMaximal" gcdMaximal

  calc "gcdCorrect"
       (\(Forall a) (Forall b) ->
             let g = gcd a b
          in  g `dvd` a
          .&& g `dvd` b
          .&& quantifiedBool (\(Forall x) -> x `dvd` a .&& x `dvd` b .=> x `dvd` g)
       ) $
       \a b -> []
            |- let g = gcd a b
                   m = quantifiedBool (\(Forall x) -> x `dvd` a .&& x `dvd` b .=> x `dvd` g)
            in g `dvd` a .&& g `dvd` b .&& m
            ?? divides `at` (Inst @"a" a, Inst @"b" b)
            =: m
            ?? maximal
            =: sTrue
            =: qed

-- | \(\bigl((a \neq 0 \lor b \neq 0) \land x \mid a \land x \mid b \bigr) \implies x \leq \gcd\,a\,b\)
--
-- Additionally prove that GCD is really maximum, i.e., it is the largest in the regular sense. Note
-- that we have to make an exception for @gcd 0 0@ since by definition the GCD is @0@, which is clearly
-- not the largest divisor of @0@ and @0@. (Since any number is a GCD for the pair @(0, 0)@, there is
-- no maximum.)
--
-- ==== __Proof__
-- >>> runTP gcdLargest
-- Lemma: gcdMaximal                       Q.E.D.
-- Lemma: gcdZero                          Q.E.D.
-- Lemma: gcdNonNegative                   Q.E.D.
-- Lemma: gcdLargest
--   Step: 1                               Q.E.D.
--   Step: 2                               Q.E.D.
--   Result:                               Q.E.D.
-- [Proven] gcdLargest :: Ɐa ∷ Integer → Ɐb ∷ Integer → Ɐx ∷ Integer → Bool
gcdLargest :: TP (Proof (Forall "a" Integer -> Forall "b" Integer -> Forall "x" Integer -> SBool))
gcdLargest = do
   maximal <- recall "gcdMaximal"     gcdMaximal
   zero    <- recall "gcdZero"        gcdZero
   nn      <- recall "gcdNonNegative" gcdNonNegative

   calc "gcdLargest"
        (\(Forall a) (Forall b) (Forall x) -> (a ./= 0 .|| b ./= 0) .&& x `dvd` a .&& x `dvd` b .=> x .<= gcd a b) $
        \a b x -> [(a ./= 0 .|| b ./= 0) .&& x `dvd` a, x `dvd` b]
               |- x .<= gcd a b
               ?? maximal `at` (Inst @"a" a, Inst @"b" b, Inst @"x" x)
               =: (x `dvd` gcd a b .=> x .<= gcd a b)
               ?? zero  `at` (Inst @"a" a, Inst @"b" b)
               ?? nn    `at` (Inst @"a" a, Inst @"b" b)
               =: sTrue
               =: qed

-- | \(\gcd\, a\, b = \gcd\, (a + b)\, b\)
--
-- ==== __Proof__
-- >>> runTP gcdAdd
-- Lemma: dvdSum1                          Q.E.D.
-- Lemma: dvdSum2                          Q.E.D.
-- Lemma: gcdDivides                       Q.E.D.
-- Lemma: gcdLargest                       Q.E.D.
-- Lemma: gcdAdd
--   Step: 1                               Q.E.D.
--   Step: 2                               Q.E.D.
--   Step: 3                               Q.E.D.
--   Step: 4                               Q.E.D.
--   Step: 5                               Q.E.D.
--   Step: 6                               Q.E.D.
--   Step: 7                               Q.E.D.
--   Result:                               Q.E.D.
-- [Proven] gcdAdd :: Ɐa ∷ Integer → Ɐb ∷ Integer → Bool
gcdAdd :: TP (Proof (Forall "a" Integer -> Forall "b" Integer -> SBool))
gcdAdd = do

   dSum1   <- recall "dvdSum1"    dvdSum1
   dSum2   <- recall "dvdSum2"    dvdSum2
   divides <- recall "gcdDivides" gcdDivides
   largest <- recall "gcdLargest" gcdLargest

   calc "gcdAdd"
        (\(Forall @"a" a) (Forall @"b" b) -> gcd a b .== gcd (a + b) b) $
        \a b -> [] |-> let g1 = gcd a       b
                           g2 = gcd (a + b) b
                    in sTrue

                    -- First use the divides property to conclude that g1 divides a and b
                    ?? divides `at` (Inst @"a" a, Inst @"b" b)
                    =: g1 `dvd` a .&& g1 `dvd` b

                    -- Same for g2 for a+b and b
                    ?? divides `at` (Inst @"a" (a + b), Inst @"b" b)
                    =: g2 `dvd` (a+b) .&& g2 `dvd` b

                    -- Use dSum1 to show g1 divides a+b
                    ?? dSum1 `at` (Inst @"d" g1, Inst @"a" a, Inst @"b" b)
                    =: g1 `dvd` (a+b)

                    -- Similarly, use dSum2 to show g2 divides a
                    ?? dSum2 `at` (Inst @"d" g2, Inst @"a" a, Inst @"b" b)
                    =:  g2 `dvd` a

                    -- Now use largest to show g1 >= g2
                    ?? largest `at` (Inst @"a" a,     Inst @"b" b, Inst @"x" g2)
                    =: g1 .>= g2

                    -- But again via largest, we can show g2 >= g1
                    ?? largest `at` (Inst @"a" (a+b), Inst @"b" b, Inst @"x" g1)
                    =: g2 .>= g1

                    -- Finally conclude g1 = g2, since both are greater-than-equal to each other:
                    =: g1 .== g2
                    =: qed

-- | \(\gcd\, 2a\, 2b = 2 \gcd\,a\, b\)
--
-- >>> runTP gcdEvenEven
-- Lemma: modEE                            Q.E.D.
-- Inductive lemma (strong): nGCDEvenEven
--   Step: Measure is non-negative         Q.E.D.
--   Step: 1 (2 way case split)
--     Step: 1.1                           Q.E.D.
--     Step: 1.2.1                         Q.E.D.
--     Step: 1.2.2                         Q.E.D.
--     Step: 1.2.3                         Q.E.D.
--     Step: 1.2.4                         Q.E.D.
--     Step: 1.Completeness                Q.E.D.
--   Result:                               Q.E.D.
-- Lemma: gcdEvenEven
--   Step: 1                               Q.E.D.
--   Step: 2                               Q.E.D.
--   Step: 3                               Q.E.D.
--   Step: 4                               Q.E.D.
--   Result:                               Q.E.D.
-- [Proven] gcdEvenEven :: Ɐa ∷ Integer → Ɐb ∷ Integer → Bool
gcdEvenEven :: TP (Proof (Forall "a" Integer -> Forall "b" Integer -> SBool))
gcdEvenEven = do

   modEE <- lemma "modEE"
                  (\(Forall @"a" a) (Forall @"b" b) -> b ./= 0 .=> (2 * a) `sEMod` (2 * b) .== 2 * (a `sEMod` b))
                  []

   nGCDEvenEven <- sInduct "nGCDEvenEven"
                           (\(Forall @"a" a) (Forall @"b" b) -> a .>= 0 .&& b .>= 0 .=> nGCD (2*a) (2*b) .== 2 * nGCD a b)
                           (\_a b -> b) $
                           \ih a b -> [a .>= 0, b .>= 0]
                                   |- nGCD (2*a) (2*b)
                                   =: cases [ b .== 0 ==> trivial
                                            , b ./= 0 ==> nGCD (2 * a) (2 * b)
                                                       =: nGCD (2 * b) ((2 * a) `sEMod` (2 * b))
                                                       ?? modEE `at` (Inst @"a" a, Inst @"b" b)
                                                       =: nGCD (2 * b) (2 * (a `sEMod` b))
                                                       ?? ih
                                                       =: 2 * nGCD a b
                                                       =: qed
                                         ]

   calc "gcdEvenEven"
        (\(Forall a) (Forall b) -> gcd (2*a) (2*b) .== 2 * gcd a b) $
        \a b -> [] |- gcd (2*a) (2*b)
                   =: nGCD (abs (2*a)) (abs (2*b))
                   =: nGCD (2 * abs a) (2 * abs b)
                   ?? nGCDEvenEven `at` (Inst @"a" (abs a), Inst @"b" (abs b))
                   =: 2 * nGCD (abs a) (abs b)
                   =: 2 * gcd a b
                   =: qed

-- | \(\gcd\, 2a+1\, 2b = \gcd\,2a+1\, b\)
--
-- >>> runTP gcdOddEven
-- TODO
gcdOddEven :: TP (Proof (Forall "a" Integer -> Forall "b" Integer -> SBool))
gcdOddEven = do

   divides      <- recall "gcdDivides"     gcdDivides
   largest      <- recall "gcdLargest"     gcdLargest
   dMul         <- recall "dvdMul"         dvdMul
   dOddThenOdd  <- recall "dvdOddThenOdd"  dvdOddThenOdd
   dEvenWhenOdd <- recall "dvdEvenWhenOdd" dvdEvenWhenOdd

   calc "gcdOddEven"
        (\(Forall a) (Forall b) -> gcd (2*a+1) (2*b) .== gcd (2*a+1) b) $
        \a b -> [] |-> let g1 = gcd (2*a+1) (2*b)
                           g2 = gcd (2*a+1) b
                   in sTrue

                   -- First use the divides property to conclude that g1 divides both 2*a+1 and 2*b
                   ?? divides `at` (Inst @"a" (2*a+1), Inst @"b" (2*b))
                   =: g1 `dvd` (2*a+1) .&& g1 `dvd` (2*b)

                   -- Same for g2, for 2*a+1 and b
                   ?? divides `at` (Inst @"a" (2*a+1), Inst @"b" b)
                   =: g2 `dvd` (2*a+1) .&& g2 `dvd` b

                   -- By arithmetic, g2 divides 2*b
                   ?? dMul `at` (Inst @"d" g2, Inst @"a" b, Inst @"k" 2)
                   =: g2 `dvd` (2*b)

                   -- Observe that g1 must be odd
                   ?? dOddThenOdd `at` (Inst @"d" g1, Inst @"a" a)
                   =: isOdd g1

                   -- Conclude that g1 must divide b
                   ?? dEvenWhenOdd `at` (Inst @"d" g1, Inst @"a" b)
                   =: g1 `dvd` b

                   -- Now use largest to show g1 >= g2
                   ?? largest `at` (Inst @"a" (2*a+1),  Inst @"b" (2*b), Inst @"x" g2)
                   =: g1 .>= g2

                   -- But again via largest, we can show g2 >= g1
                   ?? largest `at` (Inst @"a" (2*a+1), Inst @"b" b, Inst @"x" g1)
                   =: g2 .>= g1

                   -- Finally conclude g1 = g2 since both are greater-than-equal to each other:
                   =: g1 .== g2
                   =: qed

-- * GCD via subtraction

-- | @nGCDSub@ is the original verision of Euclid, which uses subtraction instead of modulus. This is the version that
-- works on non-negative numbers. It has the precondition that @a >= b >= 0@, and maintains this invariant in each
-- recursive call.
nGCDSub :: SInteger -> SInteger -> SInteger
nGCDSub = smtFunction "nGCDSub" $ \a b -> ite (a .== b) a
                                        $ ite (a .== 0) b
                                        $ ite (b .== 0) a
                                        $ ite (a .> b)  (nGCDSub (a - b) b)
                                                        (nGCDSub a (b - a))

-- | Generalized version of subtraction based GCD, working over all integers.
gcdSub :: SInteger -> SInteger -> SInteger
gcdSub a b = nGCDSub (abs a) (abs b)

-- | \(\mathrm{gcdSub}\, a\, b = \gcd\, a\, b\)
--
-- Instead of proving @gcdSub@ correct, we'll simply show that it is equivalent to @gcd@, hence it has
-- all the properties we already established.
--
-- ==== __Proof__
-- >>> runTP gcdSubEquiv
-- Lemma: commutative                      Q.E.D.
-- Lemma: gcdAdd                           Q.E.D.
-- Inductive lemma (strong): nGCDSubEquiv
--   Step: Measure is non-negative         Q.E.D.
--   Step: 1 (5 way case split)
--     Step: 1.1                           Q.E.D.
--     Step: 1.2                           Q.E.D.
--     Step: 1.3                           Q.E.D.
--     Step: 1.4.1                         Q.E.D.
--     Step: 1.4.2                         Q.E.D.
--     Step: 1.4.3                         Q.E.D.
--     Step: 1.5.1                         Q.E.D.
--     Step: 1.5.2                         Q.E.D.
--     Step: 1.5.3                         Q.E.D.
--     Step: 1.5.4                         Q.E.D.
--     Step: 1.5.5                         Q.E.D.
--     Step: 1.Completeness                Q.E.D.
--   Result:                               Q.E.D.
-- Lemma: gcdSubEquiv
--   Step: 1                               Q.E.D.
--   Step: 2                               Q.E.D.
--   Step: 3                               Q.E.D.
--   Result:                               Q.E.D.
-- [Proven] gcdSubEquiv :: Ɐa ∷ Integer → Ɐb ∷ Integer → Bool
gcdSubEquiv :: TP (Proof (Forall "a" Integer -> Forall "b" Integer -> SBool))
gcdSubEquiv = do

   -- We'll be using the commutativity of GCD and the gcdAdd property
   comm <- recall "commutative" commutative
   addG <- recall "gcdAdd"      gcdAdd

   -- First prove over the non-negative numbers:
   nEq <- sInduct "nGCDSubEquiv"
                  (\(Forall @"a" a) (Forall @"b" b) -> a .>= 0 .&& b .>= 0 .=> nGCDSub a b .== nGCD a b)
                  (\a b -> a + b) $
                  \ih a b -> [a .>= 0, b .>= 0]
                          |- nGCDSub a b
                          =: cases [ a .== b             ==> nGCD a b =: qed
                                   , a .== 0             ==> nGCD a b =: qed
                                   , b .== 0             ==> nGCD a b =: qed
                                   , a .> b  .&& b ./= 0 ==> nGCDSub (a - b) b
                                                          ?? ih
                                                          =: nGCD (a - b) b
                                                          ?? addG `at` (Inst @"a" (a - b), Inst @"b" b)
                                                          =: nGCD a b
                                                          =: qed
                                   , a .< b  .&& a ./= 0 ==> nGCDSub a (b - a)
                                                          ?? ih
                                                          =: nGCD a (b - a)
                                                          ?? comm
                                                          =: nGCD (b - a) a
                                                          ?? addG `at` (Inst @"a" (b - a), Inst @"b" a)
                                                          =: nGCD b a
                                                          ?? comm
                                                          =: nGCD a b
                                                          =: qed
                                   ]

   -- Now prove over all integers
   calcWith cvc5 "gcdSubEquiv"
         (\(Forall a) (Forall b) -> gcd a b .== gcdSub a b) $
         \a b -> [] |- gcd a b
                    =: nGCD (abs a) (abs b)
                    ?? nEq `at` (Inst @"a" (abs a), Inst @"b" (abs b))
                    =: nGCDSub (abs a) (abs b)
                    =: gcdSub a b
                    =: qed

-- * Binary GCD

-- | @nGCDBin@ is the binary GCD algorithm that works on non-negative numbers.
nGCDBin :: SInteger -> SInteger -> SInteger
nGCDBin = smtFunction "nGCDBin" $ \a b -> ite (a .== 0)               b
                                        $ ite (b .== 0)               a
                                        $ ite (isEven a .&& isEven b) (2 * nGCDBin (a `sEDiv` 2) (b `sEDiv` 2))
                                        $ ite (isOdd  a .&& isEven b) (    nGCDBin a             (b `sEDiv` 2))
                                        $ ite (a .<= b)               (    nGCDBin a             (b - a))
                                                                      (    nGCDBin (a - b)       b)
-- | Is the given integer even?
isEven :: SInteger -> SBool
isEven = (2 `sDivides`)

-- | Is the given integer odd?
isOdd :: SInteger -> SBool
isOdd  = sNot . isEven

-- | Generalized version that works on arbitrary integers.
gcdBin :: SInteger -> SInteger -> SInteger
gcdBin a b = nGCDBin (abs a) (abs b)

-- | \(\mathrm{gcdBin}\, a\, b = \gcd\, a\, b\)
--
-- Instead of proving @gcdBin@ correct, we'll simply show that it is equivalent to @gcd@, hence it has
-- all the properties we already established.
--
-- ==== __Proof__
-- >>> runTP gcdBinEquiv
-- TODO
gcdBinEquiv :: TP (Proof (Forall "a" Integer -> Forall "b" Integer -> SBool))
gcdBinEquiv = do
   gEvenEven <- recall "gcdEvenEven" gcdEvenEven
   gOddEven  <- recall "gcdOddEven"  gcdOddEven
   gAdd      <- recall "gcdAdd"      gcdAdd

   -- First prove over the non-negative numbers:
   nEq <- sInduct "nGCDBinEquiv"
                  (\(Forall @"a" a) (Forall @"b" b) -> a .>= 0 .&& b .>= 0 .=> nGCDBin a b .== nGCD a b)
                  (\a b -> tuple (a, b)) $
                  \ih a b -> [a .>= 0, b .>= 0]
                          |- nGCDBin a b
                          =: cases [ a .== 0               ==> trivial
                                   , b .== 0               ==> trivial
                                   , isEven a .&& isEven b ==> 2 * nGCDBin (a `sEDiv` 2) (b `sEDiv` 2)
                                                            ?? ih `at` (Inst @"a" (a `sEDiv` 2), Inst @"b" (b `sEDiv` 2))
                                                            =: 2 * nGCD (a `sEDiv` 2) (b `sEDiv` 2)
                                                            ?? a .== 2 * a `sEDiv` 2
                                                            ?? b .== 2 * b `sEDiv` 2
                                                            ?? gEvenEven `at` (Inst @"a" (a `sEDiv` 2), Inst @"b" (b `sEDiv` 2))
                                                            =: nGCD a b
                                                            =: qed
                                   , isOdd a  .&& isEven b ==> nGCDBin a (b `sEDiv` 2)
                                                            ?? ih `at` (Inst @"a" a, Inst @"b" (b `sEDiv` 2))
                                                            =: nGCD a (b `sEDiv` 2)
                                                            ?? a .== 2 * ((a-1) `sEDiv` 2) + 1
                                                            ?? b .== 2 * b `sEDiv` 2
                                                            ?? gOddEven `at` (Inst @"a" ((a-1) `sEDiv` 2), Inst @"b" (b `sEDiv` 2))
                                                            =: nGCD a b
                                                            =: qed
                                   , isOdd b               ==> cases [ a .== 0             ==> trivial
                                                                     , a ./= 0 .&& a .<= b ==> nGCDBin a b
                                                                                            =: nGCDBin a (b - a)
                                                                                            ?? ih `at` (Inst @"a" a, Inst @"b" (b - a))
                                                                                            =: nGCD a (b - a)
                                                                                            ?? sorry
                                                                                            =: nGCD a b
                                                                                            =: qed
                                                                     , a .>  b             ==> nGCDBin a b
                                                                                            =: nGCDBin (a - b) b
                                                                                            ?? ih `at` (Inst @"a" (a - b), Inst @"b" b)
                                                                                            =: nGCD (a - b) b
                                                                                            ?? gAdd `at` (Inst @"a" a, Inst @"b" (-b))
                                                                                            =: nGCD a b
                                                                                            =: qed
                                                                     ]
                                   ]

   -- Now prove over all integers
   calcWith cvc5 "gcdBinEquiv"
         (\(Forall a) (Forall b) -> gcd a b .== gcdBin a b) $
         \a b -> [] |- gcd a b
                    =: nGCD (abs a) (abs b)
                    ?? nEq `at` (Inst @"a" (abs a), Inst @"b" (abs b))
                    =: nGCDBin (abs a) (abs b)
                    =: gcdBin a b
                    =: qed
