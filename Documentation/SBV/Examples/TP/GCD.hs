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

-- * Correctness of GCD

-- | \(\gcd\,a\,b \mid a \land \gcd\,a\,b \mid b\)
--
-- GCD of two numbers divide these numbers. This is part one of the proof, where we are
-- not concerned with maximality. Our goal is to show that the calculated gcd divides both inputs.
--
-- ==== __Proof__
-- >>> runTP gcdDivides
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

   dAbs <- dvdAbs

   -- Helper about divisibility. If @x | b@ and @x | a%b@, then @x | a@.
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

   dAbs  <- dvdAbs

   eDiv <- lemma "eDiv"
                 (\(Forall @"x" x) (Forall @"y" y) -> y ./= 0 .=> x .== (x `sEDiv` y) * y + x `sEMod` y)
                 []

   -- Helper: If @x | a@, @x | b@ then @x | a%b@.
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
-- Lemma: gcdCorrect
--   Step: 1                               Q.E.D.
--   Step: 2                               Q.E.D.
--   Result:                               Q.E.D.
-- [Proven] gcdCorrect :: Ɐa ∷ Integer → Ɐb ∷ Integer → Bool
gcdCorrect :: TP (Proof (Forall "a" Integer -> Forall "b" Integer -> SBool))
gcdCorrect = do
  divides <- gcdDivides
  maximal <- gcdMaximal

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
-- Inductive lemma (strong): nGCDZero
--   Step: Measure is non-negative         Q.E.D.
--   Step: 1 (2 way case split)
--     Step: 1.1                           Q.E.D.
--     Step: 1.2.1                         Q.E.D.
--     Step: 1.2.2                         Q.E.D.
--     Step: 1.Completeness                Q.E.D.
--   Result:                               Q.E.D.
-- Lemma: gcdZero                          Q.E.D.
-- Inductive lemma (strong): nonNegativeNGCD
--   Step: Measure is non-negative         Q.E.D.
--   Step: 1 (2 way case split)
--     Step: 1.1                           Q.E.D.
--     Step: 1.2.1                         Q.E.D.
--     Step: 1.2.2                         Q.E.D.
--     Step: 1.Completeness                Q.E.D.
--   Result:                               Q.E.D.
-- Lemma: nonNegative                      Q.E.D.
-- Lemma: gcdLargest
--   Step: 1                               Q.E.D.
--   Step: 2                               Q.E.D.
--   Result:                               Q.E.D.
-- [Proven] gcdLargest :: Ɐa ∷ Integer → Ɐb ∷ Integer → Ɐx ∷ Integer → Bool
gcdLargest :: TP (Proof (Forall "a" Integer -> Forall "b" Integer -> Forall "x" Integer -> SBool))
gcdLargest = do
   maximal <- gcdMaximal
   zero    <- gcdZero
   nn      <- gcdNonNegative

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

-- | \(\gcd\, a\, b = \mathrm{gcdSub}\, a\, b\)
--
-- Instead of proving @gcdSub@ correct, we'll simply show that it is equivalent to @gcd@, hence it has
-- all the properties we already established.
--
-- >>> runTP gcdSubEquiv
gcdSubEquiv :: TP (Proof (Forall "a" Integer -> Forall "b" Integer -> SBool))
gcdSubEquiv = do
   modSub <- calc "modSub"
                  (\(Forall @"a" a) (Forall @"b" b) -> a .> b .&& b .> 0 .=> a `sEMod` b .== (a - b) `sEMod` b) $
                  \a b -> [a .> b, b .> 0]
                       |- a `sEMod` b
                       =: (b * a `sEDiv` b + a `sEMod` b) `sEMod` b
                       =: qed

   comm <-
     sInduct "ngcdSubComm"
             (\(Forall @"a" a) (Forall @"b" b) -> a .>= 0 .&& b .>= 0 .=> nGCDSub a b .== nGCDSub b a)
             (\a b -> a + b) $
             \ih a b -> [a .>= 0, b .>= 0]
                     |- nGCDSub a b
                     ?? ih `at` (Inst @"a" (a - b), Inst @"b" b)
                     ?? ih `at` (Inst @"a" a, Inst @"b" (b - a))
                     =: nGCDSub b a
                     =: qed

   -- Helper relating the subtraction to modulus in nGCDSub
   ngcdSubMod <-
     sInduct "ngcdSubMod"
             (\(Forall @"a" a) (Forall @"b" b) -> a .>= 0 .&& b .> 0 .=> nGCDSub a b .== nGCDSub (a `sEMod` b) b)
             (\a b -> a + b) $
             \ih a b -> [a .>= 0, b .> 0]
                     |- nGCDSub a b
                     =: cases [ a .== b ==> nGCDSub (a `sEMod` b) b =: qed
                              , a .== 0 ==> nGCDSub (a `sEMod` b) b =: qed
                              , a .> b  ==> nGCDSub (a - b) b
                                         ?? ih `at` (Inst @"a" (a - b), Inst @"b" b)
                                         =: nGCDSub ((a - b) `sEMod` b) b
                                         ?? modSub `at` (Inst @"a" a, Inst @"b" b)
                                         =: nGCDSub (a `sEMod` b) b
                                         =: qed
                              , a .<  b ==> nGCDSub a (b - a)
                                         ?? ih `at` (Inst @"a" a, Inst @"b" (b - a))
                                         =: nGCDSub (a `sEMod` (b - a)) (b - a)
                                         ?? sorry
                                         =: nGCDSub (a `sEMod` b) b
                                         =: qed
                              ]

   -- First prove over the non-negative numbers:
   nEq <- sInduct "nGCDSubEquiv"
                  (\(Forall @"a" a) (Forall @"b" b) -> a .>= 0 .&& b .>= 0 .=> nGCD a b .== nGCDSub a b)
                  (\_a b -> b) $
                  \ih a b -> [a .>= 0, b .>= 0]
                          |- nGCD a b
                          =: cases [ a .== b .|| b .== 0 ==> nGCDSub a b =: qed
                                   , a ./= b .&& b ./= 0 ==> nGCD b (a `sEMod` b)
                                                          ?? ih
                                                          =: nGCDSub b (a `sEMod` b)
                                                          ?? comm `at` (Inst @"a" b, Inst @"b" (a `sEMod` b))
                                                          =: nGCDSub (a `sEMod` b) b
                                                          ?? ngcdSubMod
                                                          =: nGCDSub a b
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
