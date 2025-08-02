-----------------------------------------------------------------------------
-- |
-- Module    : Documentation.SBV.Examples.TP.GCD
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Proving Euclid's GCD algorithm correct.
-----------------------------------------------------------------------------

{-# LANGUAGE DataKinds        #-}
{-# LANGUAGE TypeAbstractions #-}
{-# LANGUAGE TypeApplications #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module Documentation.SBV.Examples.TP.GCD where

import Prelude hiding (gcd)

import Data.SBV
import Data.SBV.TP

-- nGCD a b: Precondition a .>= b .&& b .>= 0. It also maintains this invariant in each recursive call.
-- Ideally, we should make this function local to gcd, but then we can't refer to it explicitly in our proofs.
--
-- Note on maximality: Since we defined @gcd 0 0 = 0@, and since any number divides @0@,
-- there is no greatest common divisor for the pair @(0, 0)@. So, maximality here is meant
-- to be in terms of divisibility. That is, any divisor of `a` and `b` will also divide their gcd.
nGCD :: SInteger -> SInteger -> SInteger
nGCD = smtFunction "nGCD" $ \a b -> ite (b .== 0) a (nGCD b (a `sEMod` b))

-- Generalized version over all integers
gcd :: SInteger -> SInteger -> SInteger
gcd = smtFunction "gcd" $ \a b -> let aa = abs a
                                      ab = abs b
                                  in ite (aa .>= ab) (nGCD aa ab) (nGCD ab aa)

-- | >>> runTP nonNegative
-- TODO
nonNegative :: TP (Proof (Forall "a" Integer -> Forall "b" Integer -> SBool))
nonNegative = do
     nn <- sInduct "nonNegativeNGCD"
                   (\(Forall a) (Forall b) -> a .>= b .&& b .>= 0 .=> nGCD a b .>= 0)
                   (\a b -> a + b) $
                   \ih a b -> [a .>= b, b .>= 0]
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

-- | >>> runTP commutative
-- TODO
commutative :: TP (Proof (Forall "a" Integer -> Forall "b" Integer -> SBool))
commutative = lemma "commutative" (\(Forall a) (Forall b) -> gcd a b .== gcd b a) []

-- Divides relation. 0 divides 0 only
dvd :: SInteger -> SInteger -> SBool
a `dvd` b = ite (a .== 0) (b .== 0) (b `sEMod` a .== 0)

-- | If a number divides another, then it also divides its absolute value.
-- z3 is unable to prove this. Even cvc5 needs a bit of help.
--
-- >>> runTP dvdAbs
-- TODO
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

-- | >>> runTP gcdDivides
-- TODO
gcdDivides :: TP (Proof (Forall "a" Integer -> Forall "b" Integer -> SBool))
gcdDivides = do

   dAbs <- dvdAbs

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

   dNGCD <- sInduct "dvdNGCD"
                     (\(Forall @"a" a) (Forall @"b" b) -> a .>= b .&& b .>= 0 .=> nGCD a b `dvd` a .&& nGCD a b `dvd` b)
                     (\a b -> a + b) $
                     \ih a b -> [a .>= b, b .>= 0]
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

   lemma"gcdDivides"
        (\(Forall a) (Forall b) -> gcd a b `dvd` a .&& gcd a b `dvd` b)
        [proofOf dAbs, proofOf dNGCD]

-- | >>> runTP gcdMaximal
-- TODO
gcdMaximal :: TP (Proof (Forall "a" Integer -> Forall "b" Integer -> Forall "x" Integer -> SBool))
gcdMaximal = do

   dAbs  <- dvdAbs

   eDiv <- lemma "eDiv"
                 (\(Forall @"x" x) (Forall @"y" y) -> y ./= 0 .=> x .== (x `sEDiv` y) * y + x `sEMod` y)
                 []

   helper <- calc "helper"
                  (\(Forall @"a" a) (Forall @"b" b) (Forall @"x" x) ->
                       x ./= 0 .&& b ./= 0 .&& x `dvd` a .&& x `dvd` b .=> x `dvd` (a `sEMod` b)) $
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

   mNGCD <- sInduct "mNGCD"
                    (\(Forall @"a" a) (Forall @"b" b) (Forall @"x" x) ->
                          a .>= b .&& b .>= 0 .&& x `dvd` a .&& x `dvd` b .=> x `dvd` nGCD a b)
                    (\a b _x -> a + b) $
                    \ih a b x -> let g = nGCD a b
                              in [a .>= b, b .>= 0, x `dvd` a .&& x `dvd` b]
                              |- x `dvd` g
                              =: cases [ b .== 0 ==> trivial
                                       , b .>  0 ==> x `dvd` nGCD b (a `sEMod` b)
                                                  ?? ih `at` (Inst @"a" b, Inst @"b" (a `sEMod` b), Inst @"x" x)
                                                  ?? helper
                                                  =: sTrue
                                                  =: qed
                                                  ]

   gcdMatch <- lemma "gcdMatch"
                     (\(Forall @"a" a) (Forall @"b" b)
                                -> let aa = abs a
                                       ab = abs b
                                   in gcd a b .== ite (aa .>= ab) (nGCD aa ab) (nGCD ab aa))
                     []

   calc "gcdMaximal"
        (\(Forall @"a" a) (Forall @"b" b) (Forall @"x" x) -> x `dvd` a .&& x `dvd` b .=> x `dvd` gcd a b) $
        \a b x -> [x `dvd` a, x `dvd` b]
               |- x `dvd` gcd a b
               =: cases [ abs a .>= abs b ==> x `dvd` nGCD (abs a) (abs b)
                                           ?? mNGCD    `at` (Inst @"a" (abs a), Inst @"b" (abs b), Inst @"x" x)
                                           ?? gcdMatch `at` (Inst @"a"      a,  Inst @"b"      b)
                                           ?? dAbs     `at` (Inst @"a" x, Inst @"b" a)
                                           ?? dAbs     `at` (Inst @"a" x, Inst @"b" b)
                                           =: sTrue
                                           =: qed
                        , abs a .<  abs b ==> x `dvd` nGCD (abs b) (abs a)
                                           ?? mNGCD    `at` (Inst @"a" (abs b), Inst @"b" (abs a), Inst @"x" x)
                                           ?? gcdMatch `at` (Inst @"a"      a,  Inst @"b"      b)
                                           ?? dAbs     `at` (Inst @"a" x, Inst @"b" a)
                                           ?? dAbs     `at` (Inst @"a" x, Inst @"b" b)
                                           =: sTrue
                                           =: qed
                        ]

-- | >>> runTP gcdCorrect
-- TODO
--
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
