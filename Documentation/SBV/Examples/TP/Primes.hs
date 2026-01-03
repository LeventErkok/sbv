-----------------------------------------------------------------------------
-- |
-- Module    : Documentation.SBV.Examples.TP.Primes
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Prove that there are an infinite number of primes. Along the way we formalize
-- and prove a number of properties about divisibility as well. Our proof is inspired by
-- the ACL2 proof in <https://github.com/acl2/acl2/blob/master/books/projects/numbers/euclid.lisp>.
-----------------------------------------------------------------------------

{-# LANGUAGE CPP              #-}
{-# LANGUAGE DataKinds        #-}
{-# LANGUAGE TypeAbstractions #-}
{-# LANGUAGE TypeApplications #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module Documentation.SBV.Examples.TP.Primes where

import Data.SBV
import Data.SBV.TP

#ifdef DOCTEST
-- $setup
-- >>> import Data.SBV.TP
#endif

-- * Divisibility

-- | Divides relation. By definition @0@ only divides @0@. (But every number divides @0@).
dvd :: SInteger -> SInteger -> SBool
x `dvd` y = ite (x .== 0) (y .== 0) (y `sEMod` x .== 0)

-- | \(x \mid y \implies x \mid y * z\)
--
-- === __Proof__
-- >>> runTP dividesProduct
-- Lemma: dividesProduct
--   Step: 1 (2 way case split)
--     Step: 1.1                           Q.E.D.
--     Step: 1.2.1                         Q.E.D.
--     Step: 1.2.2                         Q.E.D.
--     Step: 1.2.3                         Q.E.D.
--     Step: 1.Completeness                Q.E.D.
--   Result:                               Q.E.D.
-- [Proven] dividesProduct :: Ɐx ∷ Integer → Ɐy ∷ Integer → Ɐz ∷ Integer → Bool
dividesProduct :: TP (Proof (Forall "x" Integer -> Forall "y" Integer -> Forall "z" Integer -> SBool))
dividesProduct = calc "dividesProduct"
                      (\(Forall x) (Forall y) (Forall z) -> x `dvd` y .=> x `dvd` (y*z)) $
                      \x y z -> [x `dvd` y]
                             |- cases [ x .== 0 ==> x `dvd` (y*z)
                                                 ?? y .== 0
                                                 =: sTrue
                                                 =: qed
                                      , x ./= 0 ==> x `dvd` (y*z)
                                                 ?? y .== x * y `sEDiv` x
                                                 =: x `dvd` ((x * y `sEDiv` x) * z)
                                                 =: x `dvd` (x * ((y `sEDiv` x) * z))
                                                 =: sTrue
                                                 =: qed
                                      ]
-- | \(x \mid y \land y \mid z \implies x \mid z\)
--
-- === __Proof__
-- >>> runTP dividesTransitive
-- Lemma: dividesProduct                   Q.E.D.
-- Lemma: dividesTransitive
--   Step: 1 (2 way case split)
--     Step: 1.1                           Q.E.D.
--     Step: 1.2.1                         Q.E.D.
--     Step: 1.2.2                         Q.E.D.
--     Step: 1.2.3                         Q.E.D.
--     Step: 1.2.4                         Q.E.D.
--     Step: 1.Completeness                Q.E.D.
--   Result:                               Q.E.D.
-- [Proven] dividesTransitive :: Ɐx ∷ Integer → Ɐy ∷ Integer → Ɐz ∷ Integer → Bool
dividesTransitive :: TP (Proof (Forall "x" Integer -> Forall "y" Integer -> Forall "z" Integer -> SBool))
dividesTransitive = do
    dp <- recall "dividesProduct" dividesProduct

    calc "dividesTransitive"
         (\(Forall x) (Forall y) (Forall z) -> x `dvd` y .&& y `dvd` z .=> x `dvd` z) $
         \x y z -> [x `dvd` y, y `dvd` z]
                |- cases [ x .== 0 .|| y .== 0 .|| z .== 0 ==> trivial
                         , x ./= 0 .&& y ./= 0 .&& z ./= 0
                            ==> x `dvd` z
                             ?? z .== z `sEDiv` y * y
                             =: x `dvd` (z `sEDiv` y * y)
                             ?? y .== y `sEDiv` x * x
                             =: x `dvd` ((z `sEDiv` y) * (y `sEDiv` x * x))
                             =: x `dvd` (x * ((z `sEDiv` y) * (y `sEDiv` x)))
                             ?? dp `at` (Inst @"x" x, Inst @"y" x, Inst @"z" ((z `sEDiv` y) * (y `sEDiv` x)))
                             =: sTrue
                             =: qed
                         ]

-- * The least divisor

-- | The definition of primality will depend on the notion of least divisor. Given @k@ and @n@, the least-divisor of
-- @n@ that is at least @k@ is the number that is at least @k@ and divides @n@ evenly. The idea is that a number is
-- prime if the least divisor starting from @2@ is itself.
ld :: SInteger -> SInteger -> SInteger
ld = smtFunction "ld" $ \k n -> ite (n `sEMod` k .== 0) k (ld (k+1) n)

-- | \(1 < k \leq n \implies \mathit{ld}\,k\,n \mid n \land k \leq \mathit{ld}\,k\,n \leq n\)
--
-- === __Proof__
-- >>> runTP leastDivisorDivides
-- Inductive lemma (strong): leastDivisorDivides
--   Step: Measure is non-negative         Q.E.D.
--   Step: 1 (2 way case split)
--     Step: 1.1                           Q.E.D.
--     Step: 1.2                           Q.E.D.
--     Step: 1.Completeness                Q.E.D.
--   Result:                               Q.E.D.
-- [Proven] leastDivisorDivides :: Ɐk ∷ Integer → Ɐn ∷ Integer → Bool
leastDivisorDivides :: TP (Proof (Forall "k" Integer -> Forall "n" Integer -> SBool))
leastDivisorDivides =
   sInduct "leastDivisorDivides"
           (\(Forall k) (Forall n) -> 1 .< k .&& k .<= n .=> let d = ld k n in d `dvd` n .&& k .<= d .&& d .<= n)
           (\k n -> n - k, []) $
           \ih k n -> [1 .< k, k .<= n]
                  |- let d = ld k n
                  in cases [ n `sEMod` k .== 0 ==> d `dvd` n .&& k .<= d .&& d .<= n
                                                ?? d .== k
                                                =: sTrue
                                                =: qed
                           , n `sEMod` k ./= 0 ==> d `dvd` n .&& k .<= d .&& d .<= n
                                                ?? d .== ld (k+1) n
                                                ?? ih
                                                =: sTrue
                                                =: qed
                           ]

-- | \(1 < k \leq n \land d \mid n \land k \leq d \implies \mathit{ld}\,k\,n \leq d\)
--
-- === __Proof__
-- >>> runTP leastDivisorIsLeast
-- Inductive lemma (strong): leastDivisorisLeast
--   Step: Measure is non-negative         Q.E.D.
--   Step: 1 (2 way case split)
--     Step: 1.1                           Q.E.D.
--     Step: 1.2                           Q.E.D.
--     Step: 1.Completeness                Q.E.D.
--   Result:                               Q.E.D.
-- [Proven] leastDivisorisLeast :: Ɐk ∷ Integer → Ɐn ∷ Integer → Ɐd ∷ Integer → Bool
leastDivisorIsLeast :: TP (Proof (Forall "k" Integer -> Forall "n" Integer -> Forall "d" Integer -> SBool))
leastDivisorIsLeast =
  sInduct "leastDivisorisLeast"
          (\(Forall k) (Forall n) (Forall d) -> 1 .< k .&& k .<= n .&& d `dvd` n .&& k .<= d .=> ld k n .<= d)
          (\k n _d -> n - k, []) $
          \ih k n d -> [1 .< k, k .<= n, d `dvd` n, k .<= d]
                    |- cases [ n `sEMod` k .== 0 ==> ld k n .<= d
                                                  =: k .<= d
                                                  =: qed
                             , n `sEMod` k ./= 0 ==> ld k n .<= d
                                                  ?? ih
                                                  =: sTrue
                                                  =: qed
                             ]

-- | \(n \geq k \geq 2 \implies \mathit{ld}\,k\,(\mathit{ld}\,k\,n) = \mathit{ld}\,k\,n\)
--
-- === __Proof__
-- >>> runTP leastDivisorTwice
-- Lemma: dividesTransitive                Q.E.D.
-- Lemma: leastDivisorDivides              Q.E.D.
-- Lemma: leastDivisorIsLeast              Q.E.D.
-- Lemma: helper1                          Q.E.D.
-- Lemma: helper2                          Q.E.D.
-- Lemma: helper3                          Q.E.D.
-- Lemma: helper4                          Q.E.D.
-- Lemma: helper5
--   Step: 1                               Q.E.D.
--   Result:                               Q.E.D.
-- Lemma: leastDivisorTwice                Q.E.D.
-- [Proven] leastDivisorTwice :: Ɐk ∷ Integer → Ɐn ∷ Integer → Bool
leastDivisorTwice :: TP (Proof (Forall "k" Integer -> Forall "n" Integer -> SBool))
leastDivisorTwice = do
  dt  <- recall "dividesTransitive"   dividesTransitive
  ldd <- recall "leastDivisorDivides" leastDivisorDivides
  ldl <- recall "leastDivisorIsLeast" leastDivisorIsLeast

  h1 <- lemma "helper1"
              (\(Forall @"k" k) (Forall @"n" n) -> n .>= k .&& k .>= 2 .=> ld k (ld k n) `dvd` ld k n .&& ld k (ld k n) .<= ld k n)
              [proofOf ldd]

  h2 <- lemma "helper2"
              (\(Forall @"k" k) (Forall @"n" n) -> n .>= k .&& k .>= 2 .=> ld k n `dvd` n)
              [proofOf ldd]

  h3 <- lemma "helper3"
              (\(Forall @"k" k) (Forall @"n" n) -> n .>= k .&& k .>= 2 .=> ld k (ld k n) `dvd` n)
              [proofOf h1, proofOf h2, proofOf dt]

  h4 <- lemma "helper4"
              (\(Forall @"k" k) (Forall @"n" n) -> n .>= k .&& k .>= 2 .=> k .<= ld k (ld k n))
              [proofOf ldd]

  h5 <- calc "helper5"
              (\(Forall @"k" k) (Forall @"n" n) -> n .>= k .&& k .>= 2 .=> ld k n .<= ld k (ld k n)) $
              \k n -> [n .>= k, k .>= 2]
                   |- ld k n .<= ld k (ld k n)
                   ?? h3  `at` (Inst @"k" k, Inst @"n" n)
                   ?? h4  `at` (Inst @"k" k, Inst @"n" n)
                   ?? ldl `at` (Inst @"k" k, Inst @"n" n, Inst @"d" (ld k (ld k n)))
                   =: sTrue
                   =: qed

  lemma "leastDivisorTwice"
        (\(Forall k) (Forall n) -> n .>= k .&& k .>= 2 .=> ld k (ld k n) .== ld k n)
        [proofOf h1, proofOf h5]

-- * Primality

-- | A number is prime if its least divisor greater than or equal to @2@ is itself.
isPrime :: SInteger -> SBool
isPrime n = n .>= 2 .&& ld 2 n .== n

-- | \(\mathit{isPrime}\,p \implies p \geq 2\)
--
-- === __Proof__
-- >>> runTP primeAtLeast2
-- Lemma: primeAtLeast2                    Q.E.D.
-- [Proven] primeAtLeast2 :: Ɐp ∷ Integer → Bool
primeAtLeast2 :: TP (Proof (Forall "p" Integer -> SBool))
primeAtLeast2 = lemma "primeAtLeast2" (\(Forall p) -> isPrime p .=> p .>= 2) []

-- | \(n \geq 2 \implies \mathit{isPrime}\,(\mathit{ld}\,2\,n)\)
--
-- === __Proof__
-- >>> runTP leastDivisorIsPrime
-- Lemma: leastDivisorTwice                Q.E.D.
-- Lemma: leastDivisorDivides              Q.E.D.
-- Lemma: leastDivisorIsPrime
--   Step: 1                               Q.E.D.
--   Result:                               Q.E.D.
-- [Proven] leastDivisorIsPrime :: Ɐn ∷ Integer → Bool
leastDivisorIsPrime :: TP (Proof (Forall "n" Integer -> SBool))
leastDivisorIsPrime = do
   ldt <- recall "leastDivisorTwice" leastDivisorTwice
   ldd <- recall "leastDivisorDivides" leastDivisorDivides

   calc "leastDivisorIsPrime"
        (\(Forall n) -> n .>= 2 .=> isPrime (ld 2 n)) $
        \n -> [n .>= 2] |- isPrime (ld 2 n)
                        ?? ldt `at` (Inst @"k" 2, Inst @"n" n)
                        ?? ldd `at` (Inst @"k" 2, Inst @"n" n)
                        =: sTrue
                        =: qed

-- | The least prime divisor is the least divisor of it starting from @2@. By 'leastDivisorIsPrime', this number
-- is guaranteed to be prime.
leastPrimeDivisor :: SInteger -> SInteger
leastPrimeDivisor n = ld 2 n

-- * Formalizing factorial

-- | The factorial function.
fact :: SInteger -> SInteger
fact = smtFunction "fact" $ \n -> ite (n .<= 0) 1 (n * fact (n - 1))

-- | \(n! \geq 1\)
--
-- === __Proof__
-- >>> runTP factAtLeast1
-- Inductive lemma: factAtLeast1
--   Step: Base                            Q.E.D.
--   Step: 1 (2 way case split)
--     Step: 1.1                           Q.E.D.
--     Step: 1.2.1                         Q.E.D.
--     Step: 1.2.2                         Q.E.D.
--     Step: 1.Completeness                Q.E.D.
--   Result:                               Q.E.D.
-- [Proven] factAtLeast1 :: Ɐn ∷ Integer → Bool
factAtLeast1 :: TP (Proof (Forall "n" Integer -> SBool))
factAtLeast1 = inductWith cvc5 "factAtLeast1"
                      (\(Forall n) -> fact n .>= 1) $
                      \ih n -> [] |- fact (n+1) .>= 1
                                  =: cases [ n+1 .<= 0 ==> trivial
                                           , n+1 .>  0 ==> (n+1) * fact n .>= 1
                                                        ?? ih
                                                        =: sTrue
                                                        =: qed
                                           ]

-- | \(1 \leq k \land k \leq n \implies k \mid n!\)
--
-- === __Proof__
-- >>> runTP dividesFact
-- Lemma: dividesProduct                   Q.E.D.
-- Inductive lemma: dividesFact
--   Step: Base                            Q.E.D.
--   Step: 1                               Q.E.D.
--   Step: 2 (2 way case split)
--     Step: 2.1.1                         Q.E.D.
--     Step: 2.1.2                         Q.E.D.
--     Step: 2.2.1                         Q.E.D.
--     Step: 2.2.2                         Q.E.D.
--     Step: 2.Completeness                Q.E.D.
--   Result:                               Q.E.D.
-- [Proven] dividesFact :: Ɐn ∷ Integer → Ɐk ∷ Integer → Bool
dividesFact :: TP (Proof (Forall "n" Integer -> Forall "k" Integer -> SBool))
dividesFact = do
   dvp <- recall "dividesProduct" dividesProduct

   induct "dividesFact"
          (\(Forall n) (Forall k) -> 1 .<= k .&& k .<= n .=> k `dvd` fact n) $
          \ih n k -> [1 .<= k, k .<= n + 1]
                  |- k `dvd` fact (n + 1)
                  =: k `dvd` ((n + 1) * fact n)
                  =: cases [ k .== n + 1 ==> k `dvd` ((n + 1) * fact n)
                                          ?? dvp `at` (Inst @"x" k, Inst @"y" (n+1), Inst @"z" (fact n))
                                          =: sTrue
                                          =: qed
                           , k ./= n + 1 ==> k `dvd` ((n + 1) * fact n)
                                          ?? ih
                                          ?? dvp `at` (Inst @"x" k, Inst @"y" (fact n), Inst @"z" (n+1))
                                          =: sTrue
                                          =: qed
                           ]

-- | \(1 \leq k \land k \leq n \implies \neg (k \mid n! + 1)\)
--
-- === __Proof__
-- >>> runTP notDividesFactP1
-- Lemma: dividesFact                      Q.E.D.
-- Lemma: notDividesFactP1
--   Step: 1                               Q.E.D.
--   Step: 2                               Q.E.D.
--   Step: 3                               Q.E.D.
--   Result:                               Q.E.D.
-- [Proven] notDividesFactP1 :: Ɐn ∷ Integer → Ɐk ∷ Integer → Bool
notDividesFactP1 :: TP (Proof (Forall "n" Integer -> Forall "k" Integer -> SBool))
notDividesFactP1 = do
   df    <- recall "dividesFact"  dividesFact

   calc "notDividesFactP1"
         (\(Forall n) (Forall k) -> 1 .< k .&& k .<= n .=> sNot (k `dvd` (fact n + 1))) $
         \n k -> [1 .< k, k .<= n]
              |- k `dvd` (fact n + 1)
              ?? df `at` (Inst @"n" n, Inst @"k" k)
              =: k `dvd` (k * fact n `sEDiv` k + 1)
              =: k `dvd` 1
              =: contradiction

-- * Finding a greater prime

-- | Given a number, return another number which is both prime and is larger than the input. Note that
-- we don't claim to return the closest prime to the input. Just some prime that is larger, as we shall prove.
greaterPrime :: SInteger -> SInteger
greaterPrime n = leastPrimeDivisor (1 + fact n)

-- | \(\mathit{greaterPrime}\, n \mid n! + 1\)
--
-- === __Proof__
-- >>> runTP greaterPrimeDivides
-- Lemma: leastDivisorDivides              Q.E.D.
-- Lemma: factAtLeast1                     Q.E.D.
-- Lemma: greaterPrimeDivides
--   Step: 1                               Q.E.D.
--   Step: 2                               Q.E.D.
--   Step: 3                               Q.E.D.
--   Result:                               Q.E.D.
-- [Proven] greaterPrimeDivides :: Ɐn ∷ Integer → Bool
greaterPrimeDivides :: TP (Proof (Forall "n" Integer -> SBool))
greaterPrimeDivides = do
   ldd  <- recall "leastDivisorDivides" leastDivisorDivides
   fal1 <- recall "factAtLeast1"        factAtLeast1

   calc "greaterPrimeDivides"
        (\(Forall n) -> greaterPrime n `dvd` (1 + fact n)) $
        \n -> [] |- greaterPrime n `dvd` (1 + fact n)
                 =: leastPrimeDivisor (1 + fact n) `dvd` (1 + fact n)
                 =: ld 2 (1 + fact n) `dvd` (1 + fact n)
                 ?? ldd  `at` (Inst @"k" 2, Inst @"n" (1 + fact n))
                 ?? fal1 `at` Inst @"n" n
                 =: sTrue
                 =: qed

-- | \(\mathit{greaterPrime}\, n > n\)
--
-- === __Proof__
-- >>> runTP greaterPrimeGreater
-- Lemma: notDividesFactP1                 Q.E.D.
-- Lemma: greaterPrimeDivides              Q.E.D.
-- Lemma: leastDivisorIsPrime              Q.E.D.
-- Lemma: factAtLeast1                     Q.E.D.
-- Lemma: primeAtLeast2                    Q.E.D.
-- Lemma: greaterPrimeGreater
--   Step: 1                               Q.E.D.
--   Step: 2                               Q.E.D.
--   Step: 3                               Q.E.D.
--   Step: 4                               Q.E.D.
--   Step: 5                               Q.E.D.
--   Step: 6                               Q.E.D.
--   Result:                               Q.E.D.
-- [Proven] greaterPrimeGreater :: Ɐn ∷ Integer → Bool
greaterPrimeGreater :: TP (Proof (Forall "n" Integer -> SBool))
greaterPrimeGreater = do
   ndfp1 <- recall "notDividesFactP1"    notDividesFactP1
   gpd   <- recall "greaterPrimeDivides" greaterPrimeDivides
   ldp   <- recall "leastDivisorIsPrime" leastDivisorIsPrime
   fal1  <- recall "factAtLeast1"        factAtLeast1
   pal2  <- recall "primeAtLeast2"       primeAtLeast2

   calc "greaterPrimeGreater"
         (\(Forall n) -> greaterPrime n .> n) $
         \n -> [] |-> sTrue
                   ?? ndfp1 `at` (Inst @"n" n, Inst @"k" (greaterPrime n))
                   ?? gpd   `at` Inst @"n" n
                   =: sNot (1 .< greaterPrime n .&& greaterPrime n .<= n)
                   =: (1 .>= greaterPrime n .|| greaterPrime n .> n)
                   =: (1 .>= leastPrimeDivisor (1 + fact n) .|| greaterPrime n .> n)
                   =: (1 .>= leastPrimeDivisor (1 + fact n) .|| greaterPrime n .> n)
                   =: (1 .>= ld 2 (1 + fact n) .|| greaterPrime n .> n)
                   ?? ldp  `at` Inst @"n" (1 + fact n)
                   ?? pal2 `at` Inst @"p" (ld 2 (1 + fact n))
                   ?? fal1 `at` Inst @"n" n
                   =: greaterPrime n .> n
                   =: qed

-- * Infinitude of primes

-- | \(\mathit{isPrime}\,(\mathit{greaterPrime}\,n) \land \mathit{greaterPrime}\,n > n\)
--
-- We can finally prove our goal: For each given number, there is a larger number that is prime. This
-- establishes that we have an infinite number of primes.
--
-- === __Proof__
-- >>> runTP infinitudeOfPrimes
-- Lemma: leastDivisorIsPrime              Q.E.D.
-- Lemma: factAtLeast1                     Q.E.D.
-- Lemma: greaterPrimeGreater              Q.E.D.
-- Lemma: infinitudeOfPrimes
--   Step: 1                               Q.E.D.
--   Step: 2                               Q.E.D.
--   Step: 3                               Q.E.D.
--   Result:                               Q.E.D.
-- [Proven] infinitudeOfPrimes :: Ɐn ∷ Integer → Bool
infinitudeOfPrimes :: TP (Proof (Forall "n" Integer -> SBool))
infinitudeOfPrimes = do
   ldp <- recall "leastDivisorIsPrime" leastDivisorIsPrime
   fa1 <- recall "factAtLeast1"        factAtLeast1
   gpg <- recall "greaterPrimeGreater" greaterPrimeGreater

   calc "infinitudeOfPrimes"
         (\(Forall n) -> let p = greaterPrime n in p .> n .&& isPrime p) $
         \n -> [] |- let p = greaterPrime n
                  in p .> n .&& isPrime (greaterPrime n)
                  =: p .> n .&& isPrime (leastPrimeDivisor (1 + fact n))
                  =: p .> n .&& isPrime (ld 2 (1 + fact n))
                  ?? ldp `at` Inst @"n" (1 + fact n)
                  ?? fa1 `at` Inst @"n" n
                  ?? gpg `at` Inst @"n" n
                  =: sTrue
                  =: qed

-- | \(\forall n. \exists p. \mathit{isPrime}\,p \land p > n\)
--
-- Another expression of the fact that there are infinitely many primes. One might prefer this
-- version as it only refers to the 'isPrime' predicate only.
--
-- === __Proof__
-- >>> runTP noLargestPrime
-- Lemma: infinitudeOfPrimes               Q.E.D.
-- Lemma: helper
--   Step: 1                               Q.E.D.
--   Result:                               Q.E.D.
-- Lemma: noLargestPrime                   Q.E.D.
-- [Proven] noLargestPrime :: Ɐn ∷ Integer → ∃p ∷ Integer → Bool
noLargestPrime :: TP (Proof (Forall "n" Integer -> Exists "p" Integer -> SBool))
noLargestPrime = do
   iop <- recall "infinitudeOfPrimes" infinitudeOfPrimes

   h <- calc "helper"
             (\(Forall @"n" n) -> quantifiedBool (\(Exists p) -> isPrime p .&& p .> n)) $
             \n -> [] |- quantifiedBool (\(Exists p) -> isPrime p .&& p .> n)
                      ?? iop `at` Inst @"n" n
                      =: sTrue
                      =: qed

   lemmaWith cvc5 "noLargestPrime"
       (\(Forall n) (Exists p) -> isPrime p .&& p .> n)
       [proofOf h]

{- HLint ignore module "Avoid lambda" -}
{- HLint ignore module "Eta reduce"   -}
