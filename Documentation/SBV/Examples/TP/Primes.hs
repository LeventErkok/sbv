-----------------------------------------------------------------------------
-- |
-- Module    : Documentation.SBV.Examples.TP.Primes
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Prove that there are an infinite number of primes. Along the way we formalize
-- and prove a number of properties about divisibility as well. Our proof
-- follows closely the ACL2 proof in <https://github.com/acl2/acl2/blob/master/books/projects/numbers/euclid.lisp>.
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

-- | Divides relation. By definition we @0@ only divides @0@. (But every number divides @0@).
dvd :: SInteger -> SInteger -> SBool
x `dvd` y = ite (x .== 0) (y .== 0) (y `sEMod` x .== 0)

-- | \(x > 0 \land y > 0 x \mid y \implies x \leq y\)
--
-- === __Proof__
-- >>> runTP dividesLeq
-- Lemma: dividesLeq                       Q.E.D.
-- [Proven] dividesLeq :: Ɐx ∷ Integer → Ɐy ∷ Integer → Bool
dividesLeq :: TP (Proof (Forall "x" Integer -> Forall "y" Integer -> SBool))
dividesLeq = lemma "dividesLeq"
                    (\(Forall @"x" x) (Forall @"y" y) -> x .> 0 .&& y .> 0 .&& x `dvd` y .=> x .<= y)
                    []

-- | \(x \mid y .=> x `mid` -y\)
--
-- === __Proof__
-- >>> runTP dividesMinus
-- Lemma: dividesMinus
--   Step: 1 (2 way case split)
--     Step: 1.1                           Q.E.D.
--     Step: 1.2                           Q.E.D.
--     Step: 1.Completeness                Q.E.D.
--   Result:                               Q.E.D.
-- [Proven] dividesMinus :: Ɐx ∷ Integer → Ɐy ∷ Integer → Bool
dividesMinus :: TP (Proof (Forall "x" Integer -> Forall "y" Integer -> SBool))
dividesMinus = calc "dividesMinus"
                     (\(Forall @"x" x) (Forall @"y" y) -> x `dvd` y .=> x `dvd` (-y)) $
                     \x y -> [x `dvd` y]
                          |- cases [ x .== 0 ==> x `dvd` (-y)
                                              ?? x .== 0
                                              =: sTrue
                                              =: qed
                                   , x ./= 0 ==> x `dvd` (-y)
                                              ?? y .== x * y `sEDiv` x
                                              =: x `dvd` (-1 * x * y `sEDiv` x)
                                              =: qed
                                   ]

-- | \(x \mid y \land y \mid z \implies x \mid (y + z)\)
--
-- ==== __Proof__
-- >>> runTP dividesSum
-- Lemma: dividesSum
--   Step: 1 (2 way case split)
--     Step: 1.1                           Q.E.D.
--     Step: 1.2.1                         Q.E.D.
--     Step: 1.2.2                         Q.E.D.
--     Step: 1.2.3                         Q.E.D.
--     Step: 1.Completeness                Q.E.D.
--   Result:                               Q.E.D.
-- [Proven] dividesSum :: Ɐx ∷ Integer → Ɐy ∷ Integer → Ɐz ∷ Integer → Bool
dividesSum :: TP (Proof (Forall "x" Integer -> Forall "y" Integer -> Forall "z" Integer -> SBool))
dividesSum =
  calc "dividesSum"
       (\(Forall x) (Forall y) (Forall z) -> x `dvd` y .&& x `dvd` z .=> x `dvd` (y + z)) $
       \x y z -> [x `dvd` y .&& x `dvd` z]
              |- cases [ y .== 0 .|| z .== 0 ==> trivial
                       , y ./= 0 .&& z ./= 0 ==> x `dvd` (y + z)
                                              =: x `dvd` (y `sEDiv` x * x + z `sEDiv` x * x)
                                              =: x `dvd` (x * (y `sEDiv` x + z `sEDiv` x))
                                              =: sTrue
                                              =: qed
                       ]

-- | \(x \mid y \implies x \mid y * z\)
--
-- === __Proof__
-- >>> runTP dividesProduct
-- Lemma: dividesProduct
--   Step: 1 (2 way case split)
--     Step: 1.1                           Q.E.D.
--     Step: 1.2.1                         Q.E.D.
--     Step: 1.2.2                         Q.E.D.
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
                                                 =: qed
                                      ]
-- | \(x \mid y \land y \mid z \implies x \mid z\)
--
-- === __Proof__
-- >>> runTP dividesTransitive
-- Lemma: dividesTransitive
--   Step: 1                               Q.E.D.
--   Step: 2                               Q.E.D.
--   Step: 3                               Q.E.D.
--   Step: 4                               Q.E.D.
--   Result:                               Q.E.D.
-- [Proven] dividesTransitive :: Ɐx ∷ Integer → Ɐy ∷ Integer → Ɐz ∷ Integer → Bool
dividesTransitive :: TP (Proof (Forall "x" Integer -> Forall "y" Integer -> Forall "z" Integer -> SBool))
dividesTransitive = calc "dividesTransitive"
                          (\(Forall x) (Forall y) (Forall z) -> x `dvd` y .&& y `dvd` z .=> x `dvd` z) $
                          \x y z -> [x `dvd` y, y `dvd` z]
                                 |- x `dvd` z
                                 ?? z .== z `sEDiv` y * y
                                 =: x `dvd` (z `sEDiv` y * y)
                                 ?? y .== y `sEDiv` x * x
                                 =: x `dvd` ((z `sEDiv` y) * (y `sEDiv` x * x))
                                 =: x `dvd` (((z `sEDiv` y) * (y `sEDiv` x)) * x)
                                 =: sTrue
                                 =: qed

-- | \(x \mid x\)
--
-- === __Proof__
-- >>> runTP dividesSelf
-- Lemma: dividesSelf                      Q.E.D.
-- [Proven] dividesSelf :: Ɐx ∷ Integer → Bool
dividesSelf :: TP (Proof (Forall "x" Integer -> SBool))
dividesSelf = lemma "dividesSelf" (\(Forall x) -> x `dvd` x) []

-- | \(x \mid 0\)
--
-- === __Proof__
-- >>> runTP divides0
-- Lemma: divides0                         Q.E.D.
-- [Proven] divides0 :: Ɐx ∷ Integer → Bool
divides0 :: TP (Proof (Forall "x" Integer -> SBool))
divides0 = lemma "divides0" (\(Forall x) -> x `dvd` 0) []

-- | \(n \neq 0 \implies n `mid` a-b \equiv a \mod n = b \mod n\)
--
-- === __Proof__
-- >>> runTP dividesModEqual
-- Lemma: dividesModEqual
--   Step: 1                               Q.E.D.
--   Step: 2                               Q.E.D.
--   Step: 3                               Q.E.D.
--   Step: 4 (2 way case split)
--     Step: 4.1.1                         Q.E.D.
--     Step: 4.1.2                         Q.E.D.
--     Step: 4.2.1                         Q.E.D.
--     Step: 4.2.2 (2 way case split)
--       Step: 4.2.2.1                     Q.E.D.
--       Step: 4.2.2.2.1                   Q.E.D.
--       Step: 4.2.2.2.2                   Q.E.D.
--       Step: 4.2.2.2.3                   Q.E.D.
--       Step: 4.2.2.2.4                   Q.E.D.
--       Step: 4.2.2.2.5                   Q.E.D.
--       Step: 4.2.2.Completeness          Q.E.D.
--     Step: 4.Completeness                Q.E.D.
--   Result:                               Q.E.D.
-- [Proven] dividesModEqual :: Ɐa ∷ Integer → Ɐb ∷ Integer → Ɐn ∷ Integer → Bool
dividesModEqual :: TP (Proof (Forall "a" Integer -> Forall "b" Integer -> Forall "n" Integer -> SBool))
dividesModEqual =
  calc "dividesModEqual"
        (\(Forall a) (Forall b) (Forall n) -> n ./= 0 .=> (n `dvd` (a-b) .== (a `sEMod` n .== b `sEMod` n))) $
        \a b n -> [n ./= 0]
               |- let an = a `sEMod` n
                      bn = b `sEMod` n
               in n `dvd` (a - b)
               =: n `dvd` ((a `sEDiv` n * n + an) - (b `sEDiv` n * n + bn))
               =: n `dvd` ((a `sEDiv` n - b `sEDiv` n) * n + an - bn)
               =: let k = a `sEDiv` n - b `sEDiv` n
               in n `dvd` (k * n + an - bn)
               =: cases [ an .== bn ==> n `dvd` (k * n)
                                     =: sTrue
                                     =: qed
                        , an ./= bn ==> n `dvd` (k * n + an - bn)
                                     =: cases [ n .== 0 ==> trivial
                                              , n ./= 0 ==> (k * n + an - bn) `sEMod` n .== 0
                                                         =: (((k * n) `sEMod` n) + ((an - bn) `sEMod` n)) `sEMod` n .== 0
                                                         =: ((an - bn) `sEMod` n) `sEMod` n .== 0
                                                         =: (an - bn) `sEMod` n .== 0
                                                         =: sFalse
                                                         =: qed
                                              ]
                        ]

-- | \(n \neq 0 \implies n \mid a == (a \mod n == 0)\)
--
-- === __Proof__
-- >>> runTP dividesMod0
-- Lemma: dividesMod0                      Q.E.D.
-- [Proven] dividesMod0 :: Ɐn ∷ Integer → Ɐa ∷ Integer → Bool
dividesMod0 :: TP (Proof (Forall "n" Integer -> Forall "a" Integer -> SBool))
dividesMod0 = lemma "dividesMod0"
                    (\(Forall n) (Forall a) -> n ./= 0 .=> n `dvd` a .== ((a `sEMod` n) .== 0))
                    []

-- * The least divisor

-- | The definition of primality will depend on the notion of least divisor. Given @k@ and @n@, the least-divisor of
-- @n@ that is at least @k@ is the number that is at least @k@ and divides @n@ evenly. The idea is that a number is
-- prime if the least divisor of a number between @2@ and itself is the number itself, then it must be prime.
leastDivisor :: SInteger -> SInteger -> SInteger
leastDivisor = smtFunction "leastDivisor" $ \k n -> ite (n `sEMod` k .== 0) k (leastDivisor (k+1) n)

-- | \(1 < k \leq n \implies \textrm{ld}_{k\,n} \mid n \land \textrm{ld}_{k\,n} \geq k \land \textrm{ld}_{k\,n} \leq n\)
--
-- where \(textrm{\ld}_{k\,n} = \textrm{\leastDivisor}\,k\,\n\).
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
           (\(Forall k) (Forall n) -> 1 .< k .&& k .<= n .=> let ld = leastDivisor k n in ld `dvd` n .&& k .<= ld .&& ld .<= n)
           (\k n -> n - k, []) $
           \ih k n -> [1 .< k, k .<= n]
                  |- let ld = leastDivisor k n
                  in cases [ n `sEMod` k .== 0 ==> ld `dvd` n .&& k .<= ld .&& ld .<= n
                                                ?? ld .== k
                                                =: sTrue
                                                =: qed
                           , n `sEMod` k ./= 0 ==> ld `dvd` n .&& k .<= ld .&& ld .<= n
                                                ?? ld .== leastDivisor (k+1) n
                                                ?? ih
                                                =: sTrue
                                                =: qed
                           ]

-- | \(1 < k \leq n \land d \mid n \land k \leq d \implies \textrm{leastDivisor}\,k\,n \leq d\)
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
          (\(Forall k) (Forall n) (Forall d) -> 1 .< k .&& k .<= n .&& d `dvd` n .&& k .<= d .=> leastDivisor k n .<= d)
          (\k n _d -> n - k, []) $
          \ih k n d -> [1 .< k, k .<= n, d `dvd` n, k .<= d]
                    |- cases [ n `sEMod` k .== 0 ==> leastDivisor k n .<= d
                                                  =: k .<= d
                                                  =: qed
                             , n `sEMod` k ./= 0 ==> leastDivisor k n .<= d
                                                  ?? ih
                                                  =: sTrue
                                                  =: qed
                             ]

-- * Primality

-- | A number is prime if its least divisor greater than or equal to @2@ is itself.
isPrime :: SInteger -> SBool
isPrime n = n .>= 2 .&& leastDivisor 2 n .== n

-- | \(\textrm{isPrime}\,p \implies p \geq 2\)
--
-- === __Proof__
-- >>> runTP primeAtLeast2
-- Lemma: primeAtLeast2                    Q.E.D.
-- [Proven] primeAtLeast2 :: Ɐp ∷ Integer → Bool
primeAtLeast2 :: TP (Proof (Forall "p" Integer -> SBool))
primeAtLeast2 = lemma "primeAtLeast2" (\(Forall p) -> isPrime p .=> p .>= 2) []

-- | \(textrm{isPrime}\,p \land d \mid p \land d > 1 \implies d = p\)
--
-- === __Proof__
-- >>> runTP primeNoDivisor
-- Lemma: leastDivisorIsLeast              Q.E.D.
-- Lemma: primeNoDivisor
--   Step: 1                               Q.E.D.
--   Step: 2                               Q.E.D.
--   Result:                               Q.E.D.
-- [Proven] primeNoDivisor :: Ɐp ∷ Integer → Ɐd ∷ Integer → Bool
primeNoDivisor :: TP (Proof (Forall "p" Integer -> Forall "d" Integer -> SBool))
primeNoDivisor = do
  ldil <- recall "leastDivisorIsLeast" leastDivisorIsLeast

  calc "primeNoDivisor"
       (\(Forall p) (Forall d) -> isPrime p .&& d `dvd` p .&& d .> 1 .=> d .== p) $
       \p d -> [isPrime p, d `dvd` p, d .> 1]
            |-> p .>= 2 .&& leastDivisor 2 p .== p
            ?? ldil
            =: p .<= d
            ?? d `dvd` p
            =: sTrue
            =: qed

-- | \(n \geq 2 .=> textrm{isPrime}(\textrm{leastDivisor}\,2\,n)\)
--
-- === __Proof__
-- >>> runTP leastDivisorIsPrime
-- Lemma: leastDivisorIsPrime              Q.E.D. [Modulo: sorry]
-- [Modulo: sorry] leastDivisorIsPrime :: Ɐn ∷ Integer → Bool
leastDivisorIsPrime :: TP (Proof (Forall "n" Integer -> SBool))
leastDivisorIsPrime = lemma "leastDivisorIsPrime"
                            (\(Forall n) -> n .>= 2 .=> isPrime (leastDivisor 2 n))
                            [sorry]

-- | By the 'leastDivisorIsPrime' theorem, the least prime divisor is the least divisor starting from @2@.
leastPrimeDivisor :: SInteger -> SInteger
leastPrimeDivisor n = leastDivisor 2 n

-- * Infinitude of primes

-- | The factorial function.
fact :: SInteger -> SInteger
fact = smtFunction "fact" $ \n -> ite (n .<= 0) 1 (n * (fact (n - 1)))

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

-- | Given a number, return another number which is both prime and is larger than the input. Note that
-- we don't claim to return the closest prime to the input. Just some prime that is larger, as we shall prove.
greaterPrime :: SInteger -> SInteger
greaterPrime n = leastPrimeDivisor (1 + fact n)

-- | \(\textrm{greaterPrime}\, n \mid n! + 1\)
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
                 =: leastDivisor 2 (1 + fact n) `dvd` (1 + fact n)
                 ?? ldd  `at` (Inst @"k" 2, Inst @"n" (1 + fact n))
                 ?? fal1 `at` (Inst @"n" n)
                 =: sTrue
                 =: qed

-- | \(1 \leq k \land k \leq n \implies k `dvd` n!\)
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

-- | \(1 \leq k \land k \leq n \implies \neg (k `dvd` n! + 1)\)
--
-- === __Proof__
-- >>> runTP notDividesFactP1
-- Lemma: dividesSum                       Q.E.D.
-- Lemma: dividesFact                      Q.E.D.
-- Lemma: notDividesFactP1
--   Step: 1                               Q.E.D.
--   Step: 2                               Q.E.D.
--   Result:                               Q.E.D.
-- [Proven] notDividesFactP1 :: Ɐn ∷ Integer → Ɐk ∷ Integer → Bool
notDividesFactP1 :: TP (Proof (Forall "n" Integer -> Forall "k" Integer -> SBool))
notDividesFactP1 = do
   ds <- recall "dividesSum"  dividesSum
   df <- recall "dividesFact" dividesFact

   calc "notDividesFactP1"
         (\(Forall n) (Forall k) -> 1 .< k .&& k .<= n .=> sNot (k `dvd` (fact n + 1))) $
         \n k -> [1 .< k, k .<= n]
              |- k `dvd` (fact n + 1)
              ?? df `at` (Inst @"n" n, Inst @"k" k)
              ?? ds `at` (Inst @"x" k, Inst @"y" (fact n), Inst @"z" 1)
              =: k `dvd` 1
              =: contradiction

-- | \(\textrm{greaterPrime}\, n > n\)
--
-- === __Proof__
-- >>> runTP greaterPrimeGreater
-- Lemma: notDividesFactP1                 Q.E.D.
-- Lemma: greaterPrimeDivides              Q.E.D.
-- Lemma: leastDivisorIsPrime              Q.E.D. [Modulo: sorry]
-- Lemma: factAtLeast1                     Q.E.D.
-- Lemma: primeAtLeast2                    Q.E.D.
-- Lemma: greaterPrimeGreater
--   Step: 1                               Q.E.D.
--   Step: 2                               Q.E.D.
--   Step: 3                               Q.E.D.
--   Step: 4                               Q.E.D.
--   Step: 5                               Q.E.D.
--   Step: 6                               Q.E.D. [Modulo: sorry]
--   Result:                               Q.E.D. [Modulo: sorry]
-- [Modulo: leastDivisorIsPrime] greaterPrimeGreater :: Ɐn ∷ Integer → Bool
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
                   ?? gpd   `at` (Inst @"n" n)
                   =: sNot (1 .< greaterPrime n .&& greaterPrime n .<= n)
                   =: (1 .>= greaterPrime n .|| greaterPrime n .> n)
                   =: (1 .>= leastPrimeDivisor (1 + fact n) .|| greaterPrime n .> n)
                   =: (1 .>= leastPrimeDivisor (1 + fact n) .|| greaterPrime n .> n)
                   =: (1 .>= leastDivisor 2 (1 + fact n) .|| greaterPrime n .> n)
                   ?? ldp  `at` (Inst @"n" (1 + fact n))
                   ?? pal2 `at` (Inst @"p" (leastDivisor 2 (1 + fact n)))
                   ?? fal1 `at` (Inst @"n" n)
                   =: greaterPrime n .> n
                   =: qed

-- | \(\textrm{isPrime}\,(\textrm{greaterPrime}\,n) \land \text{greaterPrime}\,n > n\)
--
-- We can finally prove our goal: For each given number, there is a larger number that is prime. This
-- establishes that we have an infinite number of primes.
--
-- === __Proof__
-- >>> runTP infinitudeOfPrimes
-- Lemma: leastDivisorIsPrime              Q.E.D. [Modulo: sorry]
-- Lemma: factAtLeast1                     Q.E.D.
-- Lemma: greaterPrimeGreater              Q.E.D. [Modulo: sorry]
-- Lemma: infinitudeOfPrimes
--   Step: 1                               Q.E.D.
--   Step: 2                               Q.E.D.
--   Step: 3                               Q.E.D. [Modulo: sorry, leastDivisorIsPrime]
--   Result:                               Q.E.D. [Modulo: sorry, leastDivisorIsPrime]
-- [Modulo: leastDivisorIsPrime, leastDivisorIsPrime] infinitudeOfPrimes :: Ɐn ∷ Integer → Bool
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
                  =: p .> n .&& isPrime (leastDivisor 2 (1 + fact n))
                  ?? ldp `at` Inst @"n" (1 + fact n)
                  ?? fa1 `at` Inst @"n" n
                  ?? gpg `at` Inst @"n" n
                  =: sTrue
                  =: qed

-- | \(\forall n. \exists p. \textrm{isPrime}\,p \land p > n\)
--
-- Another expression of the fact that there are infinitely many primes. One might prefer this
-- version as it only refers to the 'isPrime' predicate only.
--
-- === __Proof__
-- >>> runTP noLargestPrime
-- Lemma: infinitudeOfPrimes               Q.E.D. [Modulo: sorry, leastDivisorIsPrime]
-- Lemma: noLargestPrime
--   Step: 1                               Q.E.D. [Modulo: leastDivisorIsPrime, leastDivisorIsPrime]
--   Result:                               Q.E.D. [Modulo: leastDivisorIsPrime, leastDivisorIsPrime]
-- [Modulo: leastDivisorIsPrime, leastDivisorIsPrime] noLargestPrime :: Ɐn ∷ Integer → Bool
noLargestPrime :: TP (Proof (Forall "n" Integer -> SBool))
noLargestPrime = do
   iop <- recall "infinitudeOfPrimes" infinitudeOfPrimes

   calc "noLargestPrime"
        (\(Forall n) -> quantifiedBool (\(Exists p) -> isPrime p .&& p .> n)) $
        \n -> [] |- quantifiedBool (\(Exists p) -> isPrime p .&& p .> n)
                 ?? iop `at` Inst @"n" n
                 =: sTrue
                 =: qed
