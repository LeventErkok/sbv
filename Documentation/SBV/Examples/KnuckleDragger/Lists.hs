-----------------------------------------------------------------------------
-- |
-- Module    : Documentation.SBV.Examples.KnuckleDragger.Lists
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- A variety of KnuckleDragger proofs on list processing functions.
-----------------------------------------------------------------------------

{-# LANGUAGE CPP                 #-}
{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE DeriveAnyClass      #-}
{-# LANGUAGE DeriveDataTypeable  #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving  #-}
{-# LANGUAGE TemplateHaskell     #-}
{-# LANGUAGE TypeAbstractions    #-}

{-# OPTIONS_GHC -Wall -Werror -Wno-unused-do-bind #-}

module Documentation.SBV.Examples.KnuckleDragger.Lists where

import Prelude (IO, ($), flip, Bool(..), Integer, Num(..), pure, id, (.))

import Data.SBV
import Data.SBV.List
import Data.SBV.Tools.KnuckleDragger

#ifndef HADDOCK
-- $setup
-- >>> -- For doctest purposes only:
-- >>> :set -XScopedTypeVariables
-- >>> import Control.Exception
#endif

-- | Data declaration for an uninterpreted type, usually indicating source.
data A
mkUninterpretedSort ''A

-- | Data declaration for an uninterpreted type, usually indicating target.
data B
mkUninterpretedSort ''B

-- | Data declaration for an uninterpreted type, usually indicating an intermediate value.
data C
mkUninterpretedSort ''C

-- * Appending null

-- | @xs ++ [] == xs@
--
-- We have:
--
-- >>> appendNull
-- Lemma: appendNull                       Q.E.D.
-- [Proven] appendNull
appendNull :: IO Proof
appendNull = runKD $
   lemma "appendNull"
         (\(Forall @"xs" (xs :: SList A)) -> xs ++ nil .== xs)
         []

-- * Moving cons over append

-- | @(x : xs) ++ ys == x : (xs ++ ys)@
--
-- We have:
--
-- >>> consApp
-- Lemma: consApp                          Q.E.D.
-- [Proven] consApp
consApp :: IO Proof
consApp = runKD $
   lemma "consApp"
         (\(Forall @"x" (x :: SA)) (Forall @"xs" xs) (Forall @"ys" ys) -> (x .: xs) ++ ys .== x .: (xs ++ ys))
         []

-- * Associativity of append

-- | @(xs ++ ys) ++ zs == xs ++ (ys ++ zs)@
--
-- We have:
--
-- >>> appendAssoc
-- Lemma: appendAssoc                      Q.E.D.
-- [Proven] appendAssoc
--
-- Surprisingly, z3 can prove this without any induction. (Since SBV's append translates directly to
-- the concatenation of sequences in SMTLib, it must trigger an internal axiom (heuristic?) in z3
-- that proves it right out-of-the-box!)
appendAssoc :: IO Proof
appendAssoc = runKD $
   lemma "appendAssoc"
         (\(Forall @"xs" (xs :: SList A)) (Forall @"ys" ys) (Forall @"zs" zs) ->
              xs ++ (ys ++ zs) .== (xs ++ ys) ++ zs)
         []

-- * Reverse and append

-- | @reverse (x:xs) == reverse xs ++ [x]@
--
-- >>> revCons
-- Lemma: revCons                          Q.E.D.
-- [Proven] revCons
revCons :: IO Proof
revCons = runKD $
    lemma "revCons"
          (\(Forall @"x" (x :: SA)) (Forall @"xs" xs) -> reverse (x .: xs) .== reverse xs ++ singleton x)
          []

-- | @reverse (xs ++ ys) .== reverse ys ++ reverse xs@
--
-- We have:
--
-- >>> revApp
-- Lemma: revApp                           Q.E.D.
-- [Proven] revApp
revApp :: IO Proof
revApp = runKD $ do
   let p :: SList A -> SList A -> SBool
       p xs ys = reverse (xs ++ ys) .== reverse ys ++ reverse xs

   lemma "revApp"
         (\(Forall @"xs" (xs :: SList A)) (Forall @"ys" ys) -> p xs ys)
         -- induction is done on the last argument, so we use flip to make sure we induct on xs
         [induct (flip p)]

-- * Reversing twice is identity

-- | @reverse (reverse xs) == xs@
--
-- We have:
--
-- >>> reverseReverse
-- Lemma: revApp                           Q.E.D.
-- Lemma: reverseReverse                   Q.E.D.
-- [Proven] reverseReverse
reverseReverse :: IO Proof
reverseReverse = runKD $ do

   let p :: SList A -> SBool
       p xs = reverse (reverse xs) .== xs

   ra <- use revApp

   lemma "reverseReverse" (\(Forall @"xs" xs) -> p xs) [induct p, ra]

-- * Lengths of lists

-- | @length (x : xs) = 1 + length xs@
--
-- We have:
--
-- >>> lengthTail
-- Lemma: lengthTail                       Q.E.D.
-- [Proven] lengthTail
lengthTail :: IO Proof
lengthTail = runKD $
   lemma "lengthTail"
         (\(Forall @"x" (x :: SA)) (Forall @"xs" xs) -> length (x .: xs) .== 1 + length xs)
         []

-- | It is instructive to see what kind of counter-example we get if a lemma fails to prove.
-- Below, we do a variant of the 'lengthTail, but with a bad implementation over integers,
-- and see the counter-example. Our implementation returns an incorrect answer if the given list is longer
-- than 5 elements and have 42 in it. We have:
--
-- >>> badLengthProof `catch` (\(_ :: SomeException) -> pure ())
-- Lemma: badLengthProof
-- *** Failed to prove badLengthProof.
-- Falsifiable. Counter-example:
--   xs   = [15,11,13,16,27,42] :: [Integer]
--   imp  =                  42 :: Integer
--   spec =                   6 :: Integer
badLengthProof :: IO ()
badLengthProof = runKD $ do
   let badLength :: SList Integer -> SInteger
       badLength xs = ite (length xs .> 5 .&& 42 `elem` xs) 42 (length xs)

   lemma "badLengthProof"
         (\(Forall @"xs" xs) -> observe "imp" (badLength xs) .== observe "spec" (length xs))
         []

   pure ()

-- | @length (xs ++ ys) == length xs + length ys@
--
-- We have:
--
-- >>> lenAppend
-- Lemma: lenAppend                        Q.E.D.
-- [Proven] lenAppend
lenAppend :: IO Proof
lenAppend = runKD $
    lemma "lenAppend"
          (\(Forall @"xs" (xs :: SList A)) (Forall @"ys" ys) -> length (xs ++ ys) .== length xs + length ys)
          []

-- | @length xs == length ys -> length (xs ++ ys) == 2 * length xs@
--
-- We have:
--
-- >>> lenAppend2
-- Lemma: lenAppend2                       Q.E.D.
-- [Proven] lenAppend2
lenAppend2 :: IO Proof
lenAppend2 = runKD $
    lemma "lenAppend2"
          (\(Forall @"xs" (xs :: SList A)) (Forall @"ys" ys) ->
                length xs .== length ys .=> length (xs ++ ys) .== 2 * length xs)
          []

-- * Any, all, and filtering

-- | |not (all id xs) == any not xs|
--
-- A list of booleans is not all true, if any of them is false. We have:
--
-- >>> allAny
-- Lemma: allAny                           Q.E.D.
-- [Proven] allAny
allAny :: IO Proof
allAny = runKD $ lemma "allAny" (\(Forall @"xs" xs) -> p xs) [induct p]
  where p xs = sNot (all id xs) .== any sNot xs

-- | If an integer list doesn't have 2 as an element, then filtering for @> 2@ or @.>= 2@
-- yields the same result. We have:
--
-- >>> filterEx
-- Lemma: filterEx                         Q.E.D.
-- [Proven] filterEx
filterEx :: IO Proof
filterEx = runKD $ lemma "filterEx" (\(Forall @"xs" xs) -> p xs) [induct p]
  where p xs = (2 :: SInteger) `notElem` xs .=> (filter (.> 2) xs .== filter (.>= 2) xs)

-- | The 'filterEx' example above, except we get a counter-example if @2@ can be in the list. Note that
-- we don't need the induction tactic here, but we do need to tell KnuckleDragger to not generate the
-- high-order function equivalence axioms, which leads to an @unknown@ answer otherwise.
--
-- >>> filterEx2 `catch` (\(_ :: SomeException) -> pure ())
-- Lemma: filterEx2
-- *** Failed to prove filterEx2.
-- Falsifiable. Counter-example:
--   xs = [2] :: [Integer]
filterEx2 :: IO ()
filterEx2 = runKDWith z3{kdOptions = (kdOptions z3) {generateHOEquivs = False}} $ do
        let p :: SList Integer -> SBool
            p xs = filter (.> 2) xs .== filter (.>= 2) xs

        lemma "filterEx2" (\(Forall @"xs" xs) -> p xs) []

        pure ()

-- * Foldr-map fusion

-- | @foldr f a . map g = foldr (f . g) a@
--
-- We have:
--
-- >>> foldrMapFusion
-- Lemma: foldrMapFusion                   Q.E.D.
-- [Proven] foldrMapFusion
foldrMapFusion :: IO Proof
foldrMapFusion = runKD $ do
  let a :: SA
      a = uninterpret "a"

      g :: SC -> SB
      g = uninterpret "g"

      f :: SB -> SA -> SA
      f = uninterpret "f"

      p xs = foldr f a (map g xs) .== foldr (f . g) a xs

  lemma "foldrMapFusion" (\(Forall @"xs" xs) -> p xs) [induct p]

-- * Foldr-foldr fusion

-- |
--
-- @
--   Given f a = b and f (g x y) = h x (f y), for all x and y
--   We have: f . foldr g a = foldr h b
-- @
--
-- Note that, as of Dec 2024, z3 can't converge on this proof, but cvc5 gets it almost
-- instantaneously. We have:
--
-- >>> foldrFusion
-- Axiom: f a == b                         Axiom.
-- Axiom: f (g x) = h x (f y)              Axiom.
-- Lemma: foldrFusion                      Q.E.D.
-- [Proven] foldrFusion
foldrFusion :: IO Proof
foldrFusion = runKDWith cvc5 $ do
   let a :: SA
       a = uninterpret "a"

       b :: SB
       b = uninterpret "b"

       f :: SA -> SB
       f = uninterpret "f"

       g :: SC -> SA -> SA
       g = uninterpret "g"

       h :: SC -> SB -> SB
       h = uninterpret "h"

       p xs = f (foldr g a xs) .== foldr h b xs

   -- f a == b
   h1 <- axiom "f a == b" $ f a .== b

   -- forall x, y: f (g x y) = h x (f y)
   h2 <- axiom "f (g x) = h x (f y)" $ \(Forall @"x" x) (Forall @"y" y) -> f (g x y) .== h x (f y)

   lemma "foldrFusion" (\(Forall @"xs" xs) -> p xs) [h1, h2, induct p]

-- * Foldr over append

-- | @foldr f a (xs ++ ys) == foldr f (foldr f a ys) xs@
--
-- We have:
--
-- >>> foldrOverAppend
-- Lemma: foldrOverAppend                  Q.E.D.
-- [Proven] foldrOverAppend
foldrOverAppend :: IO Proof
foldrOverAppend = runKD $ do
   let a :: SA
       a = uninterpret "a"

       f :: SA -> SA -> SA
       f = uninterpret "f"

       p xs ys = foldr f a (xs ++ ys) .== foldr f (foldr f a ys) xs

   lemma "foldrOverAppend"
          (\(Forall @"xs" xs) (Forall @"ys" ys) -> p xs ys)
          -- Induction is done on the last element. Here we want to induct on xs, hence the flip below.
          [induct (flip p)]

-- * Map, append, and reverse

-- | @map f (xs ++ ys) == map f xs ++ map f ys@
--
-- >>> mapAppend
-- Lemma: mapAppend                        Q.E.D.
-- [Proven] mapAppend
mapAppend :: IO Proof
mapAppend = runKD $ do
   let p :: (SA -> SB) -> SList A -> SList A -> SBool
       p g xs ys = map g (xs ++ ys) .== map g xs ++ map g ys

       -- For an arbitrary uninterpreted function 'f':
       f :: SA -> SB
       f = uninterpret "f"

   lemma "mapAppend"
         (\(Forall @"xs" xs) (Forall @"ys" ys) -> p f xs ys)
         -- induction is done on the last argument, so flip to do it on xs
         [induct (flip (p f))]

-- | @map f . reverse == reverse . map f@
--
-- >>> mapReverse
-- Lemma: revCons                          Q.E.D.
-- Lemma: mapAppend                        Q.E.D.
-- Chain: mapReverse
--   Lemma: mapReverse.1                   Q.E.D.
--   Lemma: mapReverse.2                   Q.E.D.
--   Lemma: mapReverse.3                   Q.E.D.
--   Lemma: mapReverse.4                   Q.E.D.
--   Lemma: mapReverse.5                   Q.E.D.
--   Lemma: mapReverse.6                   Q.E.D.
-- Lemma: mapReverse                       Q.E.D.
-- [Proven] mapReverse
mapReverse :: IO Proof
mapReverse = runKD $ do
     let p :: (SA -> SB) -> SList A -> SBool
         p g xs = reverse (map g xs) .== map g (reverse xs)

         -- For an arbitrary uninterpreted function 'f':
         f :: SA -> SB
         f = uninterpret "f"

     rCons <- use revCons
     mApp  <- use mapAppend

     chainLemma "mapReverse"
                (\(Forall @"xs" xs) -> p f xs)
                (\x xs -> [ reverse (map f (x .: xs))
                          , reverse (f x .: map f xs)
                          , reverse (map f xs) ++ singleton (f x)
                          , map f (reverse xs) ++ singleton (f x)
                          , map f (reverse xs) ++ map f (singleton x)
                          , map f (reverse xs ++ singleton x)
                          , map f (reverse (x .: xs))
                          ])
                [induct (p f), rCons, mApp]

-- * Reverse and length

-- | @length xs == length (reverse xs)@
--
-- We have:
--
-- >>> revLen
-- Lemma: revLen                           Q.E.D.
-- [Proven] revLen
revLen :: IO Proof
revLen = runKD $ do
   let p :: SList A -> SBool
       p xs = length (reverse xs) .== length xs

   lemma "revLen"
         (\(Forall @"xs" xs) -> p xs)
         [induct p]

-- | An example where we attempt to prove a non-theorem. Notice the counter-example
-- generated for:
--
-- @length xs = ite (length xs .== 3) 5 (length xs)@
--
-- We have:
--
-- >>> badRevLen `catch` (\(_ :: SomeException) -> pure ())
-- Lemma: badRevLen
-- *** Failed to prove badRevLen.
-- Falsifiable. Counter-example:
--   xs = [A_1,A_2,A_1] :: [A]
badRevLen :: IO ()
badRevLen = runKD $ do
   let p :: SList A -> SBool
       p xs = length (reverse xs) .== ite (length xs .== 3) 5 (length xs)

   lemma "badRevLen"
         (\(Forall @"xs" xs) -> p xs)
         [induct p]

   pure ()

{- Can't converge
-- * Foldl over append

-- | @foldl f a (xs ++ ys) == foldl f (foldl f a xs) ys@
--
-- We have:
--
-- >>> foldlOverAppend
-- Lemma: foldrOverAppend                  Q.E.D.
-- [Proven] foldrOverAppend
foldlOverAppend :: IO Proof
foldlOverAppend = runKD $ do
   let f :: SA -> SA -> SA
       f = uninterpret "f"

       p a xs ys = foldl f a (xs ++ ys) .== foldl f (foldl f a xs) ys

   chainLemma "foldlOverAppend"
               (\(Forall @"a" a) (Forall @"xs" xs) (Forall @"ys" ys) -> p a xs ys)
               (\a x xs ys -> [ foldl f a ((x .: xs) ++ ys)
                              , foldl f a (x .: (xs ++ ys))
                              , foldl f (a `f` x) (xs ++ ys)
                              , foldl f (foldl f (a `f` x) xs) ys
                              ])
               -- Induction is done on the last element. Here we want to induct on xs, hence the rearrangement below
               [induct (flip . p)]
-}

{- can't converge
-- * Foldr-foldl correspondence

-- | @foldr f e xs == foldl (flip f) e (reverse xs)@
--
-- We have:
--
-- >> foldrFoldlReverse
foldrFoldlReverse :: IO Proof
foldrFoldlReverse = runKD $ do
   let e :: SB
       e = uninterpret "e"

       f :: SA -> SB -> SB
       f = uninterpret "f"

       p xs = foldr f e xs .== foldl (flip f) e (reverse xs)

   rc <- use $ runKD revCons

   chainLemma "foldrFoldlDuality"
              (\(Forall @"xs" xs) -> p xs)
              (\x xs -> [ -- foldr f e (x .: xs)
                        -- , x `f` foldr f e xs
                          foldl (flip f) e (reverse (x .: xs))
                        , foldl (flip f) e (reverse xs ++ singleton x)
                        , x `f` foldl (flip f) e (reverse xs)
                        ])
              [rc, induct p]
-}

{-
 --- Can't converge
-- * Bookkeeping law

-- | Provided @f@ is associative and @a@ is its right-unit: we have:
--
-- | @foldr f a . concat == foldr f a . map (foldr f a)@
--
-- We have:
--
-- >>> bookKeeping
bookKeeping :: IO Proof
bookKeeping = runKD $ do
   let a :: SA
       a = uninterpret "a"

       f :: SA -> SA -> SA
       f = uninterpret "f"

       p xss = foldr f a (concat xss) .== foldr f a (map (foldr f a) xss)

   assoc <- axiom "f is associative" (\(Forall @"x" x) (Forall @"y" y) (Forall @"z" z) -> x `f` (y `f` z) .== (x `f` y) `f` z)
   unit  <- axiom "a is right-unit"   (\(Forall @"x" x) -> x `f` a .== x)

   foa <- use foldrOverAppend

   chainLemma "bookKeeping"
              (\(Forall @"xss" xss) -> p xss)
              (\xs xss -> [ -- foldr f a (concat (xs .: xss))
                          -- , foldr f a (xs ++ concat xss)
                          -- , foldr f (foldr f a (concat xss)) xs
                          -- , foldr f (foldr f a (map (foldr f a) xss)) xs

                            f (foldr f a xs) (foldr f a (map (foldr f a) xss))
                          , foldr f (foldr f a (map (foldr f a) xss)) (singleton (foldr f a xs))
                          , foldr f a (singleton (foldr f a xs) ++ map (foldr f a) xss)
                          , foldr f a (foldr f a xs .: map (foldr f a) xss)
                          , foldr f a (map (foldr f a) (xs .: xss))
                          ])
              [assoc, unit, foa, induct p]
-}

{----------------
-- TODO: Can't converge on this either..
-- | First duality theorem. Given:
--
-- @
--     x @ (y @ z) = (x @ y) @ z     (associativity of @)
-- and e @ x = x                     (left unit)
-- and x @ e = x                     (right unit)
-- @
--
-- Prove:
--
-- @
--     foldr (@) e xs = foldl (@) e xs
-- @
--
-- We have:
--
-- >>> firstDuality
firstDuality :: IO Proof
firstDuality  = runKD $ do
   let (@) :: SA -> SA -> SA
       (@) = uninterpret "|@|"

       e :: SA
       e = uninterpret "e"

   axm1 <- axiom "@ is associative" (\(Forall @"x" x) (Forall @"y" y) (Forall @"z" z) -> x @ (y @ z) .== (x @ y) @ z)
   axm2 <- axiom "e is left unit"   (\(Forall @"x" x) -> e @ x .== x)
   axm3 <- axiom "e is right unit"  (\(Forall @"x" x) -> x @ e .== x)

   let p xs = foldr (@) e xs .== foldl (@) e xs

   -- Helper: foldl (@) (y @ z) xs = y @ foldl (@) z xs
   h <- do
      let hp y z xs = foldl (@) (y @ z) xs .== y @ foldl (@) z xs

      chainLemma "foldl over @"
                 (\(Forall @"y" y) (Forall @"z" z) (Forall @"xs" xs) -> hp y z xs)
                 (\y z x xs -> [ foldl (@) (y @ z) (x .: xs)
                               , foldl (@) ((y @ z) @ x) xs
                               , foldl (@) (y @ (z @ x)) xs
                               -- this transition is hard
                               , y @ foldl (@) (z @ x) xs
                               , y @ foldl (@) z (x .: xs)
                               ])
                 [axm1, axm2, induct hp]

   lemma "firstDuality" (\(Forall @"xs" xs) -> p xs) [axm1, axm2, axm3, h, induct p]
-}

{- TODO: Can't converge on this one. The strengthened induction axiom requires a very careful
   instantiation of the inductive hypothesis, which I can't get through. Perhaps we need proper
   support for patterns.

-- | Given:
-- @
--        (x <> y) @ z = x \<> (y \@ z)
--   and  e \@ x = x \<> e
-- @
--
-- Proves:
--
-- @
--    foldl (\@\) e xs = foldr (\<>) e xs@
-- @
--
-- We have:
--
-- >>> foldrFoldl
foldrFoldl :: IO Proof
foldrFoldl = runKD $ do

   let -- Declare the operators as uninterpreted functions
       (@) :: SB -> SA -> SB
       (@) = uninterpret "|@|"

       (<>) :: SA -> SB -> SB
       (<>) = uninterpret "|<>|"

       -- The unit element
       e :: SB
       e = uninterpret "e"

       -- Equivalence predicate
       p :: SList A -> SBool
       p xs = foldl (@) e xs .== foldr (<>) e xs


   -- Assumptions about the operators

   -- (x <> y) @ z == x <> (y @ z)
   axm1 <- axiom "<> over @" $ \(Forall @"x" x) (Forall @"y" y) (Forall @"z" z)
                                  -> (x <> y) @ z .== x <> (y @ z)

   -- e @ x == x <> e
   axm2 <- axiom "unit" $ \(Forall @"x" x) -> e @ x .== x <> e

   -- Helper: foldl (@) (y <> z) xs = y <> foldl (@) z xs
   h <- do
      let hp y z xs = foldl (@) (y <> z) xs .== y <> foldl (@) z xs

      chainLemma "foldl over @"
                 (\(Forall @"y" y) (Forall @"z" z) (Forall @"xs" xs) -> hp y z xs)
                 (\y z x xs -> [ foldl (@) (y <> z) (x .: xs)
                               , foldl (@) ((y <> z) @ x) xs
                               , foldl (@) (y <> (z @ x)) xs
                               -- this transition is hard
                               , y <> foldl (@) (z @ x) xs
                               , y <> foldl (@) z (x .: xs)
                               ])
                 [axm1, axm2, induct hp]

   -- Final proof:
   lemma "foldrFoldl" (\(Forall @"xs" xs) -> p xs) [axm1, axm2, h, induct p]
-}
