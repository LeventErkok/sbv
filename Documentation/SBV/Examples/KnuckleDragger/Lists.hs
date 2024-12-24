-----------------------------------------------------------------------------
-- |
-- Module    : Documentation.SBV.Examples.KnuckleDragger.AppendRev
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Example use of the KnuckleDragger, on list append and reverses.
-----------------------------------------------------------------------------

{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE DeriveAnyClass      #-}
{-# LANGUAGE DeriveDataTypeable  #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving  #-}
{-# LANGUAGE TemplateHaskell     #-}
{-# LANGUAGE TypeAbstractions    #-}
{-# LANGUAGE TypeApplications    #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module Documentation.SBV.Examples.KnuckleDragger.AppendRev where

import Prelude hiding (reverse, (++))

import Data.SBV
import Data.SBV.Tools.KnuckleDragger

import Data.SBV.List ((.:), (++), reverse)
import qualified Data.SBV.List as SL

-- | Use an uninterpreted type for the elements
data Elt
mkUninterpretedSort ''Elt

-- | @xs ++ [] == xs@
--
-- We have:
--
-- >>> appendNull
-- Lemma: appendNull                       Q.E.D.
-- [Proven] appendNull
appendNull :: IO Proof
appendNull = runKD $ lemma "appendNull"
                           (\(Forall @"xs" (xs :: SList Elt)) -> xs ++ SL.nil .== xs)
                           []

-- | @(x : xs) ++ ys == x : (xs ++ ys)@
--
-- We have:
--
-- >>> consApp
-- Lemma: consApp                          Q.E.D.
-- [Proven] consApp
consApp :: IO Proof
consApp = runKD $ lemma "consApp"
                        (\(Forall @"x" (x :: SElt)) (Forall @"xs" xs) (Forall @"ys" ys) -> (x .: xs) ++ ys .== x .: (xs ++ ys))
                        []

-- | @(xs ++ ys) ++ zs == xs ++ (ys ++ zs)@
--
-- We have:
--
-- >>> appendAssoc
-- Lemma: appendAssoc                      Q.E.D.
-- [Proven] appendAssoc
appendAssoc :: IO Proof
appendAssoc = runKD $ do
   let p :: SymVal a => SList a -> SList a -> SList a -> SBool
       p xs ys zs = xs ++ (ys ++ zs) .== (xs ++ ys) ++ zs

   lemma "appendAssoc"
         (\(Forall @"xs" (xs :: SList Elt)) (Forall @"ys" ys) (Forall @"zs" zs) -> p xs ys zs)
         []

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

   -- Helper lemma: @reverse (xs ++ ys) .== reverse ys ++ reverse xs@
   let ra :: SymVal a => SList a -> SList a -> SBool
       ra xs ys = reverse (xs ++ ys) .== reverse ys ++ reverse xs

   revApp <- lemma "revApp" (\(Forall @"xs" (xs :: SList Elt)) (Forall @"ys" ys) -> ra xs ys)
                   -- induction is always done on the last argument, so flip to make sure we induct on xs
                   [induct (flip (ra @Elt))]

   let p :: SymVal a => SList a -> SBool
       p xs = reverse (reverse xs) .== xs

   lemma "reverseReverse"
         (\(Forall @"xs" (xs :: SList Elt)) -> p xs)
         [induct (p @Elt), revApp]
-----------------------------------------------------------------------------
-- |
-- Module    : Documentation.SBV.Examples.KnuckleDragger.EquationalReasoning
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Various equalities that arise in functional-programming. A good source
-- is the classic book "Introduction to Functional Programming using Haskell,"
-- second edition. (Section 4.6 and others.)
-----------------------------------------------------------------------------

{-# LANGUAGE CPP                #-}
{-# LANGUAGE DataKinds          #-}
{-# LANGUAGE DeriveAnyClass     #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell    #-}
{-# LANGUAGE TypeAbstractions   #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module Documentation.SBV.Examples.KnuckleDragger.EquationalReasoning where

import Prelude hiding (concat, map, foldl, foldr, reverse, (<>), (++))

import Data.SBV
import Data.SBV.List
import Data.SBV.Tools.KnuckleDragger

-- | Data declaration for an uninterpreted type, usually indicating source.
data A
mkUninterpretedSort ''A

-- | Data declaration for an uninterpreted type, usually indicating target.
data B
mkUninterpretedSort ''B

-- | Data declaration for an uninterpreted type, usually indicating an intermediate value.
data C
mkUninterpretedSort ''C

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
foldrFusion = runKD $ do
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

   lemmaWith cvc5 "foldrFusion" (\(Forall @"xs" xs) -> p xs) [h1, h2, induct p]

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
-----------------------------------------------------------------------------
-- |
-- Module    : Documentation.SBV.Examples.KnuckleDragger.ListLen
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Example use of the KnuckleDragger, about lenghts of lists
-----------------------------------------------------------------------------

{-# LANGUAGE CPP                 #-}
{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE DeriveAnyClass      #-}
{-# LANGUAGE DeriveDataTypeable  #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving  #-}
{-# LANGUAGE TemplateHaskell     #-}
{-# LANGUAGE TypeAbstractions    #-}
{-# LANGUAGE TypeApplications    #-}

{-# OPTIONS_GHC -Wall -Werror -Wno-unused-do-bind #-}

module Documentation.SBV.Examples.KnuckleDragger.ListLen where

import Prelude hiding (length, (++))

import Data.SBV
import Data.SBV.Tools.KnuckleDragger

import qualified Data.SBV.List as SL

#ifndef HADDOCK
-- $setup
-- >>> -- For doctest purposes only:
-- >>> :set -XScopedTypeVariables
-- >>> import Control.Exception
#endif

-- | Use an uninterpreted type for the elements
data Elt
mkUninterpretedSort ''Elt

-- | Prove that the length of a list is one more than the length of its tail.
--
-- We have:
--
-- >>> listLengthProof
-- Lemma: length_correct                   Q.E.D.
-- [Proven] length_correct
listLengthProof :: IO Proof
listLengthProof = runKD $ do
   let length :: SList Elt -> SInteger
       length = smtFunction "length" $ \xs -> ite (SL.null xs) 0 (1 + length (SL.tail xs))

       spec :: SList Elt -> SInteger
       spec = SL.length

       p :: SList Elt -> SBool
       p xs = observe "imp" (length xs) .== observe "spec" (spec xs)

   lemma "length_correct" (\(Forall @"xs" xs) -> p xs) [induct p]

-- | It is instructive to see what kind of counter-example we get if a lemma fails to prove.
-- Below, we do a variant of the 'listLengthProof', but with a bad implementation over integers,
-- and see the counter-example. Our implementation returns an incorrect answer if the given list is longer
-- than 5 elements and have 42 in it. We have:
--
-- >>> badProof `catch` (\(_ :: SomeException) -> pure ())
-- Lemma: bad
-- *** Failed to prove bad.
-- Falsifiable. Counter-example:
--   xs   = [8,25,26,27,28,42] :: [Integer]
--   imp  =                 42 :: Integer
--   spec =                  6 :: Integer
badProof :: IO ()
badProof = runKD $ do
   let length :: SList Integer -> SInteger
       length = smtFunction "length" $ \xs -> ite (SL.null xs) 0 (1 + length (SL.tail xs))

       badLength :: SList Integer -> SInteger
       badLength xs = ite (SL.length xs .> 5 .&& 42 `SL.elem` xs) 42 (length xs)

       spec :: SList Integer -> SInteger
       spec = SL.length

       p :: SList Integer -> SBool
       p xs = observe "imp" (badLength xs) .== observe "spec" (spec xs)

   lemma "bad" (\(Forall @"xs" xs) -> p xs) [induct p]

   pure ()

-- | @length (xs ++ ys) == length xs + length ys@
--
-- We have:
--
-- >>> lenAppend
-- Lemma: lenAppend                        Q.E.D.
-- [Proven] lenAppend
lenAppend :: IO Proof
lenAppend = runKD $ lemma "lenAppend"
                           (\(Forall @"xs" (xs :: SList Elt)) (Forall @"ys" ys) ->
                                 SL.length (xs SL.++ ys) .== SL.length xs + SL.length ys)
                           []

-- | @length xs == length ys -> length (xs ++ ys) == 2 * length xs@
--
-- We have:
--
-- >>> lenAppend2
-- Lemma: lenAppend2                       Q.E.D.
-- [Proven] lenAppend2
lenAppend2 :: IO Proof
lenAppend2 = runKD $ lemma "lenAppend2"
                           (\(Forall @"xs" (xs :: SList Elt)) (Forall @"ys" ys) ->
                                     SL.length xs .== SL.length ys
                                 .=> SL.length (xs SL.++ ys) .== 2 * SL.length xs)
                           []
-----------------------------------------------------------------------------
-- |
-- Module    : Documentation.SBV.Examples.KnuckleDragger.Lists
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Various KnuckleDragger proofs about lists
-----------------------------------------------------------------------------

{-# LANGUAGE CPP                 #-}
{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE DeriveAnyClass      #-}
{-# LANGUAGE DeriveDataTypeable  #-}
{-# LANGUAGE StandaloneDeriving  #-}
{-# LANGUAGE TemplateHaskell     #-}
{-# LANGUAGE TypeAbstractions    #-}

{-# OPTIONS_GHC -Wall -Werror -Wno-unused-do-bind #-}

module Documentation.SBV.Examples.KnuckleDragger.Lists where

import Data.SBV
import Data.SBV.List
import Data.SBV.Tools.KnuckleDragger

import Prelude hiding(reverse, (++), any, all, notElem, filter, map)

#ifndef HADDOCK
-- $setup
-- >>> -- For doctest purposes only:
-- >>> :set -XScopedTypeVariables
-- >>> import Control.Exception
-- >>> import Data.SBV.Tools.KnuckleDragger
#endif

-- | A list of booleans is not all true, if any of them is false. We have:
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

-- | The 'filterEx' example above, except we get a counter-example if `2` can be in the list. Note that
-- we don't even need the induction tactic here. (Though having it wouldn't hurt.) We have:
--
-- >>> filterEx2 `catch` (\(_ :: SomeException) -> pure ())
-- Lemma: filterEx
-- *** Failed to prove filterEx.
-- Falsifiable. Counter-example:
--   xs = [2] :: [Integer]
filterEx2 :: IO ()
filterEx2 = runKD $ do
        let p :: SList Integer -> SBool
            p xs = filter (.> 2) xs .== filter (.>= 2) xs

        lemma "filterEx" (\(Forall @"xs" xs) -> p xs) []

        pure ()

-- | Data declaration for an uninterpreted source type.
data A
mkUninterpretedSort ''A

-- | Data declaration for an uninterpreted target type.
data B
mkUninterpretedSort ''B

-- | @reverse (x:xs) == reverse xs ++ [x]@
--
-- >>> runKD revCons
-- Lemma: revCons                          Q.E.D.
-- [Proven] revCons
revCons :: KD Proof
revCons = do
    let p :: SA -> SList A -> SBool
        p x xs = reverse (x .: xs) .== reverse xs ++ singleton x

    lemma "revCons" (\(Forall @"x" x) (Forall @"xs" xs) -> p x xs) []

-- | @map f (xs ++ ys) == map f xs ++ map f ys@
--
-- >>> runKD mapAppend
-- Lemma: mapAppend                        Q.E.D.
-- [Proven] mapAppend
mapAppend :: KD Proof
mapAppend = do
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
-- >>> runKD mapReverse
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
mapReverse :: KD Proof
mapReverse = do
     let p :: (SA -> SB) -> SList A -> SBool
         p g xs = reverse (map g xs) .== map g (reverse xs)

         -- For an arbitrary uninterpreted function 'f':
         f :: SA -> SB
         f = uninterpret "f"

     rCons <- revCons
     mApp  <- mapAppend

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
-----------------------------------------------------------------------------
-- |
-- Module    : Documentation.SBV.Examples.KnuckleDragger.RevLen
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Proof that reversing a list does not change its length.
-----------------------------------------------------------------------------

{-# LANGUAGE CPP                 #-}
{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE DeriveAnyClass      #-}
{-# LANGUAGE DeriveDataTypeable  #-}
{-# LANGUAGE StandaloneDeriving  #-}
{-# LANGUAGE TemplateHaskell     #-}
{-# LANGUAGE TypeAbstractions    #-}

{-# OPTIONS_GHC -Wall -Werror -Wno-unused-do-bind #-}

module Documentation.SBV.Examples.KnuckleDragger.RevLen where

import Prelude hiding (length, reverse)

import Data.SBV
import Data.SBV.Tools.KnuckleDragger

import Data.SBV.List (reverse, length)

#ifndef HADDOCK
-- $setup
-- >>> -- For doctest purposes only:
-- >>> :set -XScopedTypeVariables
-- >>> import Control.Exception
#endif

-- | Use an uninterpreted type for the elements
data Elt
mkUninterpretedSort ''Elt

-- | @length xs == length (reverse xs)@
--
-- We have:
--
-- >>> revLen
-- Lemma: revLen                           Q.E.D.
-- [Proven] revLen
revLen :: IO Proof
revLen = runKD $ do
   let p :: SList Elt -> SBool
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
--   xs = [Elt_1,Elt_2,Elt_1] :: [Elt]
badRevLen :: IO ()
badRevLen = runKD $ do
   let p :: SList Elt -> SBool
       p xs = length (reverse xs) .== ite (length xs .== 3) 5 (length xs)

   lemma "badRevLen"
         (\(Forall @"xs" xs) -> p xs)
         [induct p]

   pure ()
