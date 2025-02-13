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

import Prelude (IO, ($), Integer, Num(..), pure, id, (.), flip)

import Data.SBV
import Data.SBV.List
import Data.SBV.Tools.KnuckleDragger

#ifndef HADDOCK
-- $setup
-- >>> -- For doctest purposes only:
-- >>> :set -XScopedTypeVariables
-- >>> import Data.SBV
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
         []

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

   lemma "reverseReverse" (\(Forall @"xs" xs) -> p xs) [ra]

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

-- | @not (all id xs) == any not xs@
--
-- A list of booleans is not all true, if any of them is false. We have:
--
-- >>> allAny
-- Lemma: allAny                           Q.E.D.
-- [Proven] allAny
allAny :: IO Proof
allAny = runKD $ lemma "allAny" (\(Forall @"xs" xs) -> p xs) []
  where p xs = sNot (all id xs) .== any sNot xs

-- | If an integer list doesn't have 2 as an element, then filtering for @> 2@ or @.>= 2@
-- yields the same result. We have:
--
-- >>> filterEx
-- Lemma: filterEx                         Q.E.D.
-- [Proven] filterEx
filterEx :: IO Proof
filterEx = runKD $ lemma "filterEx" (\(Forall @"xs" xs) -> p xs) []
  where p xs = (2 :: SInteger) `notElem` xs .=> (filter (.> 2) xs .== filter (.>= 2) xs)

-- | The 'filterEx' example above, except we get a counter-example if @2@ can be in the list. Note that
-- we don't need the induction tactic here.
--
-- >>> filterEx2 `catch` (\(_ :: SomeException) -> pure ())
-- Lemma: filterEx2
-- *** Failed to prove filterEx2.
-- Falsifiable. Counter-example:
--   xs = [2] :: [Integer]
filterEx2 :: IO ()
filterEx2 = runKD $ do
        let p :: SList Integer -> SBool
            p xs = filter (.> 2) xs .== filter (.>= 2) xs

        lemma "filterEx2" (\(Forall @"xs" xs) -> p xs) []

        pure ()

-- * Map, append, and reverse

-- | @map f (xs ++ ys) == map f xs ++ map f ys@
--
-- >>> mapAppend (uninterpret "f")
-- Lemma: mapAppend                        Q.E.D.
-- [Proven] mapAppend
mapAppend :: (SA -> SB) -> IO Proof
mapAppend f = runKD $ do
   let p :: SList A -> SList A -> SBool
       p xs ys = map f (xs ++ ys) .== map f xs ++ map f ys

   lemma "mapAppend"
         (\(Forall @"xs" xs) (Forall @"ys" ys) -> p xs ys)
         []

-- | @map f . reverse == reverse . map f@
--
-- >>> mapReverse
-- Lemma: mapAppend                        Q.E.D.
-- Inductive lemma: mapReverse
--   Base: mapReverse.Base                 Q.E.D.
--   Help: mapReverse.L1 vs L2             Q.E.D.
--   Help: mapReverse.L2 vs L3             Q.E.D.
--   Help: mapReverse.L3 vs L4             Q.E.D.
--   Help: mapReverse.L4 vs L5             Q.E.D.
--   Help: mapReverse.R1 vs R2             Q.E.D.
--   Help: mapReverse.R2 vs R3             Q.E.D.
--   Help: mapReverse.L5 vs R3             Q.E.D.
--   Step: mapReverse.Step                 Q.E.D.
-- [Proven] mapReverse
mapReverse :: IO Proof
mapReverse = runKD $ do
     let p :: (SA -> SB) -> SList A -> SBool
         p g xs = reverse (map g xs) .== map g (reverse xs)

         -- For an arbitrary uninterpreted function 'f':
         f :: SA -> SB
         f = uninterpret "f"

     mApp <- use (mapAppend f)

     induct "mapReverse"
            (\(Forall @"xs" xs) -> p f xs)
            (\x xs -> ( [ reverse (map f (x .: xs))
                        , reverse (f x .: map f xs)
                        , reverse (map f xs) ++ singleton (f x)
                        , map f (reverse xs) ++ singleton (f x)     -- inductive hypothesis
                        , map f (reverse xs) ++ map f (singleton x)
                        ]
                      , [ map f (reverse (x .: xs))
                        , map f (reverse xs ++ singleton x)
                        , map f (reverse xs) ++ map f (singleton x)
                        ]
                      ))
          [mApp]

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
         []

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
         []

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

  lemma "foldrMapFusion" (\(Forall @"xs" xs) -> p xs) []

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
-- Axiom: f a == b
-- Axiom: f (g x) = h x (f y)
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

   lemma "foldrFusion" (\(Forall @"xs" xs) -> p xs) [h1, h2]

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
          []

-- * Foldl over append

-- | @foldl f a (xs ++ ys) == foldl f (foldl f a xs) ys@
--
-- We have:
--
-- >>> foldlOverAppend
-- Lemma: foldlOverAppend                  Q.E.D.
-- [Proven] foldlOverAppend
--
-- Note that the proof crucially relies on a generalized version of the theorem, where we have
-- to generalize @a@ to be an arbitrary value. Hence the quantified version we use, which reads:
--
-- @forall a. foldl f a (xs ++ ys) == foldl f (foldl f a xs) ys@
--
-- If we don't do this generalization, the inductive step cannot use the new value of the seed,
-- and hence won't converge.
foldlOverAppend :: IO Proof
foldlOverAppend = runKD $ do
   let f :: SA -> SA -> SA
       f = uninterpret "f"

       p xs ys = quantifiedBool $ \(Forall a) -> foldl f a (xs ++ ys) .== foldl f (foldl f a xs) ys

   lemma "foldlOverAppend"
         (\(Forall @"xs" xs) (Forall @"ys" ys) -> p xs ys)
         []

-- * Foldr-foldl correspondence

-- | @foldr f e xs == foldl (flip f) e (reverse xs)@
--
-- We have:
--
-- >>> foldrFoldlDuality
-- Lemma: foldlOverAppend                  Q.E.D.
-- Inductive lemma: foldrFoldlDuality
--   Base: foldrFoldlDuality.Base          Q.E.D.
--   Help: foldrFoldlDuality.L1 vs L2      Q.E.D.
--   Help: foldrFoldlDuality.L2 vs L3      Q.E.D.
--   Help: foldrFoldlDuality.R1 vs R2      Q.E.D.
--   Help: foldrFoldlDuality.R2 vs R3      Q.E.D.
--   Help: foldrFoldlDuality.R3 vs R4      Q.E.D.
--   Help: foldrFoldlDuality.R4 vs R5      Q.E.D.
--   Help: foldrFoldlDuality.R5 vs R6      Q.E.D.
--   Help: foldrFoldlDuality.L3 vs R6      Q.E.D.
--   Step: foldrFoldlDuality.Step          Q.E.D.
-- [Proven] foldrFoldlDuality
foldrFoldlDuality :: IO Proof
foldrFoldlDuality = runKD $ do
   let f :: SA -> SB -> SB
       f = uninterpret "f"

       p e xs = foldr f e xs .== foldl (flip f) e (reverse xs)

   -- An instance of foldlOverAppend above, except for our chosen f here which has a different type:
   -- Note the quantification of @e@ below is important since the recursive call changes the value.
   foa <- do let apE e xs ys = foldl (flip f) e (xs ++ ys) .== foldl (flip f) (foldl (flip f) e xs) ys
                 ap    xs ys = quantifiedBool $ \(Forall e) -> apE e xs ys
             lemma "foldlOverAppend"
                   (\(Forall @"xs" xs) (Forall @"ys" ys) -> ap xs ys)
                   []

   induct "foldrFoldlDuality"
          (\(Forall @"e" e) (Forall @"xs" xs) -> p e xs)
          (\e x xs -> ( [ foldr f e (x .: xs)
                        , x `f` foldr f e xs
                        , x `f` foldl (flip f) e (reverse xs)   -- inductive hypothesis
                        ]
                      , [ foldl (flip f) e (reverse (x .: xs))
                        , foldl (flip f) e (reverse xs ++ singleton x)
                        , foldl (flip f) (foldl (flip f) e (reverse xs)) (singleton x)  -- foa
                        , foldl (flip f) (flip f (foldl (flip f) e (reverse xs)) x) nil
                        , flip f (foldl (flip f) e (reverse xs)) x
                        , x `f` foldl (flip f) e (reverse xs)
                        ]
                      ))
          [foa]

-- * Foldr-foldl duality, generalized

-- | Given:
--
-- @
--     x \@ (y \@ z) = (x \@ y) \@ z     (associativity of @)
-- and e \@ x = x                     (left unit)
-- and x \@ e = x                     (right unit)
-- @
--
-- Prove:
--
-- @
--     foldr (\@) e xs = foldl (\@) e xs
-- @
--
-- We have:
--
-- >>> foldrFoldlDualityGeneralized
-- Axiom: @ is associative
-- Axiom: e is left unit
-- Axiom: e is right unit
-- Inductive lemma: foldl over @
--   Base: foldl over @.Base               Q.E.D.
--   Help: foldl over @.L1 vs L2           Q.E.D.
--   Help: foldl over @.L2 vs L3           Q.E.D.
--   Help: foldl over @.L3 vs L4           Q.E.D.
--   Help: foldl over @.R1 vs R2           Q.E.D.
--   Help: foldl over @.R2 vs R3           Q.E.D.
--   Help: foldl over @.R3 vs R4           Q.E.D.
--   Help: foldl over @.L4 vs R4           Q.E.D.
--   Step: foldl over @.Step               Q.E.D.
-- Inductive lemma: foldrFoldlDuality
--   Base: foldrFoldlDuality.Base          Q.E.D.
--   Help: foldrFoldlDuality.L1 vs L2      Q.E.D.
--   Help: foldrFoldlDuality.L2 vs L3      Q.E.D.
--   Help: foldrFoldlDuality.L3 vs L4      Q.E.D.
--   Help: foldrFoldlDuality.L4 vs L5      Q.E.D.
--   Help: foldrFoldlDuality.R1 vs R2      Q.E.D.
--   Help: foldrFoldlDuality.R2 vs R3      Q.E.D.
--   Help: foldrFoldlDuality.L5 vs R3      Q.E.D.
--   Step: foldrFoldlDuality.Step          Q.E.D.
-- [Proven] foldrFoldlDuality
foldrFoldlDualityGeneralized :: IO Proof
foldrFoldlDualityGeneralized  = runKD $ do
   let (@) :: SA -> SA -> SA
       (@) = uninterpret "|@|"

       e :: SA
       e = uninterpret "e"

   assoc <- axiom "@ is associative" (\(Forall @"x" x) (Forall @"y" y) (Forall @"z" z) -> x @ (y @ z) .== (x @ y) @ z)
   lunit <- axiom "e is left unit"   (\(Forall @"x" x) -> e @ x .== x)
   runit <- axiom "e is right unit"  (\(Forall @"x" x) -> x @ e .== x)

   -- Helper: foldl (@) (y @ z) xs = y @ foldl (@) z xs
   -- Note that we prove the more generalized lemma over forall-z, as the
   -- inductive case requires a different substitution.
   h <- do let hp y z xs = foldl (@) (y @ z) xs .== y @ foldl (@) z xs
           induct "foldl over @"
                  (\(Forall @"y" y) (Forall @"xs" xs) -> quantifiedBool $ \(Forall z) -> hp y z xs)
                  (\y x xs -> let z = uninterpret "z"
                              in ( [ foldl (@) (y @ z) (x .: xs)
                                   , foldl (@) ((y @ z) @ x) xs
                                   , foldl (@) (y @ (z @ x)) xs
                                   , foldl (@) y (z @ x .: xs)
                                   ]
                                 , [ y @ foldl (@) z (x .: xs)
                                   , y @ foldl (@) (z @ x) xs    -- inductive hypothesis, where z = z @ x in the inductive case
                                   , foldl (@) (y @ (z @ x)) xs
                                   , foldl (@) y (z @ x .: xs)
                                   ]))
                  [assoc]

   let p xs = foldr (@) e xs .== foldl (@) e xs

   induct "foldrFoldlDuality"
          (\(Forall @"xs" xs) -> p xs)
          (\x xs -> ( [ foldr (@) e (x .: xs)
                      , x @ foldr (@) e xs
                      , x @ foldl (@) e xs    -- inductive hypothesis
                      , foldl (@) (x @ e) xs  -- helper
                      , foldl (@) x xs
                      ]
                    , [ foldl (@) e (x .: xs)
                      , foldl (@) (e @ x) xs
                      , foldl (@) x xs
                      ]))
          [assoc, lunit, runit, h]

-- * Another foldl-foldr correspondence

-- | Given:
--
-- @
--        (x \<+> y) \<*> z = x \<+> (y \<*> z)
--   and  x \<+> e = e \<*> x
-- @
--
-- Proves:
--
-- @
--    foldr (\<+>) e xs = foldl (\<*>) e xs
-- @
--
-- In Bird's Introduction to Functional Programming book (2nd edition) this is called the second duality theorem. We have:
--
-- >>> foldrFoldl
-- Axiom: <+> over <*>
-- Axiom: unit
-- Inductive lemma: foldl over <*>/<+>
--   Base: foldl over <*>/<+>.Base         Q.E.D.
--   Help: foldl over <*>/<+>.L1 vs L2     Q.E.D.
--   Help: foldl over <*>/<+>.L2 vs L3     Q.E.D.
--   Help: foldl over <*>/<+>.L3 vs L4     Q.E.D.
--   Help: foldl over <*>/<+>.R1 vs R2     Q.E.D.
--   Help: foldl over <*>/<+>.L4 vs R2     Q.E.D.
--   Step: foldl over <*>/<+>.Step         Q.E.D.
-- Inductive lemma: foldrFoldl
--   Base: foldrFoldl.Base                 Q.E.D.
--   Help: foldrFoldl.L1 vs L2             Q.E.D.
--   Help: foldrFoldl.L2 vs L3             Q.E.D.
--   Help: foldrFoldl.R1 vs R2             Q.E.D.
--   Help: foldrFoldl.R2 vs R3             Q.E.D.
--   Help: foldrFoldl.R3 vs R4             Q.E.D.
--   Help: foldrFoldl.L3 vs R4             Q.E.D.
--   Step: foldrFoldl.Step                 Q.E.D.
-- [Proven] foldrFoldl
foldrFoldl :: IO Proof
foldrFoldl = runKD $ do

   let -- Declare the operators as uninterpreted functions
       (<+>) :: SA -> SB -> SB
       (<+>) = uninterpret "<+>"

       (<*>) :: SB -> SA -> SB
       (<*>) = uninterpret "<*>"

       -- The unit element
       e :: SB
       e = uninterpret "e"

   -- Assumptions about the operators

   -- (x <+> y) <*> z == x <+> (y <*> z)
   axm1 <- axiom "<+> over <*>" $ \(Forall @"x" x) (Forall @"y" y) (Forall @"z" z) -> (x <+> y) <*> z .== x <+> (y <*> z)

   -- x <+> e == e <*> x
   axm2 <- axiom "unit" $ \(Forall @"x" x) -> x <+> e .== e <*> x

   -- Helper: x <+> foldl (<*>) y xs == foldl (<*>) (x <+> y) xs
   -- NB. We prove this so y is explicitly quantified, as the inductive hypothesis needs to
   -- instantiate it using a different expression, where @y@ will get @y <*> z@.
   helper <- do
      let hp x y xs = x <+> foldl (<*>) y xs .== foldl (<*>) (x <+> y) xs

      induct "foldl over <*>/<+>"
             (\(Forall @"x" x) (Forall @"xs" xs) -> quantifiedBool $ \(Forall y) -> hp x y xs)
             -- Using z to avoid confusion with the variable x already present, following Bird.
             (\x z xs -> let y = uninterpret "y"
                         in ( [ x <+> foldl (<*>) y (z .: xs)
                              , x <+> foldl (<*>) (y <*> z) xs
                              , foldl (<*>) (x <+> (y <*> z)) xs  -- inductive hypothesis, y gets y <*> z
                              , foldl (<*>) ((x <+> y) <*> z) xs  -- axiom 1
                              ]
                            , [ foldl (<*>) (x <+> y) (z .: xs)
                              , foldl (<*>) ((x <+> y) <*> z) xs
                              ]))
             [axm1]

   let -- Equivalence predicate
       p :: SList A -> SBool
       p xs = foldr (<+>) e xs .== foldl (<*>) e xs

   -- Final proof:
   induct "foldrFoldl"
          (\(Forall @"xs" xs) -> p xs)
          (\x xs -> ( [ foldr (<+>) e (x .: xs)
                      , x <+> foldr (<+>) e xs     -- inductive hypothesis
                      , x <+> foldl (<*>) e xs
                      ]
                    , [ foldl (<*>) e (x .: xs)
                      , foldl (<*>) (e <*> x) xs
                      , foldl (<*>) (x <+> e) xs   -- axm2
                      , x <+> foldl (<*>) e xs     -- helper
                      ]))
          [axm2, helper]

-- * Bookkeeping law

-- | Provided @f@ is associative and @a@ is its both left and right-unit:
--
-- @foldr f a . concat == foldr f a . map (foldr f a)@
--
-- We have:
--
-- >>> bookKeeping
-- Axiom: f is associative
-- Axiom: a is right-unit
-- Axiom: a is left-unit
-- Lemma: foldrOverAppend                  Q.E.D.
-- Inductive lemma: foldBase
--   Base: foldBase.Base                   Q.E.D.
--   Help: foldBase.L1 vs L2               Q.E.D.
--   Help: foldBase.L2 vs L3               Q.E.D.
--   Help: foldBase.R1 vs R2               Q.E.D.
--   Help: foldBase.R2 vs R3               Q.E.D.
--   Help: foldBase.L3 vs R3               Q.E.D.
--   Step: foldBase.Step                   Q.E.D.
-- Inductive lemma: bookKeeping
--   Base: bookKeeping.Base                Q.E.D.
--   Help: bookKeeping.L1 vs L2            Q.E.D.
--   Help: bookKeeping.L2 vs L3            Q.E.D.
--   Help: bookKeeping.L3 vs L4            Q.E.D.
--   Help: bookKeeping.L4 vs L5            Q.E.D.
--   Help: bookKeeping.L5 vs L6            Q.E.D.
--   Help: bookKeeping.R1 vs R2            Q.E.D.
--   Help: bookKeeping.R2 vs R3            Q.E.D.
--   Help: bookKeeping.R3 vs R4            Q.E.D.
--   Help: bookKeeping.L6 vs R4            Q.E.D.
--   Step: bookKeeping.Step                Q.E.D.
-- [Proven] bookKeeping
--
-- NB. As of early 2025, we cannot express the above theorem in SBV directly, since it involves nested lambdas.
-- (On the right hand side map has an argument that is represented as a foldr, which itself has a lambda.) As
-- SMTLib moves to a higher-order logic, we intend to make such expressions readily expressable. In the mean time,
-- we use an equivalent (albeit roundabout) version, where we define map-foldr combo as a recursive function ourselves.
--
-- NB. This theorem does not hold if @f@ does not have a left-unit! Consider the input @[[], [x]]@. Left hand side reduces to
-- @x@, while the right hand side reduces to: @f a x@. And unless @f@ is commutative or @a@ is not also a left-unit,
-- then one can find a counter-example. (Aside: if both left and right units exist for a binary operator, then they
-- are necessarily the same element, since @l = f l r = r@. So, an equivalent statement could simply say @f@ has
-- both left and right units.) A concrete counter-example is:
--
-- @
--   data T = A | B | C
--
--   f :: T -> T -> T
--   f C A = A
--   f C B = A
--   f x _ = x
-- @
--
-- You can verify @f@ is associative. Also note that @C@ is the right-unit for @f@, but it isn't the left-unit.
-- In fact, @f@ has no-left unit by the above argument. In this case, the bookkeeping law produces @B@ for
-- the left-hand-side, and @A@ for the right-hand-side for the input @[[], [B]]@.
--
bookKeeping :: IO Proof
bookKeeping = runKD $ do
   let a :: SA
       a = uninterpret "a"

       f :: SA -> SA -> SA
       f = uninterpret "f"

       -- Fuse map (foldr f a) in the theorem into one call to avoid nested lambdas. See above note.
       mapFoldr :: SA -> SList [A] -> SList A
       mapFoldr = smtFunction "mapFoldr" $ \e xss -> ite (null xss)
                                                         nil
                                                         (foldr f e (head xss) .: mapFoldr e (tail xss))

       p xss = foldr f a (concat xss) .== foldr f a (mapFoldr a xss)

   assoc <- axiom "f is associative" (\(Forall @"x" x) (Forall @"y" y) (Forall @"z" z) -> x `f` (y `f` z) .== (x `f` y) `f` z)
   rUnit <- axiom "a is right-unit"  (\(Forall @"x" x) -> x `f` a .== x)
   lUnit <- axiom "a is left-unit"   (\(Forall @"x" x) -> a `f` x .== x)

   foa <- use foldrOverAppend

   -- Helper:
   --   foldr f y xs = foldr f a xs `f` y
   helper <- induct "foldBase"
                    (\(Forall @"b" y) (Forall @"xs" xs) -> foldr f y xs .== foldr f a xs `f` y)
                    (\y x xs -> ( [ foldr f y (x .: xs)
                                  , x `f` foldr f y xs
                                  , x `f` (foldr f a xs `f` y)   -- inductive hypothesis
                                  ]
                                , [ foldr f a (x .: xs) `f` y
                                  , (x `f` foldr f a xs) `f` y
                                  , x `f` (foldr f a xs `f` y)
                                  ]))
                    [assoc, lUnit]

   induct "bookKeeping"
          (\(Forall @"xss" xss) -> p xss)
          (\xs xss -> let y = foldr f a (mapFoldr a xss)
                      in  ( [ foldr f a (concat (xs .: xss))
                            , foldr f a (xs ++ concat xss)
                            , foldr f (foldr f a (concat xss)) xs      -- foa: foldr-over-append
                            , foldr f (foldr f a (mapFoldr a xss)) xs  -- inductive hypothesis
                            , foldr f y xs                             -- helper
                            , foldr f a xs `f` y
                            ]
                          , [ foldr f a (mapFoldr a (xs .: xss))
                            , foldr f a (foldr f a xs .: mapFoldr a xss)
                            , foldr f a xs `f` foldr f a (mapFoldr a xss)
                            , foldr f a xs `f` y
                            ]))
          [assoc, rUnit, foa, helper]
