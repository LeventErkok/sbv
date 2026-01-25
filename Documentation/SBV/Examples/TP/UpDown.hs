-----------------------------------------------------------------------------
-- |
-- Module    : Documentation.SBV.Examples.TP.UpDown
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Proves @reverse (down n) = up n@.
--
-- This problem is motivated by an ACL2 midterm exam question, from Fall 2011.
-- See: <https://www.cs.utexas.edu/~moore/classes/cs389r/midterm-answers.lisp>.
-----------------------------------------------------------------------------

{-# LANGUAGE CPP              #-}
{-# LANGUAGE DataKinds        #-}
{-# LANGUAGE OverloadedLists  #-}
{-# LANGUAGE QuasiQuotes      #-}
{-# LANGUAGE TypeAbstractions #-}
{-# LANGUAGE TypeApplications #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module Documentation.SBV.Examples.TP.UpDown where

import Prelude hiding (reverse, (++))

import Data.SBV
import Data.SBV.TP
import Data.SBV.List

import Documentation.SBV.Examples.TP.Lists
import Documentation.SBV.Examples.TP.Peano

#ifdef DOCTEST
-- $setup
-- >>> import Data.SBV.TP
#endif

-- | Construct a list of size @n@, containing numbers @1@ to @n@.
--
-- >>> up 0
-- [] :: [SInteger]
-- >>> up 5
-- [1,2,3,4,5] :: [SInteger]
up :: SNat -> SList Integer
up n = upAcc n []

-- | Keep consing the first argument on to the accumulator, until we hit zero. After that, return the second argument.
-- Normally, we'd define this as a local function, but the definition needs to be visible for the proofs.
upAcc :: SNat -> SList Integer -> SList Integer
upAcc = smtFunction "up" $ \n lst -> [sCase|Nat n of
                                       Zero   -> lst
                                       Succ p -> upAcc p (n2i n .: lst)
                                     |]

-- | Construct a list of size @n@, containing numbers @n-1@ down to @0@.
--
-- >>> down 0
-- [] :: [SInteger]
-- >>> down 5
-- [5,4,3,2,1] :: [SInteger]
down :: SNat -> SList Integer
down = smtFunction "down" $ \n -> [sCase|Nat n of
                                     Zero   -> nil
                                     Succ p -> n2i n .: down p
                                  |]

-- | Prove that @reverse (down n)@ is the same as @up n@
--
-- >>> runTP upDown
-- Lemma: n2iNonNeg                        Q.E.D.
-- Lemma: revCons                          Q.E.D.
-- Inductive lemma (strong): upDownGen
--   Step: Measure is non-negative         Q.E.D.
--   Step: 1 (2 way case split)
--     Step: 1.1                           Q.E.D.
--     Step: 1.2.1                         Q.E.D.
--     Step: 1.2.2                         Q.E.D.
--     Step: 1.2.3                         Q.E.D.
--     Step: 1.2.4                         Q.E.D.
--     Step: 1.2.5                         Q.E.D.
--     Step: 1.Completeness                Q.E.D.
--   Result:                               Q.E.D.
-- Lemma: upDown                           Q.E.D.
-- [Proven] upDown :: Ɐn ∷ Nat → Bool
upDown :: TP (Proof (Forall "n" Nat -> SBool))
upDown = do
   n2inn <- recall "n2iNonNeg" n2iNonNeg
   rc    <- recall "revCons"   (revCons @Integer)

   -- We first generalize the theorem, to make it inductive
   upDownGen <- sInduct "upDownGen"
           (\(Forall @"n" n) (Forall @"xs" xs) -> reverse (down n) ++ xs .== upAcc n xs)
           (\n _ -> n2i n, [proofOf n2inn]) $
           \ih n xs -> [] |- cases [ isZero n ==> trivial
                                   , isSucc n ==> let p = getSucc_1 n
                                               in reverse (down (sSucc p)) ++ xs
                                               =: reverse (n2i n .: down p) ++ xs
                                               ?? rc
                                               =: reverse (down p) ++ [n2i n] ++ xs
                                               ?? ih `at` (Inst @"n" p, Inst @"xs" ([n2i n] ++ xs))
                                               =: upAcc p ([n2i n] ++ xs)
                                               =: upAcc p (n2i n .: xs)
                                               =: upAcc n xs
                                               =: qed
                                   ]

   -- The theorem we want to prove follows by instantiating the list at empty, and
   -- the SMT solver can figure it out by itself
   lemma "upDown"
         (\(Forall n) -> reverse (down n) .== up n)
         [proofOf upDownGen]
