-----------------------------------------------------------------------------
-- |
-- Module    : Documentation.SBV.Examples.TP.Huffman
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Proving the roundtrip correctness of Huffman encoding: for any symbol @s@
-- that is a member of a binary tree @t@, decoding the encoded path yields @s@.
--
-- We define a simple binary tree (no weights needed for roundtrip), encode a
-- symbol by finding its path from root to leaf, and decode by following a bit
-- path through the tree. The main theorem shows these are inverses.
-----------------------------------------------------------------------------

{-# LANGUAGE CPP               #-}
{-# LANGUAGE DataKinds         #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE QuasiQuotes       #-}
{-# LANGUAGE TemplateHaskell   #-}
{-# LANGUAGE TypeAbstractions  #-}
{-# LANGUAGE TypeApplications  #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module Documentation.SBV.Examples.TP.Huffman where

import Prelude hiding (null, head, tail, length)

import Data.SBV
import Data.SBV.List
import Data.SBV.TP

#ifdef DOCTEST
-- $setup
-- >>> import Data.SBV
-- >>> import Data.SBV.TP
#endif

-- * Huffman tree

-- | A binary tree with integer symbols at the leaves.
data HTree = Tip { symbol :: Integer }
           | Bin { left   :: HTree
                 , right  :: HTree
                 }

-- | Create a symbolic version of HTree.
mkSymbolic [''HTree]

-- * Tree operations

-- | Size of a tree. Used as a termination measure for strong induction.
treeSize :: SHTree -> SInteger
treeSize = smtFunction "treeSize"
         $ \t -> [sCase| t of
                    Tip _   -> 1
                    Bin l r -> 1 + treeSize l + treeSize r
                 |]

-- | Check if a symbol is a member of the tree.
member :: SInteger -> SHTree -> SBool
member = smtFunction "member"
       $ \s t -> [sCase| t of
                    Tip x   -> s .== x
                    Bin l r -> member s l .|| member s r
                 |]

-- * Encoding and decoding

-- | Encode a symbol by finding its path from root to leaf.
-- Returns a list of bits: 'sFalse' means go left, 'sTrue' means go right.
-- At a 'Tip', we return the empty path. At a 'Bin', we check membership
-- in the left subtree to decide which way to go.
findPath :: SInteger -> SHTree -> SList Bool
findPath = smtFunction "findPath"
         $ \s t -> [sCase| t of
                      Tip _   -> nil
                      Bin l r | member s l -> sFalse .: findPath s l
                              | True       -> sTrue  .: findPath s r
                   |]

-- | Decode a bit path through a tree, returning the symbol at the destination leaf.
-- At a 'Tip', we return the symbol (ignoring remaining bits). At a 'Bin',
-- we follow the first bit: 'sTrue' goes right, 'sFalse' goes left.
decode :: SList Bool -> SHTree -> SInteger
decode = smtFunction "decode"
       $ \bs t -> [sCase| t of
                     Tip x   -> x
                     Bin l r -> case bs of
                                  -- Empty bit-string at an internal node shouldn't happen
                                  -- with a valid encoding. If it does due to a bug, we
                                  -- return an arbitrary value, which would invalidate proofs.
                                  []                -> some "unreachable" (const sTrue)
                                  b : rest | b      -> decode rest r
                                           | True   -> decode rest l
                  |]

-- * Correctness

-- | Roundtrip property: for any symbol @s@ that is a member of tree @t@,
-- decoding the encoded path yields @s@.
--
-- >>> runTPWith (tpRibbon 60 cvc5) roundtrip
-- Lemma: treeSizePos                                          Q.E.D.
-- Inductive lemma (strong): huffmanRoundtrip
--   Step: Measure is non-negative                             Q.E.D.
--   Step: 1 (2 way case split)
--     Step: 1.1                                               Q.E.D.
--     Step: 1.2 (2 way case split)
--       Step: 1.2.1.1                                         Q.E.D.
--       Step: 1.2.1.2                                         Q.E.D.
--       Step: 1.2.2.1                                         Q.E.D.
--       Step: 1.2.2.2                                         Q.E.D.
--       Step: 1.2.Completeness                                Q.E.D.
--     Step: 1.Completeness                                    Q.E.D.
--   Result:                                                   Q.E.D.
-- Functions proven terminating: decode, findPath, member, treeSize
-- [Proven] huffmanRoundtrip :: Ɐs ∷ Integer → Ɐt ∷ HTree → Bool
roundtrip :: TP (Proof (Forall "s" Integer -> Forall "t" HTree -> SBool))
roundtrip = do
   tsPos <- inductiveLemma "treeSizePos"
                           (\(Forall @"t" t) -> treeSize t .>= 1)
                           []

   sInduct "huffmanRoundtrip"
     (\(Forall @"s" s) (Forall @"t" t) -> member s t .=> decode (findPath s t) t .== s)
     (\_ t -> treeSize t, [proofOf tsPos]) $
     \ih s t -> [member s t]
       |- decode (findPath s t) t .== s
       =: [pCase| t of
             Tip _   -> trivial

             Bin l r -> cases
               [ member s l
                   ==> decode (findPath s (sBin l r)) (sBin l r) .== s
                    ?? tsPos `at` Inst @"t" r
                    ?? ih `at` (Inst @"s" s, Inst @"t" l)
                    =: sTrue
                    =: qed

               , sNot (member s l)
                   ==> decode (findPath s (sBin l r)) (sBin l r) .== s
                    ?? tsPos `at` Inst @"t" l
                    ?? ih `at` (Inst @"s" s, Inst @"t" r)
                    =: sTrue
                    =: qed
               ]
          |]
