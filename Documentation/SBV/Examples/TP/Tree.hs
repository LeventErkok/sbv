-----------------------------------------------------------------------------
-- |
-- Module    : Documentation.SBV.Examples.TP.Tree
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Proofs about binary tree mirroring, in-order traversal (flattening), and
-- tree sizes.
-----------------------------------------------------------------------------

{-# LANGUAGE CPP                 #-}
{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE FlexibleInstances   #-}
{-# LANGUAGE OverloadedLists     #-}
{-# LANGUAGE QuasiQuotes         #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell     #-}
{-# LANGUAGE TypeAbstractions    #-}
{-# LANGUAGE TypeApplications    #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module Documentation.SBV.Examples.TP.Tree where

import Prelude hiding (length, head, tail, null, reverse, (++))

import Data.SBV
import Data.SBV.List
import Data.SBV.TP

import Data.Proxy (Proxy(..))

#ifdef DOCTEST
-- $setup
-- >>> :set -XTypeApplications
-- >>> import Data.SBV
-- >>> import Data.SBV.TP
#endif

-- * Binary tree definition

-- | A classic parametric binary tree data type.
data Tree a = Leaf
            | Node (Tree a) a (Tree a)
            deriving (Show, Eq)

-- | Generate symbolic counterpart 'STree'.
mkSymbolic [''Tree]

-- * Tree operations

-- | Mirror a tree by recursively swapping its left and right subtrees.
--
-- >>> mirror (sNode (sNode sLeaf (1 :: SInteger) sLeaf) 2 sLeaf)
-- sNode sLeaf 2 (sNode sLeaf 1 sLeaf) :: STree Integer
mirror :: SymVal a => STree a -> STree a
mirror = smtFunction "mirror"
       $ \t -> [sCase| t of
                   Leaf       -> sLeaf
                   Node l x r -> sNode (mirror r) x (mirror l)
               |]

-- | Flatten a tree into a list via in-order traversal.
--
-- >>> flatten (sNode (sNode sLeaf (1 :: SInteger) sLeaf) 2 (sNode sLeaf 3 sLeaf))
-- [1,2,3] :: [SInteger]
flatten :: SymVal a => STree a -> SList a
flatten = smtFunction "flatten"
        $ \t -> [sCase| t of
                    Leaf       -> []
                    Node l x r -> flatten l ++ [x] ++ flatten r
                |]

-- | Calculate the number of internal nodes in a tree.
--
-- >>> treeSize (sNode (sNode sLeaf (1 :: SInteger) sLeaf) 2 sLeaf)
-- 2 :: SInteger
treeSize :: SymVal a => STree a -> SInteger
treeSize = smtFunction "treeSize"
         $ \t -> [sCase| t of
                     Leaf       -> 0
                     Node l _ r -> 1 + treeSize l + treeSize r
                 |]

-- | The size is always non-negative.
--
-- >>> runTP $ treeSizePos @Integer
-- Lemma: treeSizePos @Integer    Q.E.D.
-- Functions proven terminating: treeSize
-- [Proven] treeSizePos @Integer :: Ɐt ∷ (Tree Integer) → Bool
treeSizePos :: forall a. SymVal a => TP (Proof (Forall "t" (Tree a) -> SBool))
treeSizePos = inductiveLemma (atProxy (Proxy @a) "treeSizePos") (\(Forall t) -> treeSize t .>= 0) []

-- * Correctness proofs

-- | Proves that mirroring a tree twice yields the original tree:
--
-- @mirror (mirror t) == t@
--
-- >>> runTP $ mirrorInvolution @Integer
-- Inductive lemma: mirrorInvolution
--   Step: Base                      Q.E.D.
--   Step: 1                         Q.E.D.
--   Step: 2                         Q.E.D.
--   Step: 3                         Q.E.D.
--   Step: 4                         Q.E.D.
--   Step: 5                         Q.E.D.
--   Result:                         Q.E.D.
-- Functions proven terminating: mirror
-- [Proven] mirrorInvolution :: Ɐt ∷ Tree Integer → Bool
mirrorInvolution :: forall a. SymVal a => TP (Proof (Forall "t" (Tree a) -> SBool))
mirrorInvolution = do
  tsp <- recall $ treeSizePos @a

  sInduct (atProxy (Proxy @a) "mirrorInvolution")
          (\(Forall @"t" t) -> mirror (mirror t) .== t)
          (treeSize, [proofOf tsp]) $
          \ih t -> [] |- [pCase| t of
                            Leaf       -> mirror (mirror sLeaf)
                                       =: mirror sLeaf
                                       =: sLeaf
                                       =: qed
                            Node l x r -> mirror (mirror (sNode l x r))
                                       =: mirror (sNode (mirror r) x (mirror l))
                                       =: sNode (mirror (mirror l)) x (mirror (mirror r))
                                       ?? ih `at` Inst @"t" l
                                       =: sNode l x (mirror (mirror r))
                                       ?? ih `at` Inst @"t" r
                                       =: sNode l x r
                                       =: qed
                         |]

-- | Proves that mirroring a tree preserves its size:
--
-- @treeSize (mirror t) == treeSize t@
--
-- >>> runTP $ sizeMirror @Integer
-- Inductive lemma: sizeMirror
--   Step: Base                      Q.E.D.
--   Step: 1                         Q.E.D.
--   Step: 2                         Q.E.D.
--   Step: 3                         Q.E.D.
--   Step: 4                         Q.E.D.
--   Step: 5                         Q.E.D.
--   Result:                         Q.E.D.
-- Functions proven terminating: mirror, treeSize
-- [Proven] sizeMirror :: Ɐt ∷ Tree Integer → Bool
sizeMirror :: forall a. SymVal a => TP (Proof (Forall "t" (Tree a) -> SBool))
sizeMirror = do
  tsp <- recall $ treeSizePos @a

  sInduct (atProxy (Proxy @a) "sizeMirror")
          (\(Forall @"t" t) -> treeSize (mirror t) .== treeSize t)
          (treeSize, [proofOf tsp]) $
          \ih t -> [] |- [pCase| t of
                            Leaf       -> treeSize (mirror (sLeaf :: STree a))
                                       =: treeSize (sLeaf :: STree a)
                                       =: qed
                            Node l x r -> treeSize (mirror (sNode l x r))
                                       =: treeSize (sNode (mirror r) x (mirror l))
                                       =: 1 + treeSize (mirror r) + treeSize (mirror l)
                                       ?? ih `at` Inst @"t" r
                                       =: 1 + treeSize r + treeSize (mirror l)
                                       ?? ih `at` Inst @"t" l
                                       =: 1 + treeSize r + treeSize l
                                       =: treeSize (sNode l x r)
                                       =: qed
                         |]

-- | Proves that in-order traversal of a mirrored tree is equal to the reverse
-- of the in-order traversal of the original tree:
--
-- @flatten (mirror t) == reverse (flatten t)@
--
-- >>> runTP $ flattenMirror @Integer
-- Inductive lemma: flattenMirror
--   Step: Base                      Q.E.D.
--   Step: 1                         Q.E.D.
--   Step: 2                         Q.E.D.
--   Step: 3                         Q.E.D.
--   Step: 4                         Q.E.D.
--   Step: 5                         Q.E.D.
--   Result:                         Q.E.D.
-- Functions proven terminating: flatten, mirror, sbv.reverse
-- [Proven] flattenMirror :: Ɐt ∷ Tree Integer → Bool
flattenMirror :: forall a. SymVal a => TP (Proof (Forall "t" (Tree a) -> SBool))
flattenMirror = do
  tsp <- recall $ treeSizePos @a

  sInduct (atProxy (Proxy @a) "flattenMirror")
          (\(Forall @"t" t) -> flatten (mirror t) .== reverse (flatten t))
          (treeSize, [proofOf tsp]) $
          \ih t -> [] |- [pCase| t of
                            Leaf       -> flatten (mirror sLeaf)
                                       =: flatten sLeaf
                                       =: ([] :: SList a)
                                       =: reverse []
                                       =: reverse (flatten sLeaf)
                                       =: qed
                            Node l x r -> flatten (mirror (sNode l x r))
                                       =: flatten (sNode (mirror r) x (mirror l))
                                       =: flatten (mirror r) ++ [x] ++ flatten (mirror l)
                                       ?? ih `at` Inst @"t" r
                                       =: reverse (flatten r) ++ [x] ++ flatten (mirror l)
                                       ?? ih `at` Inst @"t" l
                                       =: reverse (flatten r) ++ [x] ++ reverse (flatten l)
                                       =: reverse (flatten (sNode l x r))
                                       =: qed
                         |]
