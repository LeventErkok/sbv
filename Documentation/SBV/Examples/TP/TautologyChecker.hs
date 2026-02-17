-----------------------------------------------------------------------------
-- |
-- Module    : Documentation.SBV.Examples.TP.TautologyChecker
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- A verified tautology checker (unordered BDD-style SAT solver) in SBV.
-- This is a port of the Imandra proof by Grant Passmore, originally
-- inspired by Boyer-Moore '79.
-- See <https://raw.githubusercontent.com/imandra-ai/imandrax-examples/refs/heads/main/src/tautology.iml>
--
-- We define a simple formula type with If-then-else, normalize formulas into a canonical form, and prove
-- both soundness and completeness of the tautology checker. The canonical form is essentially an
-- unordered-BDD, making it easy to evaluate it.
-----------------------------------------------------------------------------

{-# LANGUAGE CPP                 #-}
{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE FlexibleInstances   #-}
{-# LANGUAGE OverloadedLists     #-}
{-# LANGUAGE QuasiQuotes         #-}
{-# LANGUAGE TemplateHaskell     #-}
{-# LANGUAGE TypeAbstractions    #-}
{-# LANGUAGE TypeApplications    #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module Documentation.SBV.Examples.TP.TautologyChecker where

import Prelude hiding (null, head, tail, (++))

import Data.SBV
import Data.SBV.List
import Data.SBV.TP
import Data.SBV.Tuple

#ifdef DOCTEST
-- $setup
-- >>> import Data.SBV
-- >>> import Data.SBV.TP
#endif

-- * Formula representation

-- | A propositional formula with variables and if-then-else.
data Formula = FTrue
             | FFalse
             | Var Integer
             | If  Formula Formula Formula

-- | Make formulas symbolic.
mkSymbolic [''Formula]

-- * Measuring formulas

-- | Depth of nested If constructors in the condition position.
ifDepth :: SFormula -> SInteger
ifDepth = smtFunction "ifDepth" $ \f -> [sCase|Formula f of
                                           If c _ _ -> 1 + ifDepth c
                                           _        -> 0
                                        |]

-- | \(\text{ifDepth}(f) \geq 0\)
--
-- >>> runTP ifDepthNonNeg
-- Lemma: ifDepthNonNeg                    Q.E.D.
-- [Proven] ifDepthNonNeg :: Ɐf ∷ Formula → Bool
ifDepthNonNeg :: TP (Proof (Forall "f" Formula -> SBool))
ifDepthNonNeg = inductiveLemma "ifDepthNonNeg" (\(Forall f) -> ifDepth f .>= 0) []

-- | Complexity of a formula (for termination measure).
ifComplexity :: SFormula -> SInteger
ifComplexity = smtFunction "ifComplexity" $ \f ->
  [sCase|Formula f of
    If c l r -> ifComplexity c * (ifComplexity l + ifComplexity r)
    _        -> 1
  |]

-- | \(\text{ifComplexity}(f) > 0\)
--
-- >>> runTP ifComplexityPos
-- Lemma: ifComplexityPos                  Q.E.D.
-- [Proven] ifComplexityPos :: Ɐf ∷ Formula → Bool
ifComplexityPos :: TP (Proof (Forall "f" Formula -> SBool))
ifComplexityPos = inductiveLemma "ifComplexityPos" (\(Forall f) -> ifComplexity f .> 0) []

-- | The branches of an If have smaller complexity than the whole.
--
-- \(\text{ifComplexity}(c) < \text{ifComplexity}(\text{If}(c, l, r)) \land \text{ifComplexity}(l) < \text{ifComplexity}(\text{If}(c, l, r)) \land \text{ifComplexity}(r) < \text{ifComplexity}(\text{If}(c, l, r))\)
--
-- >>> runTP ifComplexitySmaller
-- Lemma: ifComplexityPos                  Q.E.D.
-- Lemma: ifComplexitySmaller              Q.E.D.
-- [Proven] ifComplexitySmaller :: Ɐc ∷ Formula → Ɐl ∷ Formula → Ɐr ∷ Formula → Bool
ifComplexitySmaller :: TP (Proof (Forall "c" Formula -> Forall "l" Formula -> Forall "r" Formula -> SBool))
ifComplexitySmaller = do
  icp <- recall "ifComplexityPos" ifComplexityPos

  lemma "ifComplexitySmaller"
        (\(Forall c) (Forall l) (Forall r) ->
           let ic = ifComplexity (sIf c l r)
           in ifComplexity c .< ic .&& ifComplexity l .< ic .&& ifComplexity r .< ic)
        [proofOf icp]

-- | The condition depth increases when wrapped in If.
--
-- \(\text{ifDepth}(\text{If}(c, l, r)) = 1 + \text{ifDepth}(c)\)
--
-- >>> runTP ifDepthSmaller
-- Lemma: ifDepthNonNeg                    Q.E.D.
-- Lemma: ifDepthSmaller                   Q.E.D.
-- [Proven] ifDepthSmaller :: Ɐc ∷ Formula → Ɐl ∷ Formula → Ɐr ∷ Formula → Bool
ifDepthSmaller :: TP (Proof (Forall "c" Formula -> Forall "l" Formula -> Forall "r" Formula -> SBool))
ifDepthSmaller = do
  idn <- recall "ifDepthNonNeg" ifDepthNonNeg

  lemma "ifDepthSmaller"
        (\(Forall c) (Forall l) (Forall r) ->
           ifDepth (sIf c l r) .== 1 + ifDepth c)
        [proofOf idn]

-- | The normalization transformation preserves complexity.
--
-- \(\text{ifComplexity}(\text{If}(p, \text{If}(q, l, r), \text{If}(s, l, r))) = \text{ifComplexity}(\text{If}(\text{If}(p, q, s), l, r))\)
--
-- >>> runTP normalizePreservesComplexity
-- Lemma: normalizePreservesComplexity
--   Step: 1                               Q.E.D.
--   Step: 2                               Q.E.D.
--   Step: 3                               Q.E.D.
--   Step: 4                               Q.E.D.
--   Result:                               Q.E.D.
-- [Proven] normalizePreservesComplexity :: Ɐp ∷ Formula → Ɐq ∷ Formula → Ɐs ∷ Formula → Ɐl ∷ Formula → Ɐr ∷ Formula → Bool
normalizePreservesComplexity :: TP (Proof (Forall "p" Formula -> Forall "q" Formula -> Forall "s" Formula -> Forall "l" Formula -> Forall "r" Formula -> SBool))
normalizePreservesComplexity = do

  -- This trivial lemma, unfortunately is needed below. I'm not sure why.
  helper <- lemma "helper"
                  (\(Forall @"a" a) (Forall @"b" b) (Forall @"c" c) -> a .== b .=> a * c .== b * (c :: SInteger))
                  []

  calc "normalizePreservesComplexity"
       (\(Forall p) (Forall q) (Forall s) (Forall l) (Forall r) ->
          ifComplexity (sIf p (sIf q l r) (sIf s l r)) .== ifComplexity (sIf (sIf p q s) l r)) $
       \p q s l r ->
         let cp = ifComplexity p
             cq = ifComplexity q
             cs = ifComplexity s
             cl = ifComplexity l
             cr = ifComplexity r
         in [] |- ifComplexity (sIf p (sIf q l r) (sIf s l r))
               =: cp * (ifComplexity (sIf q l r) + ifComplexity (sIf s l r))
               =: cp * (cq * (cl + cr) + cs * (cl + cr))
               =: cp * ((cq + cs) * (cl + cr))
               =: (cp * (cq + cs)) * (cl + cr)
               ?? helper `at` (Inst @"a" (ifComplexity (sIf p q s)), Inst @"b" (cp * (cq + cs)), Inst @"c" (cl + cr))
               =: ifComplexity (sIf p q s) * (cl + cr)
               =: ifComplexity (sIf p q s) * (ifComplexity l + ifComplexity r)
               =: ifComplexity (sIf (sIf p q s) l r)
               =: qed

-- * Normalization

-- | Check if a formula is in normal form (no nested If in condition position).
isNormal :: SFormula -> SBool
isNormal = smtFunction "isNormal" $ \f ->
  [sCase|Formula f of
    If c p q  -> sNot (isIf c) .&& isNormal p .&& isNormal q
    _         -> sTrue
  |]

-- | Normalize a formula by eliminating nested Ifs in condition position.
--
-- The key transformation is:
--
-- @
--   If (If (p, q, r), left, right)
--     =
--   If (p, If (q, left, right), If (r, left, right))
-- @
--
-- Note that this transformation increases the size of the formula, but reduces its complexity.
normalize :: SFormula -> SFormula
normalize = smtFunction "normalize" $ \f ->
  [sCase|Formula f of
    If c l r -> normalizeIf c l r
    _        -> f
  |]
 where normalizeIf :: SFormula -> SFormula -> SFormula -> SFormula
       normalizeIf = smtFunction "normalizeIf" $ \c thn els ->
          [sCase|Formula c of
            If p q r -> normalize (sIf p (sIf q thn els) (sIf r thn els))
            _        -> sIf c (normalize thn) (normalize els)
          |]


-- * Variable bindings

-- | A binding associates a variable ID with a boolean value.
data Binding = Binding { varId :: Integer
                       , value :: Bool
                       }

-- | Make bindings symbolic.
mkSymbolic [''Binding]

-- | Look up a variable in the binding list. If it's not in the list, then it's false.
lookUp :: SInteger -> SList Binding -> SBool
lookUp = smtFunction "lookUp" $ \vid bs ->
  ite (null bs)
      sFalse
      [sCase|Binding (head bs) of
         Binding bId bVal -> ite (vid .== bId)
                                 bVal
                                 (lookUp vid (tail bs))
      |]

-- | Check if a variable is assigned in the bindings.
isAssigned :: SInteger -> SList Binding -> SBool
isAssigned = smtFunction "isAssigned" $ \vid bs ->
  ite (null bs)
      sFalse
      [sCase|Binding (head bs) of
         Binding bId _ -> bId .== vid .|| isAssigned vid (tail bs)
      |]

-- | Add a binding assuming the variable is true.
assumeTrue :: SInteger -> SList Binding -> SList Binding
assumeTrue vid bs = sBinding vid sTrue .: bs

-- | Add a binding assuming the variable is false.
assumeFalse :: SInteger -> SList Binding -> SList Binding
assumeFalse vid bs = sBinding vid sFalse .: bs

-- * Formula evaluation

-- | Evaluate a formula under a binding environment.
eval :: SFormula -> SList Binding -> SBool
eval = smtFunction "eval" $ \f bs ->
  [sCase|Formula f of
    Var n    -> lookUp n bs
    If c l r -> ite (eval c bs) (eval l bs) (eval r bs)
    FTrue    -> sTrue
    FFalse   -> sFalse
  |]

-- * Tautology checking

-- | Check if a normalized formula is a tautology.
isTautology' :: SFormula -> SList Binding -> SBool
isTautology' = smtFunction "isTautology'" $ \f bs ->
  [sCase|Formula f of
    FTrue    -> sTrue
    FFalse   -> sFalse
    Var _    -> eval f bs
    If c l r -> isTautology'If c l r bs
  |]
 where isTautology'If :: SFormula -> SFormula -> SFormula -> SList Binding -> SBool
       isTautology'If = smtFunction "isTautology'If" $ \c l r bs ->
           [sCase|Formula c of
             Var n -> ite (isAssigned n bs)
                          (ite (eval (sVar n) bs)
                               (isTautology' l bs)
                               (isTautology' r bs))
                          (ite (isTautology' l (assumeTrue  n bs))
                               (isTautology' r (assumeFalse n bs))
                               sFalse)
             FTrue  -> isTautology' l bs
             FFalse -> isTautology' r bs
             _      -> sFalse  -- Contradicts isNormal assumption
           |]

-- | Main tautology checker.
isTautology :: SFormula -> SBool
isTautology f = isTautology' (normalize f) []

-- * Soundness proofs

-- | \(\text{lookUp}(x, a \mathbin{+\!\!+} b) = \text{if } \text{isAssigned}(x, a) \text{ then } \text{lookUp}(x, a) \text{ else } \text{lookUp}(x, b)\)
--
-- If we look up a variable in a concatenated binding list, we first check
-- the first list, and only if not found there, check the second.
--
-- >>> runTP lookUpStable
-- Inductive lemma: lookUpStable
--   Step: Base                            Q.E.D.
--   Step: 1 (2 way case split)
--     Step: 1.1.1                         Q.E.D.
--     Step: 1.1.2                         Q.E.D.
--     Step: 1.2.1                         Q.E.D.
--     Step: 1.2.2                         Q.E.D.
--     Step: 1.Completeness                Q.E.D.
--   Result:                               Q.E.D.
-- [Proven] lookUpStable :: Ɐa ∷ [Binding] → Ɐx ∷ Integer → Ɐb ∷ [Binding] → Bool
lookUpStable :: TP (Proof (Forall "a" [Binding] -> Forall "x" Integer -> Forall "b" [Binding] -> SBool))
lookUpStable =
  induct "lookUpStable"
         (\(Forall a) (Forall x) (Forall b) -> lookUp x (a ++ b) .== ite (isAssigned x a) (lookUp x a) (lookUp x b)) $
         \ih (binding, a) x b ->
           let vid = getBinding_1 binding
               val = getBinding_2 binding
           in [] |- lookUp x ((binding .: a) ++ b)
                 =: cases [ vid .== x ==> ite (isAssigned x (binding .: a)) (lookUp x (binding .: a)) (lookUp x b)
                                       =: val
                                       =: qed
                          , vid ./= x ==> lookUp x (a ++ b)
                                       ?? ih
                                       =: ite (isAssigned x a) (lookUp x a) (lookUp x b)
                                       =: qed
                          ]

-- | \(\text{lookUp}(x, a) \implies \text{isAssigned}(x, a)\)
--
-- >>> runTP trueIsAssigned
-- Inductive lemma: trueIsAssigned
--   Step: Base                            Q.E.D.
--   Step: 1 (2 way case split)
--     Step: 1.1                           Q.E.D.
--     Step: 1.2.1                         Q.E.D.
--     Step: 1.2.2                         Q.E.D.
--     Step: 1.Completeness                Q.E.D.
--   Result:                               Q.E.D.
-- [Proven] trueIsAssigned :: Ɐa ∷ [Binding] → Ɐx ∷ Integer → Bool
trueIsAssigned :: TP (Proof (Forall "a" [Binding] -> Forall "x" Integer -> SBool))
trueIsAssigned =
  induct "trueIsAssigned"
         (\(Forall a) (Forall x) -> lookUp x a .=> isAssigned x a) $
         \ih (binding, a) x ->
           let vid = [sCase|Binding binding of Binding v _ -> v|]
           in [lookUp x (binding .: a)]
           |- isAssigned x (binding .: a)
           =: cases [ vid .== x ==> trivial
                    , vid ./= x ==> isAssigned x a
                                 ?? ih
                                 =: sTrue
                                 =: qed
                    ]

-- | \(\text{value} = \text{lookUp}(x, bs) \implies \text{eval}(f, \{x \mapsto \text{value}\} :: bs) = \text{eval}(f, bs)\)
--
-- If we add a redundant binding (same id and value) to the front, evaluation doesn't change.
--
-- >>> runTPWith cvc5 evalStable
-- Lemma: ifComplexityPos                  Q.E.D.
-- Lemma: ifComplexitySmaller                Q.E.D.
-- Inductive lemma (strong): evalStable
--   Step: Measure is non-negative         Q.E.D.
--   Step: 1 (4 way case split)
--     Step: 1.1                           Q.E.D.
--     Step: 1.2                           Q.E.D.
--     Step: 1.3                           Q.E.D.
--     Step: 1.4.1                         Q.E.D.
--     Step: 1.4.2                         Q.E.D.
--     Step: 1.4.3                         Q.E.D.
--     Step: 1.4.4                         Q.E.D.
--     Step: 1.4.5                         Q.E.D.
--     Step: 1.4.6                         Q.E.D.
--     Step: 1.Completeness                Q.E.D.
--   Result:                               Q.E.D.
-- [Proven] evalStable :: Ɐf ∷ Formula → Ɐx ∷ Integer → Ɐv ∷ Bool → Ɐbs ∷ [Binding] → Bool
evalStable :: TP (Proof (Forall "f" Formula -> Forall "x" Integer -> Forall "v" Bool -> Forall "bs" [Binding] -> SBool))
evalStable = do
  icp <- recall "ifComplexityPos"     ifComplexityPos
  ibs <- recall "ifComplexitySmaller" ifComplexitySmaller

  sInduct "evalStable"
          (\(Forall f) (Forall x) (Forall v) (Forall bs) -> v .== lookUp x bs .=> eval f (sBinding x v .: bs) .== eval f bs)
          (\f _ _ _ -> ifComplexity f, [proofOf icp]) $
          \ih f x v bs ->
               let b = sBinding x v
               in [v .== lookUp x bs]
               |- cases [ isFTrue  f ==> trivial
                        , isFFalse f ==> trivial
                        , isVar    f ==> trivial
                        , isIf     f ==>
                            let c = getIf_1 f
                                l = getIf_2 f
                                r = getIf_3 f
                            in eval f (b .: bs)
                            =: eval (sIf c l r) (b .: bs)
                            =: ite (eval c (b .: bs)) (eval l (b .: bs)) (eval r (b .: bs))
                            ?? ih  `at` (Inst @"f" c, Inst @"x" x, Inst @"v" v, Inst @"bs" bs)
                            ?? ibs `at` (Inst @"c" c, Inst @"l" l, Inst @"r" r)
                            =: ite (eval c bs) (eval l (b .: bs)) (eval r (b .: bs))
                            ?? ih  `at` (Inst @"f" l, Inst @"x" x, Inst @"v" v, Inst @"bs" bs)
                            ?? ibs `at` (Inst @"c" c, Inst @"l" l, Inst @"r" r)
                            =: ite (eval c bs) (eval l bs) (eval r (b .: bs))
                            ?? ih  `at` (Inst @"f" r, Inst @"x" x, Inst @"v" v, Inst @"bs" bs)
                            ?? ibs `at` (Inst @"c" c, Inst @"l" l, Inst @"r" r)
                            =: ite (eval c bs) (eval l bs) (eval r bs)
                            =: eval (sIf c l r) bs
                            =: qed
                        ]

-- | Key soundness lemma: If a normalized formula is a tautology under bindings @b@,
-- then it evaluates to true under @b ++ a@ for any @a@.
--
-- >>> runTPWith (tpRibbon 50 cvc5) tautologyImpliesEval
-- Lemma: ifComplexityPos                            Q.E.D.
-- Lemma: ifBranchesSmaller                          Q.E.D.
-- Lemma: lookUpStable                               Q.E.D.
-- Lemma: trueIsAssigned                             Q.E.D.
-- Lemma: evalStable                                 Q.E.D.
-- Inductive lemma (strong): tautologyImpliesEval
--   Step: Measure is non-negative                   Q.E.D.
--   Step: 1 (4 way case split)
--     Step: 1.1                                     Q.E.D.
--     Step: 1.2                                     Q.E.D.
--     Step: 1.3.1                                   Q.E.D.
--     Step: 1.3.2                                   Q.E.D.
--     Step: 1.3.3                                   Q.E.D.
--     Step: 1.3.4                                   Q.E.D.
--     Step: 1.3.5                                   Q.E.D.
--     Step: 1.4 (4 way case split)
--       Step: 1.4.1.1                               Q.E.D.
--       Step: 1.4.1.2                               Q.E.D.
--       Step: 1.4.2.1                               Q.E.D.
--       Step: 1.4.2.2                               Q.E.D.
--       Step: 1.4.2.3                               Q.E.D.
--       Step: 1.4.3 (2 way case split)
--         Step: 1.4.3.1.1                           Q.E.D.
--         Step: 1.4.3.1.2                           Q.E.D.
--         Step: 1.4.3.1.3                           Q.E.D.
--         Step: 1.4.3.1.4                           Q.E.D.
--         Step: 1.4.3.2 (2 way case split)
--           Step: 1.4.3.2.1.1                       Q.E.D.
--           Step: 1.4.3.2.1.2                       Q.E.D.
--           Step: 1.4.3.2.1.3                       Q.E.D.
--           Step: 1.4.3.2.1.4                       Q.E.D.
--           Step: 1.4.3.2.1.5                       Q.E.D.
--           Step: 1.4.3.2.1.6                       Q.E.D.
--           Step: 1.4.3.2.1.7                       Q.E.D.
--           Step: 1.4.3.2.1.8                       Q.E.D.
--           Step: 1.4.3.2.2.1                       Q.E.D.
--           Step: 1.4.3.2.2.2                       Q.E.D.
--           Step: 1.4.3.2.2.3                       Q.E.D.
--           Step: 1.4.3.2.2.4                       Q.E.D.
--           Step: 1.4.3.2.2.5                       Q.E.D.
--           Step: 1.4.3.2.2.6                       Q.E.D.
--           Step: 1.4.3.2.2.7                       Q.E.D.
--           Step: 1.4.3.2.2.8                       Q.E.D.
--           Step: 1.4.3.2.Completeness              Q.E.D.
--         Step: 1.4.3.Completeness                  Q.E.D.
--       Step: 1.4.4                                 Q.E.D.
--       Step: 1.4.Completeness                      Q.E.D.
--     Step: 1.Completeness                          Q.E.D.
--   Result:                                         Q.E.D.
-- [Proven] tautologyImpliesEval :: Ɐf ∷ Formula → Ɐa ∷ [Binding] → Ɐb ∷ [Binding] → Bool
tautologyImpliesEval :: TP (Proof (Forall "f" Formula -> Forall "a" [Binding] -> Forall "b" [Binding] -> SBool))
tautologyImpliesEval = do

  icp <- recall "ifComplexityPos"     ifComplexityPos
  ibs <- recall "ifComplexitySmaller" ifComplexitySmaller
  lus <- recall "lookUpStable"        lookUpStable
  tia <- recall "trueIsAssigned"      trueIsAssigned
  evs <- recall "evalStable"          evalStable

  sInduct "tautologyImpliesEval"
          (\(Forall f) (Forall a) (Forall b) -> isNormal f .&& isTautology' f b .=> eval f (b ++ a))
          (\f _ _ -> ifComplexity f, [proofOf icp]) $
          \ih f a b ->
                [isNormal f, isTautology' f b]
             |- cases [ isFTrue  f ==> trivial
                      , isFFalse f ==> trivial
                      , isVar    f ==> let n = getVar_1 f
                                       in eval f (b ++ a)
                                       =: eval (sVar n) (b ++ a)
                                       =: lookUp n (b ++ a)
                                       ?? lus `at` (Inst @"a" b, Inst @"x" n, Inst @"b" a)
                                       =: ite (isAssigned n b) (lookUp n b) (lookUp n a)
                                       ?? tia `at` (Inst @"a" b, Inst @"x" n)
                                       =: lookUp n b
                                       =: sTrue
                                       =: qed
                      , isIf f     ==>
                          let c = getIf_1 f
                              l = getIf_2 f
                              r = getIf_3 f
                          in cases [ isFTrue  c ==> eval (sIf c l r) (b ++ a)
                                                 =: ite (eval c (b ++ a)) (eval l (b ++ a)) (eval r (b ++ a))
                                                 ?? ibs `at` (Inst @"c" c, Inst @"l" l, Inst @"r" r)
                                                 ?? ih  `at` (Inst @"f" l, Inst @"a" a, Inst @"b" b)
                                                 =: sTrue
                                                 =: qed
                                   , isFFalse c ==> eval (sIf c l r) (b ++ a)
                                                 =: ite (eval c (b ++ a)) (eval l (b ++ a)) (eval r (b ++ a))
                                                 =: eval r (b ++ a)
                                                 ?? ibs `at` (Inst @"c" c, Inst @"l" l, Inst @"r" r)
                                                 ?? ih  `at` (Inst @"f" r, Inst @"a" a, Inst @"b" b)
                                                 =: sTrue
                                                 =: qed
                                   , isVar    c ==> let n = getVar_1 c
                                                    in cases [ isAssigned n b ==>
                                                                    eval (sIf (sVar n) l r) (b ++ a)
                                                                 =: ite (eval (sVar n) (b ++ a)) (eval l (b ++ a)) (eval r (b ++ a))
                                                                 =: ite (lookUp n (b ++ a)) (eval l (b ++ a)) (eval r (b ++ a))
                                                                 ?? lus `at` (Inst @"a" b, Inst @"x" n, Inst @"b" a)
                                                                 =: ite (lookUp n b) (eval l (b ++ a)) (eval r (b ++ a))
                                                                 ?? ibs `at` (Inst @"c" c, Inst @"l" l, Inst @"r" r)
                                                                 ?? ih  `at` (Inst @"f" l, Inst @"a" a, Inst @"b" b)
                                                                 ?? ih  `at` (Inst @"f" r, Inst @"a" a, Inst @"b" b)
                                                                 =: sTrue
                                                                 =: qed
                                                             , sNot (isAssigned n b) ==>
                                                                 cases [ lookUp n a ==>
                                                                             eval (sIf (sVar n) l r) (b ++ a)
                                                                          =: ite (eval (sVar n) (b ++ a)) (eval l (b ++ a)) (eval r (b ++ a))
                                                                          =: ite (lookUp n (b ++ a)) (eval l (b ++ a)) (eval r (b ++ a))
                                                                          ?? lus `at` (Inst @"a" b, Inst @"x" n, Inst @"b" a)
                                                                          =: ite (lookUp n a) (eval l (b ++ a)) (eval r (b ++ a))
                                                                          =: eval l (b ++ a)
                                                                          ?? evs `at` (Inst @"f" l, Inst @"x" n, Inst @"v" (lookUp n a), Inst @"bs" (b ++ a))
                                                                          ?? lus `at` (Inst @"a" b, Inst @"x" n, Inst @"b" a)
                                                                          =: eval l (sBinding n (lookUp n a) .: (b ++ a))
                                                                          =: eval l (sBinding n sTrue .: (b ++ a))
                                                                          =: eval l ((assumeTrue n b) ++ a)
                                                                          ?? ibs `at` (Inst @"c" c, Inst @"l" l, Inst @"r" r)
                                                                          ?? ih  `at` (Inst @"f" l, Inst @"a" a, Inst @"b" (assumeTrue n b))
                                                                          =: sTrue
                                                                          =: qed
                                                                       , sNot (lookUp n a) ==>
                                                                             eval (sIf (sVar n) l r) (b ++ a)
                                                                          =: ite (eval (sVar n) (b ++ a)) (eval l (b ++ a)) (eval r (b ++ a))
                                                                          =: ite (lookUp n (b ++ a)) (eval l (b ++ a)) (eval r (b ++ a))
                                                                          ?? lus `at` (Inst @"a" b, Inst @"x" n, Inst @"b" a)
                                                                          =: ite (lookUp n a) (eval l (b ++ a)) (eval r (b ++ a))
                                                                          =: eval r (b ++ a)
                                                                          ?? evs `at` (Inst @"f" r, Inst @"x" n, Inst @"v" (lookUp n a), Inst @"bs" (b ++ a))
                                                                          ?? lus `at` (Inst @"a" b, Inst @"x" n, Inst @"b" a)
                                                                          =: eval r (sBinding n (lookUp n a) .: (b ++ a))
                                                                          =: eval r (sBinding n sFalse .: (b ++ a))
                                                                          =: eval r ((assumeFalse n b) ++ a)
                                                                          ?? ibs `at` (Inst @"c" c, Inst @"l" l, Inst @"r" r)
                                                                          ?? ih  `at` (Inst @"f" r, Inst @"a" a, Inst @"b" (assumeFalse n b))
                                                                          =: sTrue
                                                                          =: qed
                                                                       ]
                                                             ]
                                   , isIf c     ==> trivial  -- Contradicts isNormal
                                   ]
                      ]

-- * Normalization correctness

-- | \(\text{isNormal}(\text{normalize}(f))\)
--
-- Normalization produces normalized formulas.
--
-- >>> runTPWith (tpRibbon 50 z3) normalizeCorrect
-- runTPWith (tpRibbon 50 z3) normalizeCorrect
-- Lemma: ifComplexityPos                            Q.E.D.
-- Lemma: ifComplexitySmaller                        Q.E.D.
-- Lemma: normalizePreservesComplexity               Q.E.D.
-- Lemma: ifDepthNonNeg                              Q.E.D.
-- Lemma: ifDepthSmaller                             Q.E.D.
-- Inductive lemma (strong): normalizeCorrect
--   Step: Measure is non-negative                   Q.E.D.
--   Step: 1 (4 way case split)
--     Step: 1.1                                     Q.E.D.
--     Step: 1.2                                     Q.E.D.
--     Step: 1.3                                     Q.E.D.
--     Step: 1.4 (2 way case split)
--       Step: 1.4.1.1                               Q.E.D.
--       Step: 1.4.1.2                               Q.E.D.
--       Step: 1.4.2.1                               Q.E.D.
--       Step: 1.4.2.2                               Q.E.D.
--       Step: 1.4.2.3                               Q.E.D.
--       Step: 1.4.2.4                               Q.E.D.
--       Step: 1.4.2.5                               Q.E.D.
--       Step: 1.4.Completeness                      Q.E.D.
--     Step: 1.Completeness                          Q.E.D.
--   Result:                                         Q.E.D.
-- [Proven] normalizeCorrect :: Ɐf ∷ Formula → Bool
normalizeCorrect :: TP (Proof (Forall "f" Formula -> SBool))
normalizeCorrect = do
  icp <- recall "ifComplexityPos"              ifComplexityPos
  ibs <- recall "ifComplexitySmaller"          ifComplexitySmaller
  npc <- recall "normalizePreservesComplexity" normalizePreservesComplexity
  idn <- recall "ifDepthNonNeg"                ifDepthNonNeg
  ids <- recall "ifDepthSmaller"               ifDepthSmaller

  sInductWith cvc5 "normalizeCorrect"
              (\(Forall f) -> isNormal (normalize f))
              (\f -> tuple (ifComplexity f, ifDepth f), [proofOf icp, proofOf idn]) $
              \ih f -> []
                    |- isNormal (normalize f)
                    =: cases [ isFTrue  f ==> trivial
                             , isFFalse f ==> trivial
                             , isVar    f ==> trivial
                             , isIf     f ==> let c = getIf_1 f
                                                  l = getIf_2 f
                                                  r = getIf_3 f
                                              in cases [ isIf c ==>
                                                           let p  = getIf_1 c
                                                               q  = getIf_2 c
                                                               rc = getIf_3 c
                                                               transformed = sIf p (sIf q l r) (sIf rc l r)
                                                           in isNormal (normalize transformed)
                                                           ?? npc `at` (Inst @"p" p, Inst @"q" q, Inst @"s" rc, Inst @"l" l, Inst @"r" r)
                                                           ?? ids `at` (Inst @"c" p, Inst @"l" (sIf q l r), Inst @"r" (sIf rc l r))
                                                           ?? ids `at` (Inst @"c" c, Inst @"l" l, Inst @"r" r)
                                                           ?? ids `at` (Inst @"c" p, Inst @"l" q, Inst @"r" rc)
                                                           ?? ih `at` Inst @"f" transformed
                                                           =: sTrue
                                                           =: qed
                                                       , sNot (isIf c) ==>
                                                              isNormal (sIf c (normalize l) (normalize r))
                                                           =: sNot (isIf c) .&& isNormal (normalize l) .&& isNormal (normalize r)
                                                           =: isNormal (normalize l) .&& isNormal (normalize r)
                                                           ?? ibs `at` (Inst @"c" c, Inst @"l" l, Inst @"r" r)
                                                           ?? ih  `at` Inst @"f" l
                                                           =: isNormal (normalize r)
                                                           ?? ibs `at` (Inst @"c" c, Inst @"l" l, Inst @"r" r)
                                                           ?? ih  `at` Inst @"f" r
                                                           =: sTrue
                                                           =: qed
                                                       ]
                             ]

-- | \(\text{isNormal}(f) \implies \text{normalize}(f) = f\)
--
-- Normalizing a normalized formula is the identity.
--
-- >>> runTPWith (tpRibbon 50 z3) normalizeSame
-- Lemma: ifComplexityPos                            Q.E.D.
-- Lemma: ifComplexitySmaller                        Q.E.D.
-- Inductive lemma (strong): normalizeSame
--   Step: Measure is non-negative                   Q.E.D.
--   Step: 1 (4 way case split)
--     Step: 1.1                                     Q.E.D.
--     Step: 1.2                                     Q.E.D.
--     Step: 1.3                                     Q.E.D.
--     Step: 1.4.1                                   Q.E.D.
--     Step: 1.4.2                                   Q.E.D.
--     Step: 1.Completeness                          Q.E.D.
--   Result:                                         Q.E.D.
-- [Proven] normalizeSame :: Ɐf ∷ Formula → Bool
normalizeSame :: TP (Proof (Forall "f" Formula -> SBool))
normalizeSame = do
  icp <- recall "ifComplexityPos"     ifComplexityPos
  ibs <- recall "ifComplexitySmaller" ifComplexitySmaller

  sInduct "normalizeSame"
          (\(Forall f) -> isNormal f .=> normalize f .== f)
          (\f -> ifComplexity f, [proofOf icp]) $
          \ih f -> [isNormal f]
                |- cases [ isFTrue  f ==> trivial
                         , isFFalse f ==> trivial
                         , isVar    f ==> trivial
                         , isIf     f ==> let c = getIf_1 f
                                              l = getIf_2 f
                                              r = getIf_3 f
                                          in sIf c (normalize l) (normalize r)
                                          ?? ibs `at` (Inst @"c" c, Inst @"l" l, Inst @"r" r)
                                          ?? ih `at` Inst @"f" l
                                          =: sIf c l (normalize r)
                                          ?? ibs `at` (Inst @"c" c, Inst @"l" l, Inst @"r" r)
                                          ?? ih `at` Inst @"f" r
                                          =: sIf c l r
                                          =: qed
                         ]

-- | \(\text{eval}(\text{normalize}(f), bs) = \text{eval}(f, bs)\)
--
-- Normalization preserves semantics.
--
-- >>> runTPWith (tpRibbon 50 cvc5) normalizeRespectsTruth
-- Inductive lemma (strong): normalizeRespectsTruth
--   Step: Measure is non-negative         Q.E.D.
--   Step: 1 (4 way full case split)
--     Step: 1.1                           Q.E.D.
--     Step: 1.2                           Q.E.D.
--     Step: 1.3                           Q.E.D.
--     Step: 1.4.1                         Q.E.D.
--     Step: 1.4.2                         Q.E.D.
--     Step: 1.4.3                         Q.E.D.
--   Result:                               Q.E.D.
-- [Proven] normalizeRespectsTruth :: Ɐf ∷ Formula → Ɐbs ∷ [Binding] → Bool
normalizeRespectsTruth :: TP (Proof (Forall "f" Formula -> Forall "bs" [Binding] -> SBool))
normalizeRespectsTruth =
  sInductWith cvc5 "normalizeRespectsTruth"
              (\(Forall f) (Forall bs) -> eval (normalize f) bs .== eval f bs)
              (\f _ -> tuple (ifComplexity f, ifDepth f), []) $
              \ih f bs -> []
                       |- cases [ isFTrue  f ==> trivial
                                , isFFalse f ==> trivial
                                , isVar    f ==> trivial
                                , isIf     f ==> let c = getIf_1 f
                                                     l = getIf_2 f
                                                     r = getIf_3 f
                                                 in eval (normalize (sIf c l r)) bs .== eval (sIf c l r) bs
                                                 ?? ih `at` (Inst @"f" c, Inst @"bs" bs)
                                                 ?? ih `at` (Inst @"f" l, Inst @"bs" bs)
                                                 ?? ih `at` (Inst @"f" r, Inst @"bs" bs)
                                                 =: sTrue
                                                 =: qed
                                ]

-- * Main soundness theorem

-- | \(\text{isTautology}(f) \implies \text{eval}(f, \text{bindings})\)
--
-- If the tautology checker says a formula is a tautology, then it evaluates
-- to true under any binding environment. This is the soundness theorem.
--
-- >>> runTP tautologyTheorem
-- Lemma: tautologyImpliesEval             Q.E.D.
-- Lemma: tautologyTheorem
--   Step: 1                               Q.E.D.
--   Step: 2                               Q.E.D.
--   Result:                               Q.E.D.
-- [Proven] tautologyTheorem :: Ɐf ∷ Formula → Ɐbindings ∷ [Binding] → Bool
tautologyTheorem :: TP (Proof (Forall "f" Formula -> Forall "bindings" [Binding] -> SBool))
tautologyTheorem = do
  tie <- recall "tautologyImpliesEval" tautologyImpliesEval

  calc "tautologyTheorem"
       (\(Forall f) (Forall bindings) -> isTautology f .=> eval f bindings) $
       \f bindings -> [isTautology f]
                   |- eval f bindings
                   =: eval (normalize f) bindings
                   ?? tie `at` (Inst @"f" (normalize f), Inst @"a" bindings, Inst @"b" [])
                   =: sTrue
                   =: qed

{- HLint ignore module "Use camelCase" -}
