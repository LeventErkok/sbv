-----------------------------------------------------------------------------
-- |
-- Module    : Documentation.SBV.Examples.TP.ConstFold
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Correctness of constant folding for a simple expression language.
-----------------------------------------------------------------------------

{-# LANGUAGE CPP                 #-}
{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE QuasiQuotes         #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeAbstractions    #-}
{-# LANGUAGE TypeApplications    #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module Documentation.SBV.Examples.TP.ConstFold where

import Prelude hiding ((++), snd)

import Data.SBV
import Data.SBV.List  as SL
import Data.SBV.Tuple as ST
import Data.SBV.TP

-- Get the expression language definitions
import Documentation.SBV.Examples.TP.VM

#ifdef DOCTEST
-- $setup
-- >>> import Data.SBV
-- >>> import Data.SBV.TP
-- >>> :set -XTypeApplications
#endif

-- | Base expression type (used in quantifiers).
type Exp = Expr String Integer

-- | Base environment-list type (used in quantifiers).
type EL = [(String, Integer)]

-- | Symbolic expression over strings and integers.
type SE = SExpr String Integer

-- | Symbolic environment over strings and integers.
type E = Env String Integer

-- * Simplification

-- | Simplify an expression at the top level, assuming sub-expressions are already folded.
-- The rules are:
--
--   * @Sqr (Con v)         → Con (v*v)@
--   * @Inc (Con v)         → Con (v+1)@
--   * @Add (Con 0) x       → x@
--   * @Add x (Con 0)       → x@
--   * @Add (Con a) (Con b) → Con (a+b)@
--   * @Mul (Con 0) x       → Con 0@
--   * @Mul x (Con 0)       → Con 0@
--   * @Mul (Con 1) x       → x@
--   * @Mul x (Con 1)       → x@
--   * @Mul (Con a) (Con b) → Con (a*b)@
--   * @Let nm (Con v) b    → subst nm v b@
simplify :: SE -> SE
simplify = smtFunction "simplify" $ \expr ->
  [sCase|Expr expr of
    Sqr (Con v)         -> sCon (v * v)

    Inc (Con v)         -> sCon (v + 1)

    Add (Con 0) r       -> r
    Add l       (Con 0) -> l
    Add (Con a) (Con b) -> sCon (a + b)

    Mul (Con 0) _       -> sCon 0
    Mul _       (Con 0) -> sCon 0
    Mul (Con 1) r       -> r
    Mul l       (Con 1) -> l
    Mul (Con a) (Con b) -> sCon (a * b)

    Let nm (Con v) b    -> subst nm v b

    -- fall-thru
    _                   -> expr
  |]

-- * Substitution

-- | Substitute a variable with a value in an expression. Capture-avoiding:
-- if a @Let@-bound variable shadows the target, we do not substitute in the body.
--
--   * @Var x         → if x == nm then Con v else Var x@
--   * @Con c         → Con c@
--   * @Sqr a         → Sqr (subst nm v a)@
--   * @Inc a         → Inc (subst nm v a)@
--   * @Add a b       → Add (subst nm v a) (subst nm v b)@
--   * @Mul a b       → Mul (subst nm v a) (subst nm v b)@
--   * @Let x a b     → Let x (subst nm v a) (if x == nm then b else subst nm v b)@
subst :: SString -> SInteger -> SE -> SE
subst = smtFunction "subst" $ \nm v expr ->
  [sCase|Expr expr of

    -- Substitute for vars if name matches
    Var x | x .== nm -> sCon v
          | True     -> sVar x

    -- pass thru
    Con c   -> sCon c
    Sqr a   -> sSqr (subst nm v a)
    Inc a   -> sInc (subst nm v a)
    Add a b -> sAdd (subst nm v a) (subst nm v b)
    Mul a b -> sMul (subst nm v a) (subst nm v b)

    -- substitute in the definition, but only substitute in the body if the name is not shadowing
    Let x a b | x .== nm -> sLet x (subst nm v a) b
              | True     -> sLet x (subst nm v a) (subst nm v b)
  |]

-- * Constant folding

-- | Constant fold an expression bottom-up: first fold sub-expressions, then simplify.
cfold :: SE -> SE
cfold = smtFunction "cfold" $ \expr ->
  [sCase|Expr expr of
    Var nm     -> sVar nm
    Con v      -> sCon v
    Sqr a      -> simplify (sSqr (cfold a))
    Inc a      -> simplify (sInc (cfold a))
    Add a b    -> simplify (sAdd (cfold a) (cfold b))
    Mul a b    -> simplify (sMul (cfold a) (cfold b))
    Let nm a b -> simplify (sLet nm (cfold a) (cfold b))
  |]

-- * Correctness

-- | The size measure is always non-negative.
--
-- >>> runTP measureNonNeg
-- Lemma: measureNonNeg                    Q.E.D.
-- [Proven] measureNonNeg :: Ɐe ∷ (Expr [Char] Integer) → Bool
measureNonNeg :: TP (Proof (Forall "e" Exp -> SBool))
measureNonNeg = inductiveLemma "measureNonNeg"
                               (\(Forall @"e" (e :: SE)) -> size e .>= 0)
                               []

-- | Congruence for squaring: if @a == b@ then @a*a == b*b@.
--
-- >>> runTP sqrCong
-- Lemma: sqrCong                          Q.E.D.
-- [Proven] sqrCong :: Ɐa ∷ Integer → Ɐb ∷ Integer → Bool
sqrCong :: TP (Proof (Forall "a" Integer -> Forall "b" Integer -> SBool))
sqrCong = lemma "sqrCong"
                (\(Forall @"a" (a :: SInteger)) (Forall @"b" b) ->
                      a .== b .=> a * a .== b * b) []

-- | Congruence for multiplication on the left: if @a == b@ then @a*c == b*c@.
--
-- >>> runTP mulCongL
-- Lemma: mulCongL                         Q.E.D.
-- [Proven] mulCongL :: Ɐa ∷ Integer → Ɐb ∷ Integer → Ɐc ∷ Integer → Bool
mulCongL :: TP (Proof (Forall "a" Integer -> Forall "b" Integer -> Forall "c" Integer -> SBool))
mulCongL = lemma "mulCongL"
                 (\(Forall @"a" (a :: SInteger)) (Forall @"b" b) (Forall @"c" c) ->
                       a .== b .=> a * c .== b * c) []

-- | Congruence for multiplication on the right: if @b == c@ then @a*b == a*c@.
--
-- >>> runTP mulCongR
-- Lemma: mulCongR                         Q.E.D.
-- [Proven] mulCongR :: Ɐa ∷ Integer → Ɐb ∷ Integer → Ɐc ∷ Integer → Bool
mulCongR :: TP (Proof (Forall "a" Integer -> Forall "b" Integer -> Forall "c" Integer -> SBool))
mulCongR = lemma "mulCongR"
                 (\(Forall @"a" (a :: SInteger)) (Forall @"b" b) (Forall @"c" c) ->
                       b .== c .=> a * b .== a * c) []

-- | Unfolding @interpInEnv@ over @Sqr@.
--
-- >>> runTP sqrHelper
-- Lemma: sqrHelper                        Q.E.D.
-- [Proven] sqrHelper :: Ɐenv ∷ [([Char], Integer)] → Ɐa ∷ (Expr [Char] Integer) → Bool
sqrHelper :: TP (Proof (Forall "env" EL -> Forall "a" Exp -> SBool))
sqrHelper = lemma "sqrHelper"
                  (\(Forall @"env" (env :: E)) (Forall @"a" a) ->
                        interpInEnv env (sSqr a) .== interpInEnv env a * interpInEnv env a) []

-- | Unfolding @interpInEnv@ over @Add@.
--
-- >>> runTP addHelper
-- Lemma: addHelper                        Q.E.D.
-- [Proven] addHelper :: Ɐenv ∷ [([Char], Integer)] → Ɐa ∷ (Expr [Char] Integer) → Ɐb ∷ (Expr [Char] Integer) → Bool
addHelper :: TP (Proof (Forall "env" EL -> Forall "a" Exp -> Forall "b" Exp -> SBool))
addHelper = lemma "addHelper"
                  (\(Forall @"env" (env :: E)) (Forall @"a" a) (Forall @"b" b) ->
                        interpInEnv env (sAdd a b) .== interpInEnv env a + interpInEnv env b) []

-- | Unfolding @interpInEnv@ over @Mul@.
--
-- >>> runTP mulHelper
-- Lemma: mulHelper                        Q.E.D.
-- [Proven] mulHelper :: Ɐenv ∷ [([Char], Integer)] → Ɐa ∷ (Expr [Char] Integer) → Ɐb ∷ (Expr [Char] Integer) → Bool
mulHelper :: TP (Proof (Forall "env" EL -> Forall "a" Exp -> Forall "b" Exp -> SBool))
mulHelper = lemma "mulHelper"
                  (\(Forall @"env" (env :: E)) (Forall @"a" a) (Forall @"b" b) ->
                        interpInEnv env (sMul a b) .== interpInEnv env a * interpInEnv env b) []

-- | Unfolding @interpInEnv@ over @Let@.
--
-- >>> runTP letHelper
-- Lemma: letHelper                        Q.E.D.
-- [Proven] letHelper :: Ɐenv ∷ [([Char], Integer)] → Ɐnm ∷ [Char] → Ɐa ∷ (Expr [Char] Integer) → Ɐb ∷ (Expr [Char] Integer) → Bool
letHelper :: TP (Proof (Forall "env" EL -> Forall "nm" String -> Forall "a" Exp -> Forall "b" Exp -> SBool))
letHelper = lemma "letHelper"
                  (\(Forall @"env" (env :: E)) (Forall @"nm" nm) (Forall @"a" a) (Forall @"b" b) ->
                        interpInEnv env (sLet nm a b) .== interpInEnv (ST.tuple (nm, interpInEnv env a) .: env) b) []

-- * Environment lemmas

-- | Swapping two adjacent bindings with distinct keys does not affect lookup.
--
-- >>> runTP lookupSwap
-- Lemma: lookupSwap                       Q.E.D.
-- [Proven] lookupSwap :: Ɐk ∷ [Char] → Ɐb1 ∷ ([Char], Integer) → Ɐb2 ∷ ([Char], Integer) → Ɐenv ∷ [([Char], Integer)] → Bool
lookupSwap :: TP (Proof (Forall "k" String -> Forall "b1" (String, Integer)
                      -> Forall "b2" (String, Integer) -> Forall "env" EL -> SBool))
lookupSwap = lemma "lookupSwap"
                   (\(Forall @"k" (k :: SString)) (Forall @"b1" (b1 :: STuple String Integer))
                     (Forall @"b2" (b2 :: STuple String Integer)) (Forall @"env" (env :: E)) ->
                       let (x, _) = ST.untuple b1
                           (y, _) = ST.untuple b2
                       in  x ./= y .=>    SL.lookup k (b1 .: b2 .: env)
                                       .== SL.lookup k (b2 .: b1 .: env))
                   []

-- | Generalized swap: swapping two adjacent distinct-keyed bindings behind
-- a prefix does not affect lookup.
--
-- >>> runTPWith cvc5 lookupSwapPfx
-- Lemma: lookupSwap                       Q.E.D.
-- Inductive lemma (strong): lookupSwapPfx
--   Step: Measure is non-negative         Q.E.D.
--   Step: 1 (2 way case split)
--     Step: 1.1 (base)                    Q.E.D.
--     Step: 1.2 (cons)                    Q.E.D.
--     Step: 1.Completeness                Q.E.D.
--   Result:                               Q.E.D.
-- [Proven] lookupSwapPfx :: Ɐpfx ∷ [([Char], Integer)] → Ɐk ∷ [Char] → Ɐb1 ∷ ([Char], Integer) → Ɐb2 ∷ ([Char], Integer) → Ɐenv ∷ [([Char], Integer)] → Bool
lookupSwapPfx :: TP (Proof (Forall "pfx" EL -> Forall "k" String -> Forall "b1" (String, Integer)
                         -> Forall "b2" (String, Integer) -> Forall "env" EL -> SBool))
lookupSwapPfx = do
   lkS <- recall "lookupSwap" lookupSwap
   sInduct "lookupSwapPfx"
     (\(Forall @"pfx" (pfx :: E)) (Forall @"k" (k :: SString)) (Forall @"b1" (b1 :: STuple String Integer))
       (Forall @"b2" (b2 :: STuple String Integer)) (Forall @"env" (env :: E)) ->
         let (x, _) = ST.untuple b1
             (y, _) = ST.untuple b2
         in  x ./= y .=>    SL.lookup k (pfx ++ b1 .: b2 .: env)
                         .== SL.lookup k (pfx ++ b2 .: b1 .: env))
     (\pfx _ _ _ _ -> SL.length pfx :: SInteger, []) $
     \ih pfx k b1 b2 env ->
       let (x, _) = ST.untuple b1
           (y, _) = ST.untuple b2
       in [x ./= y]
       |- cases [ SL.null pfx
                  ==> SL.lookup k (pfx ++ b1 .: b2 .: env)
                   ?? "base"
                   ?? lkS `at` (Inst @"k" k, Inst @"b1" b1, Inst @"b2" b2, Inst @"env" env)
                   =: SL.lookup k (pfx ++ b2 .: b1 .: env)
                   =: qed
                , sNot (SL.null pfx)
                  ==> let t  = SL.tail pfx
                       in SL.lookup k (pfx ++ b1 .: b2 .: env)
                       ?? "cons"
                       ?? ih `at` (Inst @"pfx" t, Inst @"k" k, Inst @"b1" b1, Inst @"b2" b2, Inst @"env" env)
                       =: SL.lookup k (pfx ++ b2 .: b1 .: env)
                       =: qed
                ]

-- | A shadowed binding does not affect lookup: if the same key appears first, the second is irrelevant.
--
-- >>> runTP lookupShadow
-- Lemma: lookupShadow                     Q.E.D.
-- [Proven] lookupShadow :: Ɐk ∷ [Char] → Ɐb1 ∷ ([Char], Integer) → Ɐb2 ∷ ([Char], Integer) → Ɐenv ∷ [([Char], Integer)] → Bool
lookupShadow :: TP (Proof (Forall "k" String -> Forall "b1" (String, Integer)
                        -> Forall "b2" (String, Integer) -> Forall "env" EL -> SBool))
lookupShadow = lemma "lookupShadow"
                     (\(Forall @"k" (k :: SString)) (Forall @"b1" (b1 :: STuple String Integer))
                       (Forall @"b2" (b2 :: STuple String Integer)) (Forall @"env" (env :: E)) ->
                         let (x, _) = ST.untuple b1
                             (y, _) = ST.untuple b2
                         in  x .== y .=>    SL.lookup k (b1 .: b2 .: env)
                                        .== SL.lookup k (b1 .: env))
                     []

-- | Generalized shadow: a shadowed binding behind a prefix does not affect lookup.
--
-- >>> runTPWith cvc5 lookupShadowPfx
-- Lemma: lookupShadow                     Q.E.D.
-- Inductive lemma (strong): lookupShadowPfx
--   Step: Measure is non-negative         Q.E.D.
--   Step: 1 (2 way case split)
--     Step: 1.1 (base)                    Q.E.D.
--     Step: 1.2 (cons)                    Q.E.D.
--     Step: 1.Completeness                Q.E.D.
--   Result:                               Q.E.D.
-- [Proven] lookupShadowPfx :: Ɐpfx ∷ [([Char], Integer)] → Ɐk ∷ [Char] → Ɐb1 ∷ ([Char], Integer) → Ɐb2 ∷ ([Char], Integer) → Ɐenv ∷ [([Char], Integer)] → Bool
lookupShadowPfx :: TP (Proof (Forall "pfx" EL -> Forall "k" String -> Forall "b1" (String, Integer)
                           -> Forall "b2" (String, Integer) -> Forall "env" EL -> SBool))
lookupShadowPfx = do
   lkSh <- recall "lookupShadow" lookupShadow
   sInduct "lookupShadowPfx"
     (\(Forall @"pfx" (pfx :: E)) (Forall @"k" (k :: SString)) (Forall @"b1" (b1 :: STuple String Integer))
       (Forall @"b2" (b2 :: STuple String Integer)) (Forall @"env" (env :: E)) ->
         let (x, _) = ST.untuple b1
             (y, _) = ST.untuple b2
         in  x .== y .=>    SL.lookup k (pfx ++ b1 .: b2 .: env)
                         .== SL.lookup k (pfx ++ b1 .: env))
     (\pfx _ _ _ _ -> SL.length pfx :: SInteger, []) $
     \ih pfx k b1 b2 env ->
       let (x, _) = ST.untuple b1
           (y, _) = ST.untuple b2
       in [x .== y]
       |- cases [ SL.null pfx
                  ==> SL.lookup k (pfx ++ b1 .: b2 .: env)
                   ?? "base"
                   ?? lkSh `at` (Inst @"k" k, Inst @"b1" b1, Inst @"b2" b2, Inst @"env" env)
                   =: SL.lookup k (pfx ++ b1 .: env)
                   =: qed
                , sNot (SL.null pfx)
                  ==> let h  = SL.head pfx
                          t  = SL.tail pfx
                       in SL.lookup k (pfx ++ b1 .: b2 .: env)
                       ?? "cons"
                       ?? pfx .== h .: t
                       ?? ih `at` (Inst @"pfx" t, Inst @"k" k, Inst @"b1" b1, Inst @"b2" b2, Inst @"env" env)
                       =: SL.lookup k (pfx ++ b1 .: env)
                       =: qed
                ]

-- | Swapping two adjacent distinct-keyed bindings in the environment
-- does not affect interpretation. The @pfx@ parameter allows the swap
-- to happen at any depth in the environment.
--
-- >>> runTPWith cvc5 envSwap
-- Lemma: measureNonNeg                    Q.E.D.
-- Lemma: lookupSwapPfx                    Q.E.D.
-- Lemma: sqrCong                          Q.E.D.
-- Lemma: sqrHelper                        Q.E.D.
-- Lemma: addHelper                        Q.E.D.
-- Lemma: mulCongL                         Q.E.D.
-- Lemma: mulCongR                         Q.E.D.
-- Lemma: mulHelper                        Q.E.D.
-- Lemma: letHelper                        Q.E.D.
-- Inductive lemma (strong): envSwap
--   Step: Measure is non-negative         Q.E.D.
--   Step: 1 (7 way case split)
--     Step: 1.1 (Var)                     Q.E.D.
--     Step: 1.2 (Con)                     Q.E.D.
--     Step: 1.3.1 (Sqr)                   Q.E.D.
--     Step: 1.3.2                         Q.E.D.
--     Step: 1.3.3                         Q.E.D.
--     Step: 1.4 (Inc)                     Q.E.D.
--     Step: 1.5.1 (Add)                   Q.E.D.
--     Step: 1.5.2                         Q.E.D.
--     Step: 1.5.3                         Q.E.D.
--     Step: 1.6.1 (Mul)                   Q.E.D.
--     Step: 1.6.2                         Q.E.D.
--     Step: 1.6.3                         Q.E.D.
--     Step: 1.6.4                         Q.E.D.
--     Step: 1.7.1 (Let)                   Q.E.D.
--     Step: 1.7.2                         Q.E.D.
--     Step: 1.7.3                         Q.E.D.
--     Step: 1.7.4                         Q.E.D.
--     Step: 1.Completeness                Q.E.D.
--   Result:                               Q.E.D.
-- [Proven] envSwap :: Ɐe ∷ (Expr [Char] Integer) → Ɐpfx ∷ [([Char], Integer)] → Ɐenv ∷ [([Char], Integer)] → Ɐb1 ∷ ([Char], Integer) → Ɐb2 ∷ ([Char], Integer) → Bool
envSwap :: TP (Proof (Forall "e" Exp -> Forall "pfx" EL -> Forall "env" EL
                   -> Forall "b1" (String, Integer) -> Forall "b2" (String, Integer) -> SBool))
envSwap = do
   mnn  <- recall "measureNonNeg" measureNonNeg
   lkSP <- recall "lookupSwapPfx" lookupSwapPfx
   sqrC <- recall "sqrCong"      sqrCong
   sqrH <- recall "sqrHelper"    sqrHelper
   addH <- recall "addHelper"    addHelper
   mulCL <- recall "mulCongL"    mulCongL
   mulCR <- recall "mulCongR"    mulCongR
   mulH <- recall "mulHelper"    mulHelper
   letH <- recall "letHelper"    letHelper

   sInduct "envSwap"
     (\(Forall @"e" (e :: SE)) (Forall @"pfx" (pfx :: E)) (Forall @"env" (env :: E))
       (Forall @"b1" (b1 :: STuple String Integer)) (Forall @"b2" (b2 :: STuple String Integer)) ->
       let (x, _)  = ST.untuple b1
           (y, _)  = ST.untuple b2
       in x ./= y .=> interpInEnv (pfx ++ b1 .: b2 .: env) e .== interpInEnv (pfx ++ b2 .: b1 .: env) e)
     (\e _ _ _ _ -> size e :: SInteger, [proofOf mnn]) $
     \ih e pfx env b1 b2 ->
       let (x, _) = ST.untuple b1
           (y, _) = ST.untuple b2
           env1 = pfx ++ b1 .: b2 .: env
           env2 = pfx ++ b2 .: b1 .: env
       in [x ./= y]
       |- cases [ isVar e
                  ==> let nm = svar e
                    in interpInEnv env1 (sVar nm)
                    ?? "Var"
                    ?? lkSP `at` (Inst @"pfx" pfx, Inst @"k" nm, Inst @"b1" b1, Inst @"b2" b2, Inst @"env" env)
                    =: interpInEnv env2 (sVar nm)
                    =: qed

                , isCon e
                  ==> let v = scon e
                    in interpInEnv env1 (sCon v)
                    ?? "Con"
                    =: interpInEnv env2 (sCon v)
                    =: qed

                , isSqr e
                  ==> let a = ssqrVal e
                    in interpInEnv env1 (sSqr a)
                    ?? "Sqr"
                    ?? sqrH `at` (Inst @"env" env1, Inst @"a" a)
                    =: interpInEnv env1 a * interpInEnv env1 a
                    ?? ih `at` (Inst @"e" a, Inst @"pfx" pfx, Inst @"env" env, Inst @"b1" b1, Inst @"b2" b2)
                    ?? sqrC `at` (Inst @"a" (interpInEnv env1 a), Inst @"b" (interpInEnv env2 a))
                    =: interpInEnv env2 a * interpInEnv env2 a
                    ?? sqrH `at` (Inst @"env" env2, Inst @"a" a)
                    =: interpInEnv env2 (sSqr a)
                    =: qed

                , isInc e
                  ==> let a = sincVal e
                    in interpInEnv env1 (sInc a)
                    ?? "Inc"
                    ?? ih `at` (Inst @"e" a, Inst @"pfx" pfx, Inst @"env" env, Inst @"b1" b1, Inst @"b2" b2)
                    =: interpInEnv env2 (sInc a)
                    =: qed

                , isAdd e
                  ==> let a = sadd1 e
                          b = sadd2 e
                    in interpInEnv env1 (sAdd a b)
                    ?? "Add"
                    ?? addH `at` (Inst @"env" env1, Inst @"a" a, Inst @"b" b)
                    =: interpInEnv env1 a + interpInEnv env1 b
                    ?? ih `at` (Inst @"e" a, Inst @"pfx" pfx, Inst @"env" env, Inst @"b1" b1, Inst @"b2" b2)
                    ?? ih `at` (Inst @"e" b, Inst @"pfx" pfx, Inst @"env" env, Inst @"b1" b1, Inst @"b2" b2)
                    =: interpInEnv env2 a + interpInEnv env2 b
                    ?? addH `at` (Inst @"env" env2, Inst @"a" a, Inst @"b" b)
                    =: interpInEnv env2 (sAdd a b)
                    =: qed

                , isMul e
                  ==> let a = smul1 e
                          b = smul2 e
                    in interpInEnv env1 (sMul a b)
                    ?? "Mul"
                    ?? mulH `at` (Inst @"env" env1, Inst @"a" a, Inst @"b" b)
                    =: interpInEnv env1 a * interpInEnv env1 b
                    ?? ih `at` (Inst @"e" a, Inst @"pfx" pfx, Inst @"env" env, Inst @"b1" b1, Inst @"b2" b2)
                    ?? mulCL `at` (Inst @"a" (interpInEnv env1 a), Inst @"b" (interpInEnv env2 a), Inst @"c" (interpInEnv env1 b))
                    =: interpInEnv env2 a * interpInEnv env1 b
                    ?? ih `at` (Inst @"e" b, Inst @"pfx" pfx, Inst @"env" env, Inst @"b1" b1, Inst @"b2" b2)
                    ?? mulCR `at` (Inst @"a" (interpInEnv env2 a), Inst @"b" (interpInEnv env1 b), Inst @"c" (interpInEnv env2 b))
                    =: interpInEnv env2 a * interpInEnv env2 b
                    ?? mulH `at` (Inst @"env" env2, Inst @"a" a, Inst @"b" b)
                    =: interpInEnv env2 (sMul a b)
                    =: qed

                , isLet e
                  ==> let nm = slvar  e
                          a  = slval  e
                          b  = slbody e
                          val1 = interpInEnv env1 a
                          val2 = interpInEnv env2 a
                    in interpInEnv env1 (sLet nm a b)
                    ?? "Let"
                    ?? letH `at` (Inst @"env" env1, Inst @"nm" nm, Inst @"a" a, Inst @"b" b)
                    =: interpInEnv (ST.tuple (nm, val1) .: env1) b
                    ?? ih `at` (Inst @"e" a, Inst @"pfx" pfx, Inst @"env" env, Inst @"b1" b1, Inst @"b2" b2)
                    =: interpInEnv (ST.tuple (nm, val2) .: env1) b
                    ?? ih `at` (Inst @"e" b, Inst @"pfx" (ST.tuple (nm, val2) .: pfx), Inst @"env" env, Inst @"b1" b1, Inst @"b2" b2)
                    =: interpInEnv (ST.tuple (nm, val2) .: env2) b
                    ?? letH `at` (Inst @"env" env2, Inst @"nm" nm, Inst @"a" a, Inst @"b" b)
                    =: interpInEnv env2 (sLet nm a b)
                    =: qed
                ]

-- | A shadowed binding in the environment does not affect interpretation.
-- The @pfx@ parameter allows the shadow to occur at any depth.
--
-- >>> runTPWith cvc5 envShadow
-- Lemma: measureNonNeg                    Q.E.D.
-- Lemma: lookupShadowPfx                  Q.E.D.
-- Lemma: sqrCong                          Q.E.D.
-- Lemma: sqrHelper                        Q.E.D.
-- Lemma: addHelper                        Q.E.D.
-- Lemma: mulCongL                         Q.E.D.
-- Lemma: mulCongR                         Q.E.D.
-- Lemma: mulHelper                        Q.E.D.
-- Lemma: letHelper                        Q.E.D.
-- Inductive lemma (strong): envShadow
--   Step: Measure is non-negative         Q.E.D.
--   Step: 1 (7 way case split)
--     Step: 1.1 (Var)                     Q.E.D.
--     Step: 1.2 (Con)                     Q.E.D.
--     Step: 1.3.1 (Sqr)                   Q.E.D.
--     Step: 1.3.2                         Q.E.D.
--     Step: 1.3.3                         Q.E.D.
--     Step: 1.4 (Inc)                     Q.E.D.
--     Step: 1.5.1 (Add)                   Q.E.D.
--     Step: 1.5.2                         Q.E.D.
--     Step: 1.5.3                         Q.E.D.
--     Step: 1.6.1 (Mul)                   Q.E.D.
--     Step: 1.6.2                         Q.E.D.
--     Step: 1.6.3                         Q.E.D.
--     Step: 1.6.4                         Q.E.D.
--     Step: 1.7.1 (Let)                   Q.E.D.
--     Step: 1.7.2                         Q.E.D.
--     Step: 1.7.3                         Q.E.D.
--     Step: 1.7.4                         Q.E.D.
--     Step: 1.Completeness                Q.E.D.
--   Result:                               Q.E.D.
-- [Proven] envShadow :: Ɐe ∷ (Expr [Char] Integer) → Ɐpfx ∷ [([Char], Integer)] → Ɐenv ∷ [([Char], Integer)] → Ɐb1 ∷ ([Char], Integer) → Ɐb2 ∷ ([Char], Integer) → Bool
envShadow :: TP (Proof (Forall "e" Exp -> Forall "pfx" EL -> Forall "env" EL
                     -> Forall "b1" (String, Integer) -> Forall "b2" (String, Integer) -> SBool))
envShadow = do
   mnn   <- recall "measureNonNeg"    measureNonNeg
   lkShP <- recall "lookupShadowPfx" lookupShadowPfx
   sqrC  <- recall "sqrCong"         sqrCong
   sqrH  <- recall "sqrHelper"       sqrHelper
   addH  <- recall "addHelper"       addHelper
   mulCL <- recall "mulCongL"        mulCongL
   mulCR <- recall "mulCongR"        mulCongR
   mulH  <- recall "mulHelper"       mulHelper
   letH  <- recall "letHelper"       letHelper

   sInduct "envShadow"
     (\(Forall @"e" (e :: SE)) (Forall @"pfx" (pfx :: E)) (Forall @"env" (env :: E))
       (Forall @"b1" (b1 :: STuple String Integer)) (Forall @"b2" (b2 :: STuple String Integer)) ->
       let (x, _)  = ST.untuple b1
           (y, _)  = ST.untuple b2
       in x .== y .=> interpInEnv (pfx ++ b1 .: b2 .: env) e .== interpInEnv (pfx ++ b1 .: env) e)
     (\e _ _ _ _ -> size e :: SInteger, [proofOf mnn]) $
     \ih e pfx env b1 b2 ->
       let (x, _) = ST.untuple b1
           (y, _) = ST.untuple b2
           env1 = pfx ++ b1 .: b2 .: env
           env2 = pfx ++ b1 .: env
       in [x .== y]
       |- cases [ isVar e
                  ==> let nm = svar e
                    in interpInEnv env1 (sVar nm)
                    ?? "Var"
                    ?? lkShP `at` (Inst @"pfx" pfx, Inst @"k" nm, Inst @"b1" b1, Inst @"b2" b2, Inst @"env" env)
                    =: interpInEnv env2 (sVar nm)
                    =: qed

                , isCon e
                  ==> let v = scon e
                    in interpInEnv env1 (sCon v)
                    ?? "Con"
                    =: interpInEnv env2 (sCon v)
                    =: qed

                , isSqr e
                  ==> let a = ssqrVal e
                    in interpInEnv env1 (sSqr a)
                    ?? "Sqr"
                    ?? sqrH `at` (Inst @"env" env1, Inst @"a" a)
                    =: interpInEnv env1 a * interpInEnv env1 a
                    ?? ih `at` (Inst @"e" a, Inst @"pfx" pfx, Inst @"env" env, Inst @"b1" b1, Inst @"b2" b2)
                    ?? sqrC `at` (Inst @"a" (interpInEnv env1 a), Inst @"b" (interpInEnv env2 a))
                    =: interpInEnv env2 a * interpInEnv env2 a
                    ?? sqrH `at` (Inst @"env" env2, Inst @"a" a)
                    =: interpInEnv env2 (sSqr a)
                    =: qed

                , isInc e
                  ==> let a = sincVal e
                    in interpInEnv env1 (sInc a)
                    ?? "Inc"
                    ?? ih `at` (Inst @"e" a, Inst @"pfx" pfx, Inst @"env" env, Inst @"b1" b1, Inst @"b2" b2)
                    =: interpInEnv env2 (sInc a)
                    =: qed

                , isAdd e
                  ==> let a = sadd1 e
                          b = sadd2 e
                    in interpInEnv env1 (sAdd a b)
                    ?? "Add"
                    ?? addH `at` (Inst @"env" env1, Inst @"a" a, Inst @"b" b)
                    =: interpInEnv env1 a + interpInEnv env1 b
                    ?? ih `at` (Inst @"e" a, Inst @"pfx" pfx, Inst @"env" env, Inst @"b1" b1, Inst @"b2" b2)
                    ?? ih `at` (Inst @"e" b, Inst @"pfx" pfx, Inst @"env" env, Inst @"b1" b1, Inst @"b2" b2)
                    =: interpInEnv env2 a + interpInEnv env2 b
                    ?? addH `at` (Inst @"env" env2, Inst @"a" a, Inst @"b" b)
                    =: interpInEnv env2 (sAdd a b)
                    =: qed

                , isMul e
                  ==> let a = smul1 e
                          b = smul2 e
                    in interpInEnv env1 (sMul a b)
                    ?? "Mul"
                    ?? mulH `at` (Inst @"env" env1, Inst @"a" a, Inst @"b" b)
                    =: interpInEnv env1 a * interpInEnv env1 b
                    ?? ih `at` (Inst @"e" a, Inst @"pfx" pfx, Inst @"env" env, Inst @"b1" b1, Inst @"b2" b2)
                    ?? mulCL `at` (Inst @"a" (interpInEnv env1 a), Inst @"b" (interpInEnv env2 a), Inst @"c" (interpInEnv env1 b))
                    =: interpInEnv env2 a * interpInEnv env1 b
                    ?? ih `at` (Inst @"e" b, Inst @"pfx" pfx, Inst @"env" env, Inst @"b1" b1, Inst @"b2" b2)
                    ?? mulCR `at` (Inst @"a" (interpInEnv env2 a), Inst @"b" (interpInEnv env1 b), Inst @"c" (interpInEnv env2 b))
                    =: interpInEnv env2 a * interpInEnv env2 b
                    ?? mulH `at` (Inst @"env" env2, Inst @"a" a, Inst @"b" b)
                    =: interpInEnv env2 (sMul a b)
                    =: qed

                , isLet e
                  ==> let nm = slvar  e
                          a  = slval  e
                          b  = slbody e
                          val1 = interpInEnv env1 a
                          val2 = interpInEnv env2 a
                    in interpInEnv env1 (sLet nm a b)
                    ?? "Let"
                    ?? letH `at` (Inst @"env" env1, Inst @"nm" nm, Inst @"a" a, Inst @"b" b)
                    =: interpInEnv (ST.tuple (nm, val1) .: env1) b
                    ?? ih `at` (Inst @"e" a, Inst @"pfx" pfx, Inst @"env" env, Inst @"b1" b1, Inst @"b2" b2)
                    =: interpInEnv (ST.tuple (nm, val2) .: env1) b
                    ?? ih `at` (Inst @"e" b, Inst @"pfx" (ST.tuple (nm, val2) .: pfx), Inst @"env" env, Inst @"b1" b1, Inst @"b2" b2)
                    =: interpInEnv (ST.tuple (nm, val2) .: env2) b
                    ?? letH `at` (Inst @"env" env2, Inst @"nm" nm, Inst @"a" a, Inst @"b" b)
                    =: interpInEnv env2 (sLet nm a b)
                    =: qed
                ]

-- * Substitution correctness

-- | Unfolding @interpInEnv@ over @Var@.
--
-- >>> runTP varHelper
-- Lemma: varHelper                        Q.E.D.
-- [Proven] varHelper :: Ɐenv ∷ [([Char], Integer)] → Ɐnm ∷ [Char] → Bool
varHelper :: TP (Proof (Forall "env" EL -> Forall "nm" String -> SBool))
varHelper = lemma "varHelper"
                  (\(Forall @"env" (env :: E)) (Forall @"nm" nm) ->
                        interpInEnv env (sVar nm) .== SL.lookup nm env) []

-- | Substitution preserves semantics: interpreting in an extended environment
-- is the same as substituting and interpreting in the original environment.
--
-- >>> runTPWith cvc5 substCorrect
-- Lemma: measureNonNeg                    Q.E.D.
-- Lemma: sqrCong                          Q.E.D.
-- Lemma: sqrHelper                        Q.E.D.
-- Lemma: addHelper                        Q.E.D.
-- Lemma: mulCongL                         Q.E.D.
-- Lemma: mulCongR                         Q.E.D.
-- Lemma: mulHelper                        Q.E.D.
-- Lemma: letHelper                        Q.E.D.
-- Lemma: varHelper                        Q.E.D.
-- Lemma: envSwap                          Q.E.D.
-- Lemma: envShadow                        Q.E.D.
-- Inductive lemma (strong): substCorrect
--   Step: Measure is non-negative         Q.E.D.
--   Step: 1 (7 way case split)
--     Step: 1.1 (2 way case split)
--       Step: 1.1.1.1 (Var)               Q.E.D.
--       Step: 1.1.1.2                     Q.E.D.
--       Step: 1.1.1.3                     Q.E.D.
--       Step: 1.1.1.4                     Q.E.D.
--       Step: 1.1.1.5                     Q.E.D.
--       Step: 1.1.2.1 (Var)               Q.E.D.
--       Step: 1.1.2.2                     Q.E.D.
--       Step: 1.1.2.3                     Q.E.D.
--       Step: 1.1.2.4                     Q.E.D.
--       Step: 1.1.2.5                     Q.E.D.
--       Step: 1.1.Completeness            Q.E.D.
--     Step: 1.2 (Con)                     Q.E.D.
--     Step: 1.3.1 (Sqr)                   Q.E.D.
--     Step: 1.3.2                         Q.E.D.
--     Step: 1.3.3                         Q.E.D.
--     Step: 1.3.4                         Q.E.D.
--     Step: 1.4 (Inc)                     Q.E.D.
--     Step: 1.5.1 (Add)                   Q.E.D.
--     Step: 1.5.2                         Q.E.D.
--     Step: 1.5.3                         Q.E.D.
--     Step: 1.5.4                         Q.E.D.
--     Step: 1.6.1 (Mul)                   Q.E.D.
--     Step: 1.6.2                         Q.E.D.
--     Step: 1.6.3                         Q.E.D.
--     Step: 1.6.4                         Q.E.D.
--     Step: 1.6.5                         Q.E.D.
--     Step: 1.7.1 (Let)                   Q.E.D.
--     Step: 1.7.2 (2 way case split)
--       Step: 1.7.2.1.1                   Q.E.D.
--       Step: 1.7.2.1.2 (shadow)          Q.E.D.
--       Step: 1.7.2.1.3                   Q.E.D.
--       Step: 1.7.2.1.4                   Q.E.D.
--       Step: 1.7.2.1.5                   Q.E.D.
--       Step: 1.7.2.2.1                   Q.E.D.
--       Step: 1.7.2.2.2 (swap)            Q.E.D.
--       Step: 1.7.2.2.3                   Q.E.D.
--       Step: 1.7.2.2.4                   Q.E.D.
--       Step: 1.7.2.2.5                   Q.E.D.
--       Step: 1.7.2.2.6                   Q.E.D.
--       Step: 1.7.2.Completeness          Q.E.D.
--     Step: 1.Completeness                Q.E.D.
--   Result:                               Q.E.D.
-- [Proven] substCorrect :: Ɐe ∷ (Expr [Char] Integer) → Ɐnm ∷ [Char] → Ɐv ∷ Integer → Ɐenv ∷ [([Char], Integer)] → Bool
substCorrect :: TP (Proof (Forall "e" Exp -> Forall "nm" String -> Forall "v" Integer -> Forall "env" EL -> SBool))
substCorrect = do
   mnn  <- recall "measureNonNeg"  measureNonNeg
   sqrC <- recall "sqrCong"        sqrCong
   sqrH <- recall "sqrHelper"      sqrHelper
   addH <- recall "addHelper"      addHelper
   mulCL <- recall "mulCongL"      mulCongL
   mulCR <- recall "mulCongR"      mulCongR
   mulH  <- recall "mulHelper"     mulHelper
   letH  <- recall "letHelper"     letHelper
   varH  <- recall "varHelper"     varHelper
   eSwp  <- recall "envSwap"       envSwap
   eShd  <- recall "envShadow"     envShadow

   sInduct "substCorrect"
     (\(Forall @"e" (e :: SE)) (Forall @"nm" (nm :: SString)) (Forall @"v" (v :: SInteger)) (Forall @"env" (env :: E)) ->
         interpInEnv (ST.tuple (nm, v) .: env) e .== interpInEnv env (subst nm v e))
     (\e _ _ _ -> size e :: SInteger, [proofOf mnn]) $
     \ih e nm v env ->
       let nmv  = ST.tuple (nm, v)
           env1 = nmv .: env
       in []
       |- cases [ isVar e
                  ==> let x = svar e
                    in interpInEnv env1 (sVar x)
                    ?? "Var"
                    =: cases [ x .== nm
                               ==> interpInEnv env1 (sVar nm)
                                ?? varH `at` (Inst @"env" env1, Inst @"nm" nm)
                                =: SL.lookup nm env1
                                =: v
                                =: interpInEnv env (sCon v)
                                =: interpInEnv env (subst nm v (sVar nm))
                                =: qed
                             , x ./= nm
                               ==> interpInEnv env1 (sVar x)
                                ?? varH `at` (Inst @"env" env1, Inst @"nm" x)
                                =: SL.lookup x env1
                                =: SL.lookup x env
                                ?? varH `at` (Inst @"env" env, Inst @"nm" x)
                                =: interpInEnv env (sVar x)
                                =: interpInEnv env (subst nm v (sVar x))
                                =: qed
                             ]

                , isCon e
                  ==> let c = scon e
                    in interpInEnv env1 (sCon c)
                    ?? "Con"
                    =: interpInEnv env (subst nm v (sCon c))
                    =: qed

                , isSqr e
                  ==> let a = ssqrVal e
                    in interpInEnv env1 (sSqr a)
                    ?? "Sqr"
                    ?? sqrH `at` (Inst @"env" env1, Inst @"a" a)
                    =: interpInEnv env1 a * interpInEnv env1 a
                    ?? ih `at` (Inst @"e" a, Inst @"nm" nm, Inst @"v" v, Inst @"env" env)
                    ?? sqrC `at` (Inst @"a" (interpInEnv env1 a), Inst @"b" (interpInEnv env (subst nm v a)))
                    =: interpInEnv env (subst nm v a) * interpInEnv env (subst nm v a)
                    ?? sqrH `at` (Inst @"env" env, Inst @"a" (subst nm v a))
                    =: interpInEnv env (sSqr (subst nm v a))
                    =: interpInEnv env (subst nm v (sSqr a))
                    =: qed

                , isInc e
                  ==> let a = sincVal e
                    in interpInEnv env1 (sInc a)
                    ?? "Inc"
                    ?? ih `at` (Inst @"e" a, Inst @"nm" nm, Inst @"v" v, Inst @"env" env)
                    =: interpInEnv env (subst nm v (sInc a))
                    =: qed

                , isAdd e
                  ==> let a = sadd1 e
                          b = sadd2 e
                    in interpInEnv env1 (sAdd a b)
                    ?? "Add"
                    ?? addH `at` (Inst @"env" env1, Inst @"a" a, Inst @"b" b)
                    =: interpInEnv env1 a + interpInEnv env1 b
                    ?? ih `at` (Inst @"e" a, Inst @"nm" nm, Inst @"v" v, Inst @"env" env)
                    ?? ih `at` (Inst @"e" b, Inst @"nm" nm, Inst @"v" v, Inst @"env" env)
                    =: interpInEnv env (subst nm v a) + interpInEnv env (subst nm v b)
                    ?? addH `at` (Inst @"env" env, Inst @"a" (subst nm v a), Inst @"b" (subst nm v b))
                    =: interpInEnv env (sAdd (subst nm v a) (subst nm v b))
                    =: interpInEnv env (subst nm v (sAdd a b))
                    =: qed

                , isMul e
                  ==> let a = smul1 e
                          b = smul2 e
                    in interpInEnv env1 (sMul a b)
                    ?? "Mul"
                    ?? mulH `at` (Inst @"env" env1, Inst @"a" a, Inst @"b" b)
                    =: interpInEnv env1 a * interpInEnv env1 b
                    ?? ih `at` (Inst @"e" a, Inst @"nm" nm, Inst @"v" v, Inst @"env" env)
                    ?? mulCL `at` (Inst @"a" (interpInEnv env1 a), Inst @"b" (interpInEnv env (subst nm v a)), Inst @"c" (interpInEnv env1 b))
                    =: interpInEnv env (subst nm v a) * interpInEnv env1 b
                    ?? ih `at` (Inst @"e" b, Inst @"nm" nm, Inst @"v" v, Inst @"env" env)
                    ?? mulCR `at` (Inst @"a" (interpInEnv env (subst nm v a)), Inst @"b" (interpInEnv env1 b), Inst @"c" (interpInEnv env (subst nm v b)))
                    =: interpInEnv env (subst nm v a) * interpInEnv env (subst nm v b)
                    ?? mulH `at` (Inst @"env" env, Inst @"a" (subst nm v a), Inst @"b" (subst nm v b))
                    =: interpInEnv env (sMul (subst nm v a) (subst nm v b))
                    =: interpInEnv env (subst nm v (sMul a b))
                    =: qed

                , isLet e
                  ==> let x   = slvar  e
                          a   = slval  e
                          b   = slbody e
                          val = interpInEnv env1 a
                    in interpInEnv env1 (sLet x a b)
                    ?? "Let"
                    ?? letH `at` (Inst @"env" env1, Inst @"nm" x, Inst @"a" a, Inst @"b" b)
                    =: interpInEnv (ST.tuple (x, val) .: env1) b
                    =: cases [ x .== nm
                               ==> let xv = ST.tuple (x, val)
                                 in interpInEnv (xv .: nmv .: env) b
                                 ?? "shadow"
                                 ?? eShd `at` (Inst @"e" b, Inst @"pfx" (SL.nil :: E), Inst @"env" env, Inst @"b1" xv, Inst @"b2" nmv)
                                 =: interpInEnv (xv .: env) b
                                 ?? ih `at` (Inst @"e" a, Inst @"nm" nm, Inst @"v" v, Inst @"env" env)
                                 =: interpInEnv (ST.tuple (x, interpInEnv env (subst nm v a)) .: env) b
                                 ?? letH `at` (Inst @"env" env, Inst @"nm" x, Inst @"a" (subst nm v a), Inst @"b" b)
                                 =: interpInEnv env (sLet x (subst nm v a) b)
                                 =: interpInEnv env (subst nm v (sLet x a b))
                                 =: qed
                             , x ./= nm
                               ==> let xv = ST.tuple (x, val)
                                 in interpInEnv (xv .: nmv .: env) b
                                 ?? "swap"
                                 ?? eSwp `at` (Inst @"e" b, Inst @"pfx" (SL.nil :: E), Inst @"env" env, Inst @"b1" xv, Inst @"b2" nmv)
                                 =: interpInEnv (nmv .: xv .: env) b
                                 ?? ih `at` (Inst @"e" b, Inst @"nm" nm, Inst @"v" v, Inst @"env" (xv .: env))
                                 =: interpInEnv (xv .: env) (subst nm v b)
                                 ?? ih `at` (Inst @"e" a, Inst @"nm" nm, Inst @"v" v, Inst @"env" env)
                                 =: interpInEnv (ST.tuple (x, interpInEnv env (subst nm v a)) .: env) (subst nm v b)
                                 ?? letH `at` (Inst @"env" env, Inst @"nm" x, Inst @"a" (subst nm v a), Inst @"b" (subst nm v b))
                                 =: interpInEnv env (sLet x (subst nm v a) (subst nm v b))
                                 =: interpInEnv env (subst nm v (sLet x a b))
                                 =: qed
                             ]
                ]

-- | Simplification preserves semantics.
--
-- >>> runTPWith cvc5 simpCorrect
-- Lemma: sqrCong                          Q.E.D.
-- Lemma: sqrHelper                        Q.E.D.
-- Lemma: addHelper                        Q.E.D.
-- Lemma: mulCongL                         Q.E.D.
-- Lemma: mulCongR                         Q.E.D.
-- Lemma: mulHelper                        Q.E.D.
-- Lemma: letHelper                        Q.E.D.
-- Lemma: substCorrect                     Q.E.D.
-- Lemma: simpCorrect
--   Step: 1 (7 way case split)
--     Step: 1.1.1 (Var)                   Q.E.D.
--     Step: 1.1.2                         Q.E.D.
--     Step: 1.1.3                         Q.E.D.
--     Step: 1.2.1 (Con)                   Q.E.D.
--     Step: 1.2.2                         Q.E.D.
--     Step: 1.2.3                         Q.E.D.
--     Step: 1.3.1 (Sqr)                   Q.E.D.
--     Step: 1.3.2 (2 way case split)
--       Step: 1.3.2.1.1                   Q.E.D.
--       Step: 1.3.2.1.2 (Sqr Con)         Q.E.D.
--       Step: 1.3.2.1.3                   Q.E.D.
--       Step: 1.3.2.1.4                   Q.E.D.
--       Step: 1.3.2.1.5                   Q.E.D.
--       Step: 1.3.2.2.1                   Q.E.D.
--       Step: 1.3.2.2.2 (Sqr _)           Q.E.D.
--       Step: 1.3.2.Completeness          Q.E.D.
--     Step: 1.4.1 (Inc)                   Q.E.D.
--     Step: 1.4.2 (2 way case split)
--       Step: 1.4.2.1.1                   Q.E.D.
--       Step: 1.4.2.1.2 (Inc Con)         Q.E.D.
--       Step: 1.4.2.1.3                   Q.E.D.
--       Step: 1.4.2.2.1                   Q.E.D.
--       Step: 1.4.2.2.2 (Inc _)           Q.E.D.
--       Step: 1.4.2.Completeness          Q.E.D.
--     Step: 1.5.1 (Add)                   Q.E.D.
--     Step: 1.5.2 (6 way case split)
--       Step: 1.5.2.1.1                   Q.E.D.
--       Step: 1.5.2.1.2 (Add 0+b)         Q.E.D.
--       Step: 1.5.2.1.3                   Q.E.D.
--       Step: 1.5.2.2.1                   Q.E.D.
--       Step: 1.5.2.2.2 (Add a+0)         Q.E.D.
--       Step: 1.5.2.2.3                   Q.E.D.
--       Step: 1.5.2.3.1                   Q.E.D.
--       Step: 1.5.2.3.2 (Add Con)         Q.E.D.
--       Step: 1.5.2.3.3                   Q.E.D.
--       Step: 1.5.2.4 (2 way case split)
--         Step: 1.5.2.4.1.1               Q.E.D.
--         Step: 1.5.2.4.1.2 (Add 0,_)     Q.E.D.
--         Step: 1.5.2.4.1.3               Q.E.D.
--         Step: 1.5.2.4.2.1               Q.E.D.
--         Step: 1.5.2.4.2.2 (Add C,_)     Q.E.D.
--         Step: 1.5.2.4.Completeness      Q.E.D.
--       Step: 1.5.2.5 (2 way case split)
--         Step: 1.5.2.5.1.1               Q.E.D.
--         Step: 1.5.2.5.1.2 (Add _,0)     Q.E.D.
--         Step: 1.5.2.5.1.3               Q.E.D.
--         Step: 1.5.2.5.2.1               Q.E.D.
--         Step: 1.5.2.5.2.2 (Add _,C)     Q.E.D.
--         Step: 1.5.2.5.Completeness      Q.E.D.
--       Step: 1.5.2.6.1                   Q.E.D.
--       Step: 1.5.2.6.2 (Add _,_)         Q.E.D.
--       Step: 1.5.2.Completeness          Q.E.D.
--     Step: 1.6.1 (Mul)                   Q.E.D.
--     Step: 1.6.2 (8 way case split)
--       Step: 1.6.2.1.1                   Q.E.D.
--       Step: 1.6.2.1.2 (Mul 0*b)         Q.E.D.
--       Step: 1.6.2.1.3                   Q.E.D.
--       Step: 1.6.2.2.1                   Q.E.D.
--       Step: 1.6.2.2.2 (Mul a*0)         Q.E.D.
--       Step: 1.6.2.2.3                   Q.E.D.
--       Step: 1.6.2.3.1                   Q.E.D.
--       Step: 1.6.2.3.2 (Mul 1*b)         Q.E.D.
--       Step: 1.6.2.3.3                   Q.E.D.
--       Step: 1.6.2.3.4                   Q.E.D.
--       Step: 1.6.2.3.5                   Q.E.D.
--       Step: 1.6.2.4.1                   Q.E.D.
--       Step: 1.6.2.4.2 (Mul a*1)         Q.E.D.
--       Step: 1.6.2.4.3                   Q.E.D.
--       Step: 1.6.2.4.4                   Q.E.D.
--       Step: 1.6.2.4.5                   Q.E.D.
--       Step: 1.6.2.5.1                   Q.E.D.
--       Step: 1.6.2.5.2 (Mul Con)         Q.E.D.
--       Step: 1.6.2.5.3                   Q.E.D.
--       Step: 1.6.2.5.4                   Q.E.D.
--       Step: 1.6.2.5.5                   Q.E.D.
--       Step: 1.6.2.5.6                   Q.E.D.
--       Step: 1.6.2.6 (3 way case split)
--         Step: 1.6.2.6.1.1               Q.E.D.
--         Step: 1.6.2.6.1.2 (Mul 0,_)     Q.E.D.
--         Step: 1.6.2.6.1.3               Q.E.D.
--         Step: 1.6.2.6.2.1               Q.E.D.
--         Step: 1.6.2.6.2.2 (Mul 1,_)     Q.E.D.
--         Step: 1.6.2.6.2.3               Q.E.D.
--         Step: 1.6.2.6.2.4               Q.E.D.
--         Step: 1.6.2.6.2.5               Q.E.D.
--         Step: 1.6.2.6.3.1               Q.E.D.
--         Step: 1.6.2.6.3.2 (Mul C,_)     Q.E.D.
--         Step: 1.6.2.6.Completeness      Q.E.D.
--       Step: 1.6.2.7 (3 way case split)
--         Step: 1.6.2.7.1.1               Q.E.D.
--         Step: 1.6.2.7.1.2 (Mul _,0)     Q.E.D.
--         Step: 1.6.2.7.1.3               Q.E.D.
--         Step: 1.6.2.7.2.1               Q.E.D.
--         Step: 1.6.2.7.2.2 (Mul _,1)     Q.E.D.
--         Step: 1.6.2.7.2.3               Q.E.D.
--         Step: 1.6.2.7.2.4               Q.E.D.
--         Step: 1.6.2.7.2.5               Q.E.D.
--         Step: 1.6.2.7.3.1               Q.E.D.
--         Step: 1.6.2.7.3.2 (Mul _,C)     Q.E.D.
--         Step: 1.6.2.7.Completeness      Q.E.D.
--       Step: 1.6.2.8.1                   Q.E.D.
--       Step: 1.6.2.8.2 (Mul _,_)         Q.E.D.
--       Step: 1.6.2.Completeness          Q.E.D.
--     Step: 1.7.1 (Let)                   Q.E.D.
--     Step: 1.7.2 (2 way case split)
--       Step: 1.7.2.1.1                   Q.E.D.
--       Step: 1.7.2.1.2 (Let Con)         Q.E.D.
--       Step: 1.7.2.1.3                   Q.E.D.
--       Step: 1.7.2.1.4                   Q.E.D.
--       Step: 1.7.2.2.1                   Q.E.D.
--       Step: 1.7.2.2.2 (Let _)           Q.E.D.
--       Step: 1.7.2.Completeness          Q.E.D.
--     Step: 1.Completeness                Q.E.D.
--   Result:                               Q.E.D.
-- [Proven] simpCorrect :: Ɐe ∷ (Expr [Char] Integer) → Ɐenv ∷ [([Char], Integer)] → Bool
simpCorrect :: TP (Proof (Forall "e" Exp -> Forall "env" EL -> SBool))
simpCorrect = do
   sqrC  <- recall "sqrCong"      sqrCong
   sqrH  <- recall "sqrHelper"    sqrHelper
   addH  <- recall "addHelper"    addHelper
   mulCL <- recall "mulCongL"     mulCongL
   mulCR <- recall "mulCongR"     mulCongR
   mulH  <- recall "mulHelper"    mulHelper
   letH  <- recall "letHelper"    letHelper
   subC  <- recall "substCorrect" substCorrect

   calc "simpCorrect"
     (\(Forall @"e" (e :: SE)) (Forall @"env" (env :: E)) -> interpInEnv env (simplify e) .== interpInEnv env e) $
     \e env -> []
     |- [pCase|Expr e of
          Var nm     -> interpInEnv env (simplify e)
                     ?? "Var"
                     =: interpInEnv env (simplify (sVar nm))
                     =: interpInEnv env (sVar nm)
                     =: interpInEnv env e
                     =: qed

          Con c      -> interpInEnv env (simplify e)
                     ?? "Con"
                     =: interpInEnv env (simplify (sCon c))
                     =: interpInEnv env (sCon c)
                     =: interpInEnv env e
                     =: qed

          Sqr a      -> interpInEnv env (simplify e)
                     ?? "Sqr"
                     =: interpInEnv env (simplify (sSqr a))
                     =: cases [ isCon a
                                 ==> let v = scon a
                                   in interpInEnv env (simplify (sSqr (sCon v)))
                                   ?? "Sqr Con"
                                   =: interpInEnv env (sCon (v * v))
                                   ?? interpInEnv env (sCon (v * v)) .== v * v
                                   =: v * v
                                   ?? sqrC `at` (Inst @"a" (interpInEnv env (sCon v)), Inst @"b" v)
                                   =: interpInEnv env (sCon v) * interpInEnv env (sCon v)
                                   ?? sqrH `at` (Inst @"env" env, Inst @"a" (sCon v))
                                   =: interpInEnv env (sSqr (sCon v))
                                   =: qed
                               , sNot (isCon a)
                                 ==> interpInEnv env (simplify (sSqr a))
                                   ?? "Sqr _"
                                   =: interpInEnv env (sSqr a)
                                   =: qed
                               ]

          Inc a      -> interpInEnv env (simplify e)
                     ?? "Inc"
                     =: interpInEnv env (simplify (sInc a))
                     =: cases [ isCon a
                                 ==> let v = scon a
                                   in interpInEnv env (simplify (sInc (sCon v)))
                                   ?? "Inc Con"
                                   =: interpInEnv env (sCon (v + 1))
                                   =: interpInEnv env (sInc (sCon v))
                                   =: qed
                               , sNot (isCon a)
                                 ==> interpInEnv env (simplify (sInc a))
                                   ?? "Inc _"
                                   =: interpInEnv env (sInc a)
                                   =: qed
                               ]

          Add a b    -> interpInEnv env (simplify e)
                     ?? "Add"
                     =: interpInEnv env (simplify (sAdd a b))
                     =: cases [ isCon a .&& scon a .== 0
                                 ==> interpInEnv env (simplify (sAdd (sCon 0) b))
                                   ?? "Add 0+b"
                                   =: interpInEnv env b
                                   ?? addH `at` (Inst @"env" env, Inst @"a" (sCon 0), Inst @"b" b)
                                   =: interpInEnv env (sAdd (sCon 0) b)
                                   =: qed

                               , isCon b .&& scon b .== 0
                                 ==> interpInEnv env (simplify (sAdd a (sCon 0)))
                                   ?? "Add a+0"
                                   =: interpInEnv env a
                                   ?? addH `at` (Inst @"env" env, Inst @"a" a, Inst @"b" (sCon 0))
                                   =: interpInEnv env (sAdd a (sCon 0))
                                   =: qed

                               , isCon a .&& isCon b
                                 ==> let va = scon a; vb = scon b
                                   in interpInEnv env (simplify (sAdd (sCon va) (sCon vb)))
                                   ?? "Add Con"
                                   =: interpInEnv env (sCon (va + vb))
                                   ?? addH `at` (Inst @"env" env, Inst @"a" (sCon va), Inst @"b" (sCon vb))
                                   =: interpInEnv env (sAdd (sCon va) (sCon vb))
                                   =: qed

                               , isCon a .&& sNot (isCon b)
                                 ==> let va = scon a
                                   in cases [ va .== 0
                                              ==> interpInEnv env (simplify (sAdd (sCon 0) b))
                                                ?? "Add 0,_"
                                                =: interpInEnv env b
                                                ?? addH `at` (Inst @"env" env, Inst @"a" (sCon 0), Inst @"b" b)
                                                =: interpInEnv env (sAdd (sCon 0) b)
                                                =: qed
                                            , va ./= 0
                                              ==> interpInEnv env (simplify (sAdd (sCon va) b))
                                                ?? "Add C,_"
                                                =: interpInEnv env (sAdd (sCon va) b)
                                                =: qed
                                            ]

                               , sNot (isCon a) .&& isCon b
                                 ==> let vb = scon b
                                   in cases [ vb .== 0
                                              ==> interpInEnv env (simplify (sAdd a (sCon 0)))
                                                ?? "Add _,0"
                                                =: interpInEnv env a
                                                ?? addH `at` (Inst @"env" env, Inst @"a" a, Inst @"b" (sCon 0))
                                                =: interpInEnv env (sAdd a (sCon 0))
                                                =: qed
                                            , vb ./= 0
                                              ==> interpInEnv env (simplify (sAdd a (sCon vb)))
                                                ?? "Add _,C"
                                                =: interpInEnv env (sAdd a (sCon vb))
                                                =: qed
                                            ]

                               , sNot (isCon a) .&& sNot (isCon b)
                                 ==> interpInEnv env (simplify (sAdd a b))
                                   ?? "Add _,_"
                                   =: interpInEnv env (sAdd a b)
                                   =: qed
                               ]

          Mul a b    -> interpInEnv env (simplify e)
                     ?? "Mul"
                     =: interpInEnv env (simplify (sMul a b))
                     =: cases [ isCon a .&& scon a .== 0
                                 ==> interpInEnv env (simplify (sMul (sCon 0) b))
                                   ?? "Mul 0*b"
                                   =: interpInEnv env (sCon 0)
                                   ?? mulH `at` (Inst @"env" env, Inst @"a" (sCon 0), Inst @"b" b)
                                   =: interpInEnv env (sMul (sCon 0) b)
                                   =: qed

                               , isCon b .&& scon b .== 0
                                 ==> interpInEnv env (simplify (sMul a (sCon 0)))
                                   ?? "Mul a*0"
                                   =: interpInEnv env (sCon 0)
                                   ?? mulH `at` (Inst @"env" env, Inst @"a" a, Inst @"b" (sCon 0))
                                   =: interpInEnv env (sMul a (sCon 0))
                                   =: qed

                               , isCon a .&& scon a .== 1
                                 ==> interpInEnv env (simplify (sMul (sCon 1) b))
                                   ?? "Mul 1*b"
                                   =: interpInEnv env b
                                   =: 1 * interpInEnv env b
                                   ?? interpInEnv env (sCon 1) .== 1
                                   =: interpInEnv env (sCon 1) * interpInEnv env b
                                   ?? mulH `at` (Inst @"env" env, Inst @"a" (sCon 1), Inst @"b" b)
                                   =: interpInEnv env (sMul (sCon 1) b)
                                   =: qed

                               , isCon b .&& scon b .== 1
                                 ==> interpInEnv env (simplify (sMul a (sCon 1)))
                                   ?? "Mul a*1"
                                   =: interpInEnv env a
                                   =: interpInEnv env a * 1
                                   ?? interpInEnv env (sCon 1) .== 1
                                   =: interpInEnv env a * interpInEnv env (sCon 1)
                                   ?? mulH `at` (Inst @"env" env, Inst @"a" a, Inst @"b" (sCon 1))
                                   =: interpInEnv env (sMul a (sCon 1))
                                   =: qed

                               , isCon a .&& isCon b
                                 ==> let va = scon a; vb = scon b
                                   in interpInEnv env (simplify (sMul (sCon va) (sCon vb)))
                                   ?? "Mul Con"
                                   ?? simplify (sMul (sCon va) (sCon vb)) .== sCon (va * vb)
                                   =: interpInEnv env (sCon (va * vb))
                                   ?? interpInEnv env (sCon (va * vb)) .== va * vb
                                   =: va * vb
                                   ?? mulCL `at` (Inst @"a" (interpInEnv env (sCon va)), Inst @"b" va, Inst @"c" vb)
                                   =: interpInEnv env (sCon va) * vb
                                   ?? mulCR `at` (Inst @"a" (interpInEnv env (sCon va)), Inst @"b" (interpInEnv env (sCon vb)), Inst @"c" vb)
                                   =: interpInEnv env (sCon va) * interpInEnv env (sCon vb)
                                   ?? mulH `at` (Inst @"env" env, Inst @"a" (sCon va), Inst @"b" (sCon vb))
                                   =: interpInEnv env (sMul (sCon va) (sCon vb))
                                   =: qed

                               , isCon a .&& sNot (isCon b)
                                 ==> let va = scon a
                                   in cases [ va .== 0
                                              ==> interpInEnv env (simplify (sMul (sCon 0) b))
                                                ?? "Mul 0,_"
                                                =: interpInEnv env (sCon 0)
                                                ?? mulH `at` (Inst @"env" env, Inst @"a" (sCon 0), Inst @"b" b)
                                                =: interpInEnv env (sMul (sCon 0) b)
                                                =: qed
                                            , va .== 1
                                              ==> interpInEnv env (simplify (sMul (sCon 1) b))
                                                ?? "Mul 1,_"
                                                =: interpInEnv env b
                                                =: 1 * interpInEnv env b
                                                ?? interpInEnv env (sCon 1) .== 1
                                                =: interpInEnv env (sCon 1) * interpInEnv env b
                                                ?? mulH `at` (Inst @"env" env, Inst @"a" (sCon 1), Inst @"b" b)
                                                =: interpInEnv env (sMul (sCon 1) b)
                                                =: qed
                                            , va ./= 0 .&& va ./= 1
                                              ==> interpInEnv env (simplify (sMul (sCon va) b))
                                                ?? "Mul C,_"
                                                =: interpInEnv env (sMul (sCon va) b)
                                                =: qed
                                            ]

                               , sNot (isCon a) .&& isCon b
                                 ==> let vb = scon b
                                   in cases [ vb .== 0
                                              ==> interpInEnv env (simplify (sMul a (sCon 0)))
                                                ?? "Mul _,0"
                                                =: interpInEnv env (sCon 0)
                                                ?? mulH `at` (Inst @"env" env, Inst @"a" a, Inst @"b" (sCon 0))
                                                =: interpInEnv env (sMul a (sCon 0))
                                                =: qed
                                            , vb .== 1
                                              ==> interpInEnv env (simplify (sMul a (sCon 1)))
                                                ?? "Mul _,1"
                                                =: interpInEnv env a
                                                =: interpInEnv env a * 1
                                                ?? interpInEnv env (sCon 1) .== 1
                                                =: interpInEnv env a * interpInEnv env (sCon 1)
                                                ?? mulH `at` (Inst @"env" env, Inst @"a" a, Inst @"b" (sCon 1))
                                                =: interpInEnv env (sMul a (sCon 1))
                                                =: qed
                                            , vb ./= 0 .&& vb ./= 1
                                              ==> interpInEnv env (simplify (sMul a (sCon vb)))
                                                ?? "Mul _,C"
                                                =: interpInEnv env (sMul a (sCon vb))
                                                =: qed
                                            ]

                               , sNot (isCon a) .&& sNot (isCon b)
                                 ==> interpInEnv env (simplify (sMul a b))
                                   ?? "Mul _,_"
                                   =: interpInEnv env (sMul a b)
                                   =: qed
                               ]

          Let nm a b -> interpInEnv env (simplify e)
                     ?? "Let"
                     =: interpInEnv env (simplify (sLet nm a b))
                     =: cases [ isCon a
                                 ==> let v = scon a
                                   in interpInEnv env (simplify (sLet nm (sCon v) b))
                                   ?? "Let Con"
                                   =: interpInEnv env (subst nm v b)
                                   ?? subC `at` (Inst @"e" b, Inst @"nm" nm, Inst @"v" v, Inst @"env" env)
                                   =: interpInEnv (ST.tuple (nm, v) .: env) b
                                   ?? letH `at` (Inst @"env" env, Inst @"nm" nm, Inst @"a" (sCon v), Inst @"b" b)
                                   =: interpInEnv env (sLet nm (sCon v) b)
                                   =: qed
                               , sNot (isCon a)
                                 ==> interpInEnv env (simplify (sLet nm a b))
                                   ?? "Let _"
                                   =: interpInEnv env (sLet nm a b)
                                   =: qed
                               ]
        |]

-- | Constant folding preserves the semantics: interpreting an expression
-- is the same as constant-folding it first and then interpreting the result.
--
-- >>> runTPWith cvc5 cfoldCorrect
-- Lemma: measureNonNeg                    Q.E.D.
-- Lemma: simpCorrect                      Q.E.D.
-- Lemma: sqrCong                          Q.E.D.
-- Lemma: sqrHelper                        Q.E.D.
-- Lemma: mulCongL                         Q.E.D.
-- Lemma: mulCongR                         Q.E.D.
-- Lemma: mulHelper                        Q.E.D.
-- Inductive lemma (strong): cfoldCorrect
--   Step: Measure is non-negative         Q.E.D.
--   Step: 1 (7 way case split)
--     Step: 1.1.1 (case Var)              Q.E.D.
--     Step: 1.1.2                         Q.E.D.
--     Step: 1.1.3                         Q.E.D.
--     Step: 1.2.1 (case Con)              Q.E.D.
--     Step: 1.2.2                         Q.E.D.
--     Step: 1.2.3                         Q.E.D.
--     Step: 1.3.1 (case Sqr)              Q.E.D.
--     Step: 1.3.2                         Q.E.D.
--     Step: 1.3.3                         Q.E.D.
--     Step: 1.3.4                         Q.E.D.
--     Step: 1.3.5                         Q.E.D.
--     Step: 1.3.6                         Q.E.D.
--     Step: 1.3.7                         Q.E.D.
--     Step: 1.4.1 (case Inc)              Q.E.D.
--     Step: 1.4.2                         Q.E.D.
--     Step: 1.4.3                         Q.E.D.
--     Step: 1.4.4                         Q.E.D.
--     Step: 1.4.5                         Q.E.D.
--     Step: 1.5.1 (case Add)              Q.E.D.
--     Step: 1.5.2                         Q.E.D.
--     Step: 1.5.3                         Q.E.D.
--     Step: 1.5.4                         Q.E.D.
--     Step: 1.5.5                         Q.E.D.
--     Step: 1.6.1 (case Mul)              Q.E.D.
--     Step: 1.6.2                         Q.E.D.
--     Step: 1.6.3                         Q.E.D.
--     Step: 1.6.4                         Q.E.D.
--     Step: 1.6.5                         Q.E.D.
--     Step: 1.6.6                         Q.E.D.
--     Step: 1.6.7                         Q.E.D.
--     Step: 1.6.8                         Q.E.D.
--     Step: 1.7.1 (case Let)              Q.E.D.
--     Step: 1.7.2                         Q.E.D.
--     Step: 1.7.3                         Q.E.D.
--     Step: 1.7.4                         Q.E.D.
--     Step: 1.7.5                         Q.E.D.
--     Step: 1.Completeness                Q.E.D.
--   Result:                               Q.E.D.
-- [Proven] cfoldCorrect :: Ɐe ∷ (Expr [Char] Integer) → Ɐenv ∷ [([Char], Integer)] → Bool
cfoldCorrect :: TP (Proof (Forall "e" Exp -> Forall "env" EL -> SBool))
cfoldCorrect = do
   mnn  <- recall "measureNonNeg" measureNonNeg
   sc   <- recall "simpCorrect"   simpCorrect
   sqrC <- recall "sqrCong"       sqrCong
   sqrH <- recall "sqrHelper"     sqrHelper
   mulCL <- recall "mulCongL"     mulCongL
   mulCR <- recall "mulCongR"     mulCongR
   mulH <- recall "mulHelper"     mulHelper

   sInduct "cfoldCorrect"
     (\(Forall @"e" (e :: SE)) (Forall @"env" (env :: E)) -> interpInEnv env (cfold e) .== interpInEnv env e)
     (\e _ -> size e, [proofOf mnn]) $
     \ih e env -> []
       |- [pCase|Expr e of
            Var nm     -> interpInEnv env (cfold e)
                       ?? "case Var"
                       =: interpInEnv env (cfold (sVar nm))
                       =: interpInEnv env (sVar nm)
                       =: interpInEnv env e
                       =: qed

            Con v      -> interpInEnv env (cfold e)
                       ?? "case Con"
                       =: interpInEnv env (cfold (sCon v))
                       =: interpInEnv env (sCon v)
                       =: interpInEnv env e
                       =: qed

            Sqr a      -> interpInEnv env (cfold e)
                       ?? "case Sqr"
                       =: interpInEnv env (cfold (sSqr a))
                       =: interpInEnv env (simplify (sSqr (cfold a)))
                       ?? sc `at` (Inst @"e" (sSqr (cfold a)), Inst @"env" env)
                       =: interpInEnv env (sSqr (cfold a))
                       ?? sqrH `at` (Inst @"env" env, Inst @"a" (cfold a))
                       =: interpInEnv env (cfold a) * interpInEnv env (cfold a)
                       ?? ih `at` (Inst @"e" a, Inst @"env" env)
                       ?? sqrC `at` (Inst @"a" (interpInEnv env (cfold a)), Inst @"b" (interpInEnv env a))
                       =: interpInEnv env a * interpInEnv env a
                       ?? sqrH `at` (Inst @"env" env, Inst @"a" a)
                       =: interpInEnv env (sSqr a)
                       =: interpInEnv env e
                       =: qed

            Inc a      -> interpInEnv env (cfold e)
                       ?? "case Inc"
                       =: interpInEnv env (cfold (sInc a))
                       =: interpInEnv env (simplify (sInc (cfold a)))
                       ?? sc `at` (Inst @"e" (sInc (cfold a)), Inst @"env" env)
                       =: interpInEnv env (sInc (cfold a))
                       ?? ih `at` (Inst @"e" a, Inst @"env" env)
                       =: interpInEnv env (sInc a)
                       =: interpInEnv env e
                       =: qed

            Add a b    -> interpInEnv env (cfold e)
                       ?? "case Add"
                       =: interpInEnv env (cfold (sAdd a b))
                       =: interpInEnv env (simplify (sAdd (cfold a) (cfold b)))
                       ?? sc `at` (Inst @"e" (sAdd (cfold a) (cfold b)), Inst @"env" env)
                       =: interpInEnv env (sAdd (cfold a) (cfold b))
                       ?? ih `at` (Inst @"e" a, Inst @"env" env)
                       ?? ih `at` (Inst @"e" b, Inst @"env" env)
                       =: interpInEnv env (sAdd a b)
                       =: interpInEnv env e
                       =: qed

            Mul a b    -> interpInEnv env (cfold e)
                       ?? "case Mul"
                       =: interpInEnv env (cfold (sMul a b))
                       =: interpInEnv env (simplify (sMul (cfold a) (cfold b)))
                       ?? sc `at` (Inst @"e" (sMul (cfold a) (cfold b)), Inst @"env" env)
                       =: interpInEnv env (sMul (cfold a) (cfold b))
                       ?? mulH `at` (Inst @"env" env, Inst @"a" (cfold a), Inst @"b" (cfold b))
                       =: interpInEnv env (cfold a) * interpInEnv env (cfold b)
                       ?? ih `at` (Inst @"e" a, Inst @"env" env)
                       ?? mulCL `at` (Inst @"a" (interpInEnv env (cfold a)), Inst @"b" (interpInEnv env a), Inst @"c" (interpInEnv env (cfold b)))
                       =: interpInEnv env a * interpInEnv env (cfold b)
                       ?? ih `at` (Inst @"e" b, Inst @"env" env)
                       ?? mulCR `at` (Inst @"a" (interpInEnv env a), Inst @"b" (interpInEnv env (cfold b)), Inst @"c" (interpInEnv env b))
                       =: interpInEnv env a * interpInEnv env b
                       ?? mulH `at` (Inst @"env" env, Inst @"a" a, Inst @"b" b)
                       =: interpInEnv env (sMul a b)
                       =: interpInEnv env e
                       =: qed

            Let nm a b -> interpInEnv env (cfold e)
                       ?? "case Let"
                       =: interpInEnv env (cfold (sLet nm a b))
                       =: interpInEnv env (simplify (sLet nm (cfold a) (cfold b)))
                       ?? sc `at` (Inst @"e" (sLet nm (cfold a) (cfold b)), Inst @"env" env)
                       =: interpInEnv env (sLet nm (cfold a) (cfold b))
                       ?? ih `at` (Inst @"e" a, Inst @"env" env)
                       ?? ih `at` (Inst @"e" b, Inst @"env" (ST.tuple (nm, interpInEnv env a) .: env))
                       =: interpInEnv env (sLet nm a b)
                       =: interpInEnv env e
                       =: qed
          |]

{-# ANN simpCorrect  ("HLint: ignore Evaluate" :: String) #-}
{-# ANN cfoldCorrect ("HLint: ignore Evaluate" :: String) #-}
