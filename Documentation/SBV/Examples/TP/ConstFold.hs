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
    _                   -> expr
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

-- | Simplification preserves semantics.
--
-- >>> runTPWith cvc5 simpCorrect
-- Lemma: sqrCong                          Q.E.D.
-- Lemma: sqrHelper                        Q.E.D.
-- Lemma: addHelper                        Q.E.D.
-- Lemma: mulCongL                         Q.E.D.
-- Lemma: mulCongR                         Q.E.D.
-- Lemma: mulHelper                        Q.E.D.
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
--     Step: 1.7.2                         Q.E.D.
--     Step: 1.7.3                         Q.E.D.
--     Step: 1.Completeness                Q.E.D.
--   Result:                               Q.E.D.
-- [Proven] simpCorrect :: Ɐe ∷ (Expr [Char] Integer) → Ɐenv ∷ [([Char], Integer)] → Bool
simpCorrect :: TP (Proof (Forall "e" Exp -> Forall "env" EL -> SBool))
simpCorrect = do
   sqrC <- recall "sqrCong"   sqrCong
   sqrH <- recall "sqrHelper" sqrHelper
   addH <- recall "addHelper" addHelper
   mulCL <- recall "mulCongL" mulCongL
   mulCR <- recall "mulCongR" mulCongR
   mulH <- recall "mulHelper" mulHelper

   calc "simpCorrect"
     (\(Forall @"e" (e :: SE)) (Forall @"env" (env :: E)) -> interpInEnv env (simplify e) .== interpInEnv env e) $
     \e env -> []
     |- cases [ isVar e
                ==> interpInEnv env (simplify e)
                 ?? "Var"
                 =: let nm = svar e
                 in interpInEnv env (simplify (sVar nm))
                 =: interpInEnv env (sVar nm)
                 =: interpInEnv env e
                 =: qed

              , isCon e
                ==> interpInEnv env (simplify e)
                 ?? "Con"
                 =: let c = scon e
                 in interpInEnv env (simplify (sCon c))
                 =: interpInEnv env (sCon c)
                 =: interpInEnv env e
                 =: qed

              , isSqr e
                ==> interpInEnv env (simplify e)
                 ?? "Sqr"
                 =: let a = ssqrVal e
                 in interpInEnv env (simplify (sSqr a))
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

              , isInc e
                ==> interpInEnv env (simplify e)
                 ?? "Inc"
                 =: let a = sincVal e
                 in interpInEnv env (simplify (sInc a))
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

              , isAdd e
                ==> interpInEnv env (simplify e)
                 ?? "Add"
                 =: let a = sadd1 e
                        b = sadd2 e
                 in interpInEnv env (simplify (sAdd a b))
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

              , isMul e
                ==> interpInEnv env (simplify e)
                 ?? "Mul"
                 =: let a = smul1 e
                        b = smul2 e
                 in interpInEnv env (simplify (sMul a b))
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

              , isLet e
                ==> interpInEnv env (simplify e)
                 ?? "Let"
                 =: let nm = slvar e
                        a  = slval e
                        b  = slbody e
                 in interpInEnv env (simplify (sLet nm a b))
                 =: interpInEnv env (sLet nm a b)
                 =: interpInEnv env e
                 =: qed
              ]

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
       |- cases [ isVar e
                  ==> interpInEnv env (cfold e)
                   ?? "case Var"
                   =: let nm = svar e
                   in interpInEnv env (cfold (sVar nm))
                   =: interpInEnv env (sVar nm)
                   =: interpInEnv env e
                   =: qed

                , isCon e
                  ==> interpInEnv env (cfold e)
                   ?? "case Con"
                   =: let v = scon e
                   in interpInEnv env (cfold (sCon v))
                   =: interpInEnv env (sCon v)
                   =: interpInEnv env e
                   =: qed

                , isSqr e
                  ==> interpInEnv env (cfold e)
                   ?? "case Sqr"
                   =: let a = ssqrVal e
                   in interpInEnv env (cfold (sSqr a))
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

                , isInc e
                  ==> interpInEnv env (cfold e)
                   ?? "case Inc"
                   =: let a = sincVal e
                   in interpInEnv env (cfold (sInc a))
                   =: interpInEnv env (simplify (sInc (cfold a)))
                   ?? sc `at` (Inst @"e" (sInc (cfold a)), Inst @"env" env)
                   =: interpInEnv env (sInc (cfold a))
                   ?? ih `at` (Inst @"e" a, Inst @"env" env)
                   =: interpInEnv env (sInc a)
                   =: interpInEnv env e
                   =: qed

                , isAdd e
                  ==> interpInEnv env (cfold e)
                   ?? "case Add"
                   =: let a = sadd1 e
                          b = sadd2 e
                   in interpInEnv env (cfold (sAdd a b))
                   =: interpInEnv env (simplify (sAdd (cfold a) (cfold b)))
                   ?? sc `at` (Inst @"e" (sAdd (cfold a) (cfold b)), Inst @"env" env)
                   =: interpInEnv env (sAdd (cfold a) (cfold b))
                   ?? ih `at` (Inst @"e" a, Inst @"env" env)
                   ?? ih `at` (Inst @"e" b, Inst @"env" env)
                   =: interpInEnv env (sAdd a b)
                   =: interpInEnv env e
                   =: qed

                , isMul e
                  ==> interpInEnv env (cfold e)
                   ?? "case Mul"
                   =: let a = smul1 e
                          b = smul2 e
                   in interpInEnv env (cfold (sMul a b))
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

                , isLet e
                  ==> interpInEnv env (cfold e)
                   ?? "case Let"
                   =: let nm = slvar  e
                          a  = slval  e
                          b  = slbody e
                   in interpInEnv env (cfold (sLet nm a b))
                   =: interpInEnv env (simplify (sLet nm (cfold a) (cfold b)))
                   ?? sc `at` (Inst @"e" (sLet nm (cfold a) (cfold b)), Inst @"env" env)
                   =: interpInEnv env (sLet nm (cfold a) (cfold b))
                   ?? ih `at` (Inst @"e" a, Inst @"env" env)
                   ?? ih `at` (Inst @"e" b, Inst @"env" (ST.tuple (nm, interpInEnv env a) .: env))
                   =: interpInEnv env (sLet nm a b)
                   =: interpInEnv env e
                   =: qed
                ]
