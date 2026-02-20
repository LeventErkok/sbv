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
-- >>> import Data.SBV.TP
-- >>> :set -XTypeApplications
#endif

-- | Symbolic expression over strings and integers.
type SE = SExpr String Integer

-- | Environment over strings and integers.
type E = Env String Integer

-- * Substitution

-- | Substitute a variable with a value throughout an expression. Respects shadowing:
-- if a @Let@ rebinds the same variable, we do not substitute into its body.
subst :: SString -> SInteger -> SE -> SE
subst = smtFunction "subst" $ \nm v expr ->
  [sCase|Expr expr of
    -- Variable: Do the substitution if we hit match the name
    Var x | x .== nm -> sCon v
          | True     -> sVar x

    -- Pass down:
    Con c   -> sCon c
    Sqr a   -> sSqr (subst nm v a)
    Inc a   -> sInc (subst nm v a)
    Add a b -> sAdd (subst nm v a) (subst nm v b)
    Mul a b -> sMul (subst nm v a) (subst nm v b)

    -- Let bindings: Careful about shadowing: substitute in binding but not in body
    Let x a b | x .== nm -> sLet x (subst nm v a) b
              | True     -> sLet x (subst nm v a) (subst nm v b)
  |]

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
--   * @Let nm (Con v) body → subst nm v body@
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
    Let nm (Con v) body -> subst nm v body
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
measureNonNeg :: TP (Proof (Forall "e" (Expr String Integer) -> SBool))
measureNonNeg = inductiveLemma "measureNonNeg"
                               (\(Forall @"e" (e :: SE)) -> size e .>= 0)
                               []

-- | Substitution preserves semantics: substituting @nm -> v@ in @body@ is the same
-- as interpreting @body@ in an environment extended with @(nm, v)@.
--
-- >>> runTPWith cvc5 substCorrect
-- TODO: fill in proof output
substCorrect :: TP (Proof (Forall "body" (Expr String Integer) -> Forall "nm" String -> Forall "v" Integer -> Forall "env" [(String, Integer)] -> SBool))
substCorrect = do
   mnn <- recall "measureNonNeg" measureNonNeg

   addHelper <- lemma "addHelper"
                      (\(Forall @"env" (env :: Env String Integer)) (Forall @"a" a) (Forall @"b" b) ->
                            interpInEnv env (sAdd a b) .== interpInEnv env a + interpInEnv env b) []

   sInduct "substCorrect"
     (\(Forall @"body" (body :: SE)) (Forall @"nm" nm) (Forall @"v" v) (Forall @"env" (env :: E)) ->
                  interpInEnv env (subst nm v body) .== interpInEnv (ST.tuple (nm, v) .: env) body)
     (\body _ _ _ -> size body, [proofOf mnn]) $
     \ih body nm v env -> []
       |- cases [ isVar body ==> let x = svar body
                               in interpInEnv env (subst nm v (sVar x))
                               ?? "case Var"
                               =: interpInEnv (ST.tuple (nm, v) .: env) (ite (nm .== x) (sCon v) (sVar x))
                               =: qed

                , isCon body ==> let c = scon body
                               in interpInEnv env (subst nm v (sCon c))
                               ?? "case Con"
                               =: interpInEnv (ST.tuple (nm, v) .: env) (sCon c)
                               =: qed

                , isSqr body ==> let a = ssqrVal body
                               in interpInEnv env (subst nm v (sSqr a))
                               ?? "case Sqr"
                               ?? ih `at` (Inst @"body" a, Inst @"nm" nm, Inst @"v" v, Inst @"env" env)
                               =: interpInEnv (ST.tuple (nm, v) .: env) (sSqr a)
                               =: qed

                , isInc body ==> let a = sincVal body
                               in interpInEnv env (subst nm v (sInc a))
                               ?? "case Inc"
                               =: interpInEnv env (sInc (subst nm v a))
                               ?? ih `at` (Inst @"body" a, Inst @"nm" nm, Inst @"v" v, Inst @"env" env)
                               =: interpInEnv (ST.tuple (nm, v) .: env) (sInc a)
                               =: qed

                , isAdd body ==> let a    = sadd1 body
                                     b    = sadd2 body
                                     env' = ST.tuple (nm, v) .: env
                               in interpInEnv env (subst nm v (sAdd a b))
                               ?? "case Add"
                               =: interpInEnv env (sAdd (subst nm v a) (subst nm v b))
                               ?? addHelper `at` (Inst @"env" env, Inst @"a" (subst nm v a), Inst @"b" (subst nm v b))
                               =: interpInEnv env (subst nm v a) + interpInEnv env (subst nm v b)
                               ?? ih `at` (Inst @"body" a, Inst @"nm" nm, Inst @"v" v, Inst @"env" env)
                               ?? sorry
                               ?? "stuck"
                               =: interpInEnv env' a + interpInEnv env (subst nm v b)
                               ?? ih `at` (Inst @"body" b, Inst @"nm" nm, Inst @"v" v, Inst @"env" env)
                               ?? sorry
                               ?? "stuck"
                               =: interpInEnv env' a + interpInEnv env' b
                               ?? addHelper `at` (Inst @"env" env', Inst @"a" a, Inst @"b" b)
                               =: interpInEnv env' (sAdd a b)
                               =: interpInEnv (ST.tuple (nm, v) .: env) (sAdd a b)
                               =: qed

                , isMul body ==> let a    = smul1 body
                                     b    = smul2 body
                                     env' = ST.tuple (nm, v) .: env
                               in interpInEnv env (subst nm v (sMul a b))
                               ?? "case Add"
                               =: interpInEnv env (sMul (subst nm v a) (subst nm v b))
                               ?? addHelper `at` (Inst @"env" env, Inst @"a" (subst nm v a), Inst @"b" (subst nm v b))
                               =: interpInEnv env (subst nm v a) * interpInEnv env (subst nm v b)
                               ?? ih `at` (Inst @"body" a, Inst @"nm" nm, Inst @"v" v, Inst @"env" env)
                               ?? sorry
                               ?? "stuck"
                               =: interpInEnv env' a * interpInEnv env (subst nm v b)
                               ?? ih `at` (Inst @"body" b, Inst @"nm" nm, Inst @"v" v, Inst @"env" env)
                               ?? sorry
                               ?? "stuck"
                               =: interpInEnv env' a * interpInEnv env' b
                               ?? addHelper `at` (Inst @"env" env', Inst @"a" a, Inst @"b" b)
                               =: interpInEnv env' (sMul a b)
                               =: interpInEnv (ST.tuple (nm, v) .: env) (sMul a b)
                               =: qed

                , isLet body ==> let x = slvar  body
                                     a = slval  body
                                     b = slbody body
                               in interpInEnv env (subst nm v (sLet x a b))
                               ?? "case Let"
                               ?? ih `at` (Inst @"body" a, Inst @"nm" nm, Inst @"v" v, Inst @"env" env)
                               ?? ih `at` (Inst @"body" b, Inst @"nm" nm, Inst @"v" v,
                                           Inst @"env" (ST.tuple (x, interpInEnv (ST.tuple (nm, v) .: env) a) .: env))
                               =: interpInEnv (ST.tuple (nm, v) .: env) (sLet x a b)
                               =: qed
                ]

-- | Simplification preserves semantics.
--
-- >>> runTP simpCorrect
-- TODO: fill in proof output
simpCorrect :: TP (Proof (Forall "e" (Expr String Integer) -> Forall "env" [(String, Integer)] -> SBool))
simpCorrect = do
   sc <- recall "substCorrect" substCorrect

   lemma "simpCorrect"
         (\(Forall @"e" (e :: SE)) (Forall @"env" (env :: E))
               -> interpInEnv env (simplify e) .== interpInEnv env e)
         [proofOf sc]

-- | Constant folding preserves the semantics: interpreting an expression
-- is the same as constant-folding it first and then interpreting the result.
--
-- >>> runTP cfoldCorrect
-- TODO: fill in proof output
cfoldCorrect :: TP (Proof (Forall "e" (Expr String Integer) -> Forall "env" [(String, Integer)] -> SBool))
cfoldCorrect = do
   mnn <- recall "measureNonNeg" measureNonNeg
   sc  <- recall "simpCorrect"   simpCorrect

   sInduct "cfoldCorrect"
     (\(Forall @"e" (e :: SE)) (Forall @"env" (env :: E)) ->
                  interpInEnv env (cfold e) .== interpInEnv env e)
     (\e _ -> size e, [proofOf mnn]) $
     \ih e env -> []
       |- cases [ isVar e ==> let nm = svar e
                            in interpInEnv env (cfold (sVar nm))
                            ?? "case Var"
                            =: interpInEnv env (sVar nm)
                            =: qed

                , isCon e ==> let v = scon e
                            in interpInEnv env (cfold (sCon v))
                            ?? "case Con"
                            =: interpInEnv env (sCon v)
                            =: qed

                , isSqr e ==> let a = ssqrVal e
                            in interpInEnv env (cfold (sSqr a))
                            ?? "case Sqr"
                            =: interpInEnv env (simplify (sSqr (cfold a)))
                            ?? sc `at` (Inst @"e" (sSqr (cfold a)), Inst @"env" env)
                            =: interpInEnv env (sSqr (cfold a))
                            ?? ih `at` (Inst @"e" a, Inst @"env" env)
                            =: interpInEnv env (sSqr a)
                            =: qed

                , isInc e ==> let a = sincVal e
                            in interpInEnv env (cfold (sInc a))
                            ?? "case Inc"
                            =: interpInEnv env (simplify (sInc (cfold a)))
                            ?? sc `at` (Inst @"e" (sInc (cfold a)), Inst @"env" env)
                            =: interpInEnv env (sInc (cfold a))
                            ?? ih `at` (Inst @"e" a, Inst @"env" env)
                            =: interpInEnv env (sInc a)
                            =: qed

                , isAdd e ==> let a = sadd1 e
                                  b = sadd2 e
                            in interpInEnv env (cfold (sAdd a b))
                            ?? "case Add"
                            =: interpInEnv env (simplify (sAdd (cfold a) (cfold b)))
                            ?? sc `at` (Inst @"e" (sAdd (cfold a) (cfold b)), Inst @"env" env)
                            =: interpInEnv env (sAdd (cfold a) (cfold b))
                            ?? ih `at` (Inst @"e" a, Inst @"env" env)
                            ?? ih `at` (Inst @"e" b, Inst @"env" env)
                            =: interpInEnv env (sAdd a b)
                            =: qed

                , isMul e ==> let a = smul1 e
                                  b = smul2 e
                            in interpInEnv env (cfold (sMul a b))
                            ?? "case Mul"
                            =: interpInEnv env (simplify (sMul (cfold a) (cfold b)))
                            ?? sc `at` (Inst @"e" (sMul (cfold a) (cfold b)), Inst @"env" env)
                            =: interpInEnv env (sMul (cfold a) (cfold b))
                            ?? ih `at` (Inst @"e" a, Inst @"env" env)
                            ?? ih `at` (Inst @"e" b, Inst @"env" env)
                            =: interpInEnv env (sMul a b)
                            =: qed

                , isLet e ==> let nm = slvar  e
                                  a  = slval  e
                                  b  = slbody e
                            in interpInEnv env (cfold (sLet nm a b))
                            ?? "case Let"
                            =: interpInEnv env (simplify (sLet nm (cfold a) (cfold b)))
                            ?? sc `at` (Inst @"e" (sLet nm (cfold a) (cfold b)), Inst @"env" env)
                            =: interpInEnv env (sLet nm (cfold a) (cfold b))
                            ?? ih `at` (Inst @"e" a, Inst @"env" env)
                            ?? ih `at` (Inst @"e" b, Inst @"env" (ST.tuple (nm, interpInEnv env a) .: env))
                            =: interpInEnv env (sLet nm a b)
                            =: qed
                ]
