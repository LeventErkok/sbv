-----------------------------------------------------------------------------
-- |
-- Module    : Documentation.SBV.Examples.TP.VM
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Correctness of a simple interpreter vs virtual-machine interpretation of a language.
-----------------------------------------------------------------------------

{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE FlexibleInstances   #-}
{-# LANGUAGE OverloadedLists     #-}
{-# LANGUAGE QuasiQuotes         #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell     #-}
{-# LANGUAGE TypeApplications    #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module Documentation.SBV.Examples.TP.VM where

import Data.SBV
import Data.SBV.Tuple as ST
import Data.SBV.List  as SL

import Data.SBV.TP

-- * Language

-- | Basic expression language.
data Expr nm val = Var nm                             -- ^ Variables
                 | Con val                            -- ^ Constants
                 | Sqr (Expr nm val)                  -- ^ Squaring
                 | Inc (Expr nm val)                  -- ^ Increment
                 | Add (Expr nm val) (Expr nm val)    -- ^ Addition
                 | Mul (Expr nm val) (Expr nm val)    -- ^ Multiplication
                 | Let nm (Expr nm val) (Expr nm val) -- ^ Let expression

-- | Create symbolic version of expressions
mkSymbolic [''Expr]

-- | Size of an expression. Used in strong induction.
size :: (SymVal nm, SymVal val) => SExpr nm val -> SInteger
size = smtFunction "exprSize" $ \expr -> [sCase|Expr expr of
                                            Var _     -> 0
                                            Con _     -> 0
                                            Sqr a     -> 1 + size a
                                            Inc a     -> 1 + size a
                                            Add a b   -> 1 + size a `smax` size b
                                            Mul a b   -> 1 + size a `smax` size b
                                            Let _ a b -> 1 + size a `smax` size b
                                         |]

-- | Environment, binding names to values
type Env nm val = SList (nm, val)

-- * Functional interpretation

-- | Interpreter, in the usual functional style, taking an arbitrary environment.
interpInEnv :: (SymVal nm, SymVal val, Num (SBV val)) => Env nm val -> SExpr nm val -> SBV val
interpInEnv = smtFunction "interpInEnv" $ \env expr ->
                 [sCase|Expr expr of
                    Var nm    -> nm `SL.lookup` env
                    Con v     -> v
                    Sqr a     -> let av = interpInEnv env a in av * av
                    Inc a     -> let av = interpInEnv env a in av + 1
                    Add a b   -> let av = interpInEnv env a; bv = interpInEnv env b in av + bv
                    Mul a b   -> let av = interpInEnv env a; bv = interpInEnv env b in av * bv
                    Let v a b -> let av = interpInEnv env a in interpInEnv (tuple (v, av) .: env) b
                 |]

-- | Interpret starting from empty environment.
interp :: (SymVal nm, SymVal val, Num (SBV val)) => SExpr nm val -> SBV val
interp = interpInEnv []

-- * Virtual machine

-- | Instructions
data Instr nm val = IPushN nm   -- ^ Push the value of nm from the environment on to the stack
                  | IPushV val  -- ^ Push a value on to the stack
                  | IDup        -- ^ Duplicate the top of the stack
                  | IAdd        -- ^ Add      the top two elements and push back
                  | IMul        -- ^ Multiply the top two elements and push back
                  | IBind nm    -- ^ Bind the value on top of stack to name
                  | IForget     -- ^ Pop and ignore the binding on the environment

-- | Create symbolic version of instructions
mkSymbolic [''Instr]

-- | Stack of values.
type Stack val = SList val

-- | Pushing on to the stack.
push :: SymVal val => SBV val -> Stack val  -> Stack val
push = (SL..:)

-- | Top of the stack. If the stack is empty, the result is underspecified.
top :: SymVal val => Stack val  -> SBV val
top = SL.head

-- | Popping from the stack. If the stack is empty, the result is underspecified.
pop :: SymVal val => Stack val  -> Stack val
pop = SL.tail

-- | A pair containing an environment and a stack
type EnvStack nm val = SBV ([(nm, val)], [val])

-- | Executing a single instruction in a given environment and the instruction stack.
-- We produce the new environment, and the new stack.
execute :: (SymVal nm, SymVal val, Num (SBV val)) => EnvStack nm val -> SInstr nm val -> EnvStack nm val
execute envStk instr = let (env, stk) = untuple envStk
                       in tuple $ [sCase|Instr instr of
                                     IPushN nm   -> (env, push (nm `SL.lookup` env) stk)
                                     IPushV val  -> (env, push val stk)
                                     IDup        -> (env, push (top stk) stk)
                                     IAdd        -> (env, let a = top stk; b = top (pop stk) in push (a + b) (pop (pop stk)))
                                     IMul        -> (env, let a = top stk; b = top (pop stk) in push (a * b) (pop (pop stk)))
                                     IBind nm    -> (push (tuple (nm, top stk)) env, pop stk)
                                     IForget     -> (pop env, stk)
                                  |]

-- | Execute a sequence of instructions, in a given stack and env. Returnsg the final environment and the stack. This is a
-- simple fold-left.
run :: (SymVal nm, SymVal val, Num (SBV val)) => EnvStack nm val -> SList (Instr nm val) -> EnvStack nm val
run = SL.foldl execute

-- * Compiler

-- | Convert an expression to a sequence of instructions for our virtual machine.
compile :: (SymVal nm, SymVal val, Num (SBV val)) => SExpr nm val -> SList (Instr nm val)
compile = smtFunction "compile" $ \expr ->
                [sCase|Expr expr of
                   Var nm    -> [sIPushN nm]
                   Con v     -> [sIPushV v]
                   Sqr a     -> compile a SL.++ [sIDup,     sIMul]
                   Inc a     -> compile a SL.++ [sIPushV 1, sIAdd]
                   Add a b   -> compile a SL.++ compile b  SL.++ [sIAdd]
                   Mul a b   -> compile a SL.++ compile b  SL.++ [sIMul]
                   Let v a b -> compile a SL.++ [sIBind v] SL.++ compile b SL.++ [sIForget]
                |]

-- | Compile and run an expression.
compileAndRun :: (SymVal nm, SymVal val, Num (SBV val)) => SExpr nm val -> SBV val
compileAndRun = top . ST.snd . run (tuple ([], [])) . compile

-- * Correctness

-- | The property we're after is that interpreting an expression is the same as
-- first compiling it to virtual-machine instructions, and then running them.
--
-- >>> correctness @String @Integer
correctness :: forall nm val. (SymVal nm, SymVal val, Num (SBV val)) => IO (Proof (Forall "expr" (Expr nm val) -> SBool))
correctness = runTP $ do

   -- Running a sequence of instructions that are appended is equivalent to running them in sequence:
   runSeq <- induct "runSeq"
                    (\(Forall @"xs" xs) (Forall @"ys" ys) (Forall @"es" (es :: EnvStack nm val))
                         -> run es (xs SL.++ ys) .== run (run es xs) ys) $
                    \ih (x, xs) ys es -> [] |- run es ((x .: xs) SL.++ ys)
                                            =: run es (x .: (xs SL.++ ys))
                                            =: run (execute es x) (xs SL.++ ys)
                                            ?? ih `at` (Inst @"ys" ys, Inst @"es" (execute es x))
                                            =: run (run es (x .: xs)) ys
                                            =: qed

   -- Running one instruction is equal to just executing it
   runOne <- lemma "runOne"
                   (\(Forall @"es" (es :: EnvStack nm val)) (Forall @"i" i) -> run es [i] .== execute es i)
                   []

   -- We will use the size of the expression as the measure. We need to show that it is
   -- always positive for the inductive proof to go thru.
   measureNonNeg <- inductiveLemma "measureNonNeg"
                                   (\(Forall @"e" (e :: SExpr nm val)) -> size e .>= 0)
                                   []

   -- A more general version of the theorem, starting with an arbitrary env and stack.
   -- We prove this using the induction principle for expressions.
   helper <- sInductWith cvc5 "helper"
               (\(Forall @"e" e) (Forall @"env" (env :: Env nm val)) (Forall @"stk" stk) ->
                             run (tuple (env, stk)) (compile e)
                         .== tuple (env, push (interpInEnv env e) stk))
               (\e _ _  -> size e) $
               \ih e env stk -> [assumptionFromProof measureNonNeg]
                 |- cases [ isVar e ==> let nm = getVar_1 e
                                     in run (tuple (env, stk)) (compile (sVar nm))
                                     ?? "case Var"
                                     =: run (tuple (env, stk)) [sIPushN nm]
                                     =: tuple (env, push (interpInEnv env (sVar nm)) stk)
                                     =: qed

                          , isCon e ==> let v = getCon_1 e
                                     in run (tuple (env, stk)) (compile (sCon v))
                                     ?? "case Con"
                                     =: run (tuple (env, stk)) [sIPushV v]
                                     =: tuple (env, push v stk)
                                     =: tuple (env, push (interpInEnv env (sCon v)) stk)
                                     =: qed

                          , isSqr e ==> let a = getSqr_1 e
                                     in run (tuple (env, stk)) (compile (sSqr a))
                                     ?? "case Sqr"
                                     =: run (tuple (env, stk)) (compile a SL.++ [sIDup, sIMul])
                                     ?? runSeq
                                     =: run (run (tuple (env, stk)) (compile a)) [sIDup, sIMul]
                                     ?? ih `at` (Inst @"e" a, Inst @"env" env, Inst @"stk" stk)
                                     =: let stk' = push (interpInEnv env a) stk
                                     in run (tuple (env, stk')) [sIDup, sIMul]
                                     ?? runSeq
                                     =: execute (execute (tuple (env, stk')) sIDup) sIMul
                                     =: let stk'' = push (interpInEnv env a) stk'
                                     in execute (tuple (env, stk'')) sIMul
                                     =: tuple (env, push (interpInEnv env a * interpInEnv env a) stk)
                                     =: tuple (env, push (interpInEnv env (sSqr a)) stk)
                                     =: qed

                          , isInc e ==> let a = getInc_1 e
                                     in run (tuple (env, stk)) (compile (sInc a))
                                     ?? "case Inc"
                                     =: run (tuple (env, stk)) (compile a SL.++ [sIPushV 1, sIAdd])
                                     ?? runSeq
                                     =: run (run (tuple (env, stk)) (compile a)) [sIPushV 1, sIAdd]
                                     ?? ih `at` (Inst @"e" a, Inst @"env" env, Inst @"stk" stk)
                                     =: run (tuple (env, push (interpInEnv env a) stk)) [sIPushV 1, sIAdd]
                                     =: tuple (env, push (interpInEnv env (sInc a)) stk)
                                     =: qed

                          , isAdd e ==> let a = getAdd_1 e
                                            b = getAdd_2 e
                                     in run (tuple (env, stk)) (compile (sAdd a b))
                                     ?? "case sAdd"
                                     =: run (tuple (env, stk)) (compile a SL.++ compile b SL.++ [sIAdd])
                                     ?? runSeq
                                     =: run (run (tuple (env, stk)) (compile a)) (compile b SL.++ [sIAdd])
                                     ?? ih `at` (Inst @"e" a, Inst @"env" env, Inst @"stk" stk)
                                     =: let stk' = push (interpInEnv env a) stk
                                     in run (tuple (env, stk')) (compile b SL.++ [sIAdd])
                                     ?? runSeq
                                     =: run (run (tuple (env, stk')) (compile b)) [sIAdd]
                                     ?? ih `at` (Inst @"e" b, Inst @"env" env, Inst @"stk" stk')
                                     =: let stk'' = push (interpInEnv env b) stk'
                                     in run (tuple (env, stk'')) [sIAdd]
                                     =: execute (tuple (env, stk'')) sIAdd
                                     =: tuple (env, push (interpInEnv env b + interpInEnv env a) stk)
                                     =: tuple (env, push (interpInEnv env a + interpInEnv env b) stk)
                                     =: tuple (env, push (interpInEnv env (sAdd a b)) stk)
                                     =: qed

                          , isMul e ==> let a = getMul_1 e
                                            b = getMul_2 e
                                     in run (tuple (env, stk)) (compile (sMul a b))
                                     ?? "case sMul"
                                     =: run (tuple (env, stk)) (compile a SL.++ compile b SL.++ [sIMul])
                                     ?? runSeq
                                     =: run (run (tuple (env, stk)) (compile a)) (compile b SL.++ [sIMul])
                                     ?? ih `at` (Inst @"e" a, Inst @"env" env, Inst @"stk" stk)
                                     =: let stk' = push (interpInEnv env a) stk
                                     in run (tuple (env, stk')) (compile b SL.++ [sIMul])
                                     ?? runSeq
                                     =: run (run (tuple (env, stk')) (compile b)) [sIMul]
                                     ?? ih `at` (Inst @"e" b, Inst @"env" env, Inst @"stk" stk')
                                     =: let stk'' = push (interpInEnv env b) stk'
                                     in run (tuple (env, stk'')) [sIMul]
                                     ?? runOne `at` (Inst @"es" (tuple (env, stk'')), Inst @"i" sIMul)
                                     =: execute (tuple (env, stk'')) sIMul
                                     =: tuple (env, push (interpInEnv env b * interpInEnv env a) stk)
                                     =: tuple (env, push (interpInEnv env a * interpInEnv env b) stk)
                                     =: tuple (env, push (interpInEnv env (sMul a b)) stk)
                                     =: qed

                          , isLet e ==> let nm = getLet_1 e
                                            a  = getLet_2 e
                                            b  = getLet_3 e
                                     in run (tuple (env, stk)) (compile (sLet nm a b))
                                     ?? "case Let"
                                     =: run (tuple (env, stk)) (compile a SL.++ [sIBind nm] SL.++ compile b SL.++ [sIForget])
                                     ?? runSeq
                                     =: run (run (tuple (env, stk)) (compile a)) ([sIBind nm] SL.++ compile b SL.++ [sIForget])
                                     ?? ih `at` (Inst @"e" a, Inst @"env" env, Inst @"stk" stk)
                                     =: let stk' = push (interpInEnv env a) stk
                                     in run (tuple (env, stk')) ([sIBind nm] SL.++ compile b SL.++ [sIForget])
                                     ?? runSeq
                                     =: run (run (tuple (env, stk')) [sIBind nm]) (compile b SL.++ [sIForget])
                                     ?? runOne
                                     =: run (execute (tuple (env, stk')) (sIBind nm)) (compile b SL.++ [sIForget])
                                     =: let env' = push (tuple (nm, interpInEnv env a)) env
                                     in run (tuple (env', stk)) (compile b SL.++ [sIForget])
                                     ?? runSeq
                                     =: run (run (tuple (env', stk)) (compile b)) [sIForget]
                                     ?? ih `at` (Inst @"e" b, Inst @"env" env', Inst @"stk" stk)
                                     =: let stk'' = push (interpInEnv env' b) stk
                                     in run (tuple (env', stk'')) [sIForget]
                                     =: tuple (env, push (interpInEnv env (sLet nm a b)) stk)
                                     =: qed
                          ]

   -- We can now prove the final correctness theorem, based on the helper.
   calc "correctness"
        (\(Forall @"expr" (e :: SExpr nm val)) -> compileAndRun e .== interp e) $
        \(e :: SExpr nm val) -> [] |- compileAndRun e
                                   =: top (ST.snd (run (tuple ([], [])) (compile e)))
                                   ?? helper `at` (Inst @"e" e, Inst @"env" [], Inst @"stk" [])
                                   =: top (ST.snd (tuple ([] :: Env nm val, push (interpInEnv [] e) [])))
                                   =: interpInEnv [] e
                                   =: interp e
                                   =: qed
