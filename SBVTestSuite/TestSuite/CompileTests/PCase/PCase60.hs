{-# LANGUAGE QuasiQuotes       #-}
{-# LANGUAGE DataKinds         #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeAbstractions  #-}
{-# LANGUAGE TypeApplications  #-}

{-# OPTIONS_GHC -Wall -Werror -ddump-splices #-}

module T where

import Expr
import Data.SBV
import Data.SBV.TP

-- Dump test: linear processing stress test
--   - Interleaved constructors (Add / Num / Add)
--   - Nested patterns with guards
--   - Guard variables used in both guard and RHS
--   - Var with guard, then unguarded Var later
--   - Multiple guarded wildcards at the end
t :: TP (Proof (Forall "e" Expr -> SBool))
t = calc "t" (\(Forall @"e" (e :: SExpr)) -> e .== e) $ \e -> []
    |- [pCase|Expr e of
         Add (Num i) b | i .> 0  -> sAdd (sNum i) b .== sAdd (sNum i) b =: e .== e =: qed
         Num i | i .> 0           -> sNum i .== sNum i =: e .== e =: qed
         Var s | s .== literal "hey" -> sVar s .== sVar s =: e .== e =: qed
         Add a b                  -> sAdd a b .== sAdd a b =: e .== e =: qed
         Num i                    -> sNum i .== sNum i =: e .== e =: qed
         Var s                    -> sVar s .== sVar s =: e .== e =: qed
         Zero                     -> e .== e =: qed
         _ | isLet e              -> e .== e =: qed
         _                        -> e .== e =: qed
       |]
