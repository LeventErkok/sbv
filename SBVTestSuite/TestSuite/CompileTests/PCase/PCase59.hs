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

-- Dump test: interleaved constructors (Let/Add/Let), linear processing
t :: TP (Proof (Forall "e" Expr -> SBool))
t = calc "t" (\(Forall @"e" (e :: SExpr)) -> e .== e) $ \e -> []
    |- [pCase|Expr e of
         Let s a b | isZero a -> sLet s a b .== sLet s a b =: e .== e =: qed
         Add a b              -> sAdd a b .== sAdd a b =: e .== e =: qed
         Let s a b            -> sLet s a b .== sLet s a b =: e .== e =: qed
         Zero                 -> e .== e =: qed
         Num _                -> e .== e =: qed
         Var _                -> e .== e =: qed
       |]
