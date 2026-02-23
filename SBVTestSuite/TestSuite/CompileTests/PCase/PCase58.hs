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

-- Dump test: multiple guarded arms on nested pattern, variable in guard + RHS, wildcard
t :: TP (Proof (Forall "e" Expr -> SBool))
t = calc "t" (\(Forall @"e" (e :: SExpr)) -> e .== e) $ \e -> []
    |- [pCase|Expr e of
         Let s (Num i) b | i .> 0   -> sLet s (sNum i) b .== sLet s (sNum i) b =: e .== e =: qed
                          | i .> -5  -> sLet s (sNum i) b .== sLet s (sNum i) b =: e .== e =: qed
                          | sTrue    -> sLet s (sNum i) b .== sLet s (sNum i) b =: e .== e =: qed
         Let s a b                   -> sLet s a b .== sLet s a b =: e .== e =: qed
         Add (Num i) (Num j)         -> sAdd (sNum i) (sNum j) .== sAdd (sNum i) (sNum j) =: e .== e =: qed
         _                           -> e .== e =: qed
       |]
