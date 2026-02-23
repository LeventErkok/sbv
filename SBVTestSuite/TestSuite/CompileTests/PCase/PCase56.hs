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

-- Dump test: guarded wildcard + nested pattern on a constructor
t :: TP (Proof (Forall "e" Expr -> SBool))
t = calc "t" (\(Forall @"e" (e :: SExpr)) -> e .== e) $ \e -> []
    |- [pCase|Expr e of
         Add (Num i) _ | i .> 0  -> e .== e =: qed
         Add _ _                  -> e .== e =: qed
         _ | isZero e             -> e .== e =: qed
           | sTrue                -> e .== e =: qed
       |]
