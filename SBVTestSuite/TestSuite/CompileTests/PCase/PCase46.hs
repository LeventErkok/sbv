{-# LANGUAGE QuasiQuotes       #-}
{-# LANGUAGE DataKinds         #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeAbstractions  #-}
{-# LANGUAGE TypeApplications  #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module T where

import Expr
import Data.SBV
import Data.SBV.TP

-- Negative: bound variables a, b from Add are not used in the RHS
t :: TP (Proof (Forall "e" Expr -> SBool))
t = calc "t" (\(Forall @"e" (e :: SExpr)) -> e .== e) $ \e -> []
    |- [pCase|Expr e of
         Zero      -> e .== e =: qed
         Num i     -> sNum i .== sNum i =: e .== e =: qed
         Var s     -> sVar s .== sVar s =: e .== e =: qed
         Add a b   -> e .== e =: qed
         Let nm a b -> sLet nm a b .== sLet nm a b =: e .== e =: qed
       |]
