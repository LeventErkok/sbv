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

-- Positive: wildcard catch-all after multi-arm guarded Var and Num
t :: TP (Proof (Forall "e" Expr -> SBool))
t = calc "t" (\(Forall @"e" (e :: SExpr)) -> e .== e) $ \e -> []
    |- [pCase|Expr e of
         Var s | s .== literal "a"                       -> e .== e =: qed
               | s .== literal "b" .|| s .== literal "c" -> e .== e =: qed
               | sTrue                                    -> e .== e =: qed

         Num _ | sTrue                                    -> e .== e =: qed

         _                                                -> e .== e =: qed
       |]
