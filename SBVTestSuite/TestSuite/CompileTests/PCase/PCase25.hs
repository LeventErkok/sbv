{-# LANGUAGE QuasiQuotes      #-}
{-# LANGUAGE DataKinds          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeAbstractions    #-}
{-# LANGUAGE TypeApplications    #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module T where

import Expr
import Data.SBV
import Data.SBV.TP

-- Positive: nested pattern using parenthesized constructor; use matched fields
t :: TP (Proof (Forall "e" Expr -> SBool))
t = calc "t" (\(Forall @"e" (e :: SExpr)) -> e .== e) $ \e -> []
    |- [pCase|Expr e of
         Zero              -> e .== e =: qed
         Num k             -> sNum k .== sNum k =: e .== e =: qed
         Var s             -> sVar s .== sVar s =: e .== e =: qed
         Let _ (Num i) _  -> sNum i .== sNum i =: e .== e =: qed
         Let nm a       b  -> sLet nm a b .== sLet nm a b =: e .== e =: qed
         Add a b           -> sAdd a b .== sAdd a b =: e .== e =: qed
       |]
