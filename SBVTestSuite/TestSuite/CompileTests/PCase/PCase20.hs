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

-- Positive: {} wildcard patterns; use matched field where available
t :: TP (Proof (Forall "e" Expr -> SBool))
t = calc "t" (\(Forall @"e" (e :: SExpr)) -> e .== e) $ \e -> []
    |- [pCase|Expr e of
         Num i | i .> 3  -> sNum i .== sNum i =: e .== e =: qed
               | sTrue   -> sNum i .== sNum i =: e .== e =: qed
         Zero{}           -> e .== e =: qed
         Var{}            -> e .== e =: qed
         Add{}            -> e .== e =: qed
         Let{}            -> e .== e =: qed
       |]
