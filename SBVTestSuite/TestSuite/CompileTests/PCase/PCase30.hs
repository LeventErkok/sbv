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

-- Positive: Num 1 as only Num arm, no fallback — fine in pCase (no exhaustiveness check)
t :: TP (Proof (Forall "e" Expr -> SBool))
t = calc "t" (\(Forall @"e" (e :: SExpr)) -> e .== e) $ \e -> []
    |- [pCase|Expr e of
         Zero      -> e .== e =: qed
         Num 1     -> sNum 1 .== sNum 1 =: e .== e =: qed
         Var s     -> sVar s .== sVar s =: e .== e =: qed
         Add _ _   -> e .== e =: qed
         Let _ _ _ -> e .== e =: qed
       |]
