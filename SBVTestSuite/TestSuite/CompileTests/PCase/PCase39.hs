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

-- Positive: nested pattern covers only a subset of Add, no fallback
-- (sCase rejects as non-exhaustive; pCase is fine)
t :: TP (Proof (Forall "e" Expr -> SBool))
t = calc "t" (\(Forall @"e" (e :: SExpr)) -> e .== e) $ \e -> []
    |- [pCase|Expr e of
         Zero          -> e .== e =: qed
         Num k         -> sNum k .== sNum k =: e .== e =: qed
         Var s         -> sVar s .== sVar s =: e .== e =: qed
         Add (Num i) _ -> sNum i .== sNum i =: e .== e =: qed
         Let nm a b    -> sLet nm a b .== sLet nm a b =: e .== e =: qed
       |]
