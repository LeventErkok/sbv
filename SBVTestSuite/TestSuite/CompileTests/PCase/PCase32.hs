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

-- Positive: only 2 of 5 constructors covered, including a guarded one
-- (sCase would reject this as non-exhaustive; pCase is fine)
t :: TP (Proof (Forall "e" Expr -> SBool))
t = calc "t" (\(Forall @"e" (e :: SExpr)) -> e .== e) $ \e -> []
    |- [pCase|Expr e of
         Zero           -> e .== e =: qed
         Num i | i .> 0 -> sNum i .== sNum i =: e .== e =: qed
         Var s          -> sVar s .== sVar s =: e .== e =: qed
       |]
