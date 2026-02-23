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

-- Negative: pCase generates cases [...] which has type TPProofRaw, not Proof SBool;
-- so using pCase outside a TP proof context is a type error
t :: SExpr -> Proof SBool
t e = [pCase|Expr e of
       Zero      -> e .== e =: qed
       Num _     -> e .== e =: qed
       Var _     -> e .== e =: qed
       Add _ _   -> e .== e =: qed
       Let _ _ _ -> e .== e =: qed
     |]
