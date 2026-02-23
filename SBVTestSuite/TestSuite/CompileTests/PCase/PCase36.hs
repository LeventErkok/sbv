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

-- Negative: guarded wildcard at end — wildcards not allowed even if guarded
-- (sCase rejects: guarded wildcard might fail; pCase rejects: wildcards not allowed)
t :: TP (Proof (Forall "e" Expr -> SBool))
t = calc "t" (\(Forall @"e" (e :: SExpr)) -> e .== e) $ \e -> []
    |- [pCase|Expr e of
       Zero           -> e .== e =: qed
       Num _          -> e .== e =: qed
       Var _          -> e .== e =: qed
       Add _ _        -> e .== e =: qed
       Let _ _ _      -> e .== e =: qed
       _ | 2 .>= 3   -> e .== e =: qed
     |]
