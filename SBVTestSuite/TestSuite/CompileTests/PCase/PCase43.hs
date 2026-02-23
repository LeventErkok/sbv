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

-- Positive: guarded constructor without full coverage (exhaustiveness deferred to proof time)
t :: TP (Proof (Forall "e" Expr -> SBool))
t = calc "t" (\(Forall @"e" (e :: SExpr)) -> e .== e) $ \e -> []
    |- [pCase|Expr e of
         Zero              -> e .== e =: qed
         Num _             -> e .== e =: qed
         Var _             -> e .== e =: qed
         Add a _ | isZero a -> e .== e =: qed
         Let _ _ _         -> e .== e =: qed
       |]
