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

-- Negative: all constructors covered + guarded wildcard with ambiguous type in guard (2 .>= 3)
t :: TP (Proof (Forall "e" Expr -> SBool))
t = calc "t" (\(Forall @"e" (e :: SExpr)) -> e .== e) $ \e -> []
    |- [pCase|Expr e of
       Zero           -> e .== e =: qed
       Num i          -> sNum i .== sNum i =: e .== e =: qed
       Var _          -> e .== e =: qed
       Add _ _        -> e .== e =: qed
       Let _ _ _      -> e .== e =: qed
       _ | 2 .>= 3   -> e .== e =: qed
     |]
