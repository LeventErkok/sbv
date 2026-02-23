{-# LANGUAGE QuasiQuotes       #-}
{-# LANGUAGE DataKinds         #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeAbstractions  #-}
{-# LANGUAGE TypeApplications  #-}

{-# OPTIONS_GHC -Wall -Werror -ddump-splices #-}

module T where

import Expr
import Data.SBV
import Data.SBV.TP

-- Dump test: simple unguarded, all constructors
t :: TP (Proof (Forall "e" Expr -> SBool))
t = calc "t" (\(Forall @"e" (e :: SExpr)) -> e .== e) $ \e -> []
    |- [pCase|Expr e of
         Zero      -> e .== e =: qed
         Num _     -> e .== e =: qed
         Var _     -> e .== e =: qed
         Add _ _   -> e .== e =: qed
         Let _ _ _ -> e .== e =: qed
       |]
