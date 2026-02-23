{-# LANGUAGE QuasiQuotes #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module T where

import Expr
import Data.SBV
import Data.SBV.TP

-- Arity mismatch in nested pattern: Num takes 1, given 2
t :: SExpr -> Proof SBool
t e = [pCase|Expr e of
        Zero            -> undefined
        Num k           -> undefined
        Var _           -> undefined
        Add (Num i j) b -> undefined
        Let _ _ _       -> undefined
      |]
