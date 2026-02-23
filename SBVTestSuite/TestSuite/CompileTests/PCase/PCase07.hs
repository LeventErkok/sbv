{-# LANGUAGE QuasiQuotes #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module T where

import Expr
import Data.SBV
import Data.SBV.TP

-- Arity mismatch: Num takes 1 arg, given 2
t :: SExpr -> Proof SBool
t e = [pCase|Expr e of
        Zero     -> undefined
        Num _ _  -> undefined
        Var _    -> undefined
        Add _ _  -> undefined
        Let _ _ _ -> undefined
      |]
