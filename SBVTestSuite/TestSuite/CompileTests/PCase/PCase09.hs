{-# LANGUAGE QuasiQuotes #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module T where

import Expr
import Data.SBV
import Data.SBV.TP

-- Overlapping constructors: unguarded Num after guarded Num
t :: SExpr -> Proof SBool
t e = [pCase|Expr e of
        Zero         -> undefined
        Num i        -> undefined
        Num i | i .> 3 -> undefined
        Var _        -> undefined
      |]
