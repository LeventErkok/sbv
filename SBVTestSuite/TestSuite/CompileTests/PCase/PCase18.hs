{-# LANGUAGE QuasiQuotes #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module T where

import Expr
import Data.SBV
import Data.SBV.TP

-- Negative: wildcard with args (e.g. _ _ ->)
t :: SExpr -> Proof SBool
t e = [pCase|Expr e of
        Zero    -> undefined
        Num _   -> undefined
        Var _   -> undefined
        Add _ _ -> undefined
        _ _     -> undefined
      |]
