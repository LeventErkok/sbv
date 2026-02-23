{-# LANGUAGE QuasiQuotes #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module T where

import Expr
import Data.SBV
import Data.SBV.TP

-- Negative: wildcard catch-all after guarded Add arm
-- (sCase accepts this; pCase rejects the wildcard)
t :: SExpr -> Proof SBool
t e = [pCase|Expr e of
        Zero           -> undefined
        Num _          -> undefined
        Var _          -> undefined
        Add a b | t a .== undefined -> undefined
        Let _ _ _      -> undefined
        _              -> undefined
      |]
