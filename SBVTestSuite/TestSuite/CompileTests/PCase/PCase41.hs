{-# LANGUAGE QuasiQuotes #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module T where

import Expr
import Data.SBV
import Data.SBV.TP

-- Negative: parse error (else keyword in wrong position)
t :: SExpr -> Proof SBool
t e = [pCase|Expr e of
        Zero  -> undefined
        Var s -> ite (s .== "a") undefined else undefined
        Num _ -> undefined
      |]
