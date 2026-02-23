{-# LANGUAGE QuasiQuotes #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module T where

import Expr
import Data.SBV
import Data.SBV.TP

-- Pattern guards not supported
t :: SExpr -> Proof SBool
t e = [pCase|Expr e of
        Zero        -> undefined
        Num i | Just 1 <- Just i -> undefined
        Var _       -> undefined
      |]
