{-# LANGUAGE QuasiQuotes #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module T where

import Expr
import Data.SBV
import Data.SBV.TP

-- Wildcard not allowed in pCase
t :: SExpr -> Proof SBool
t e = [pCase|Expr e of
        Zero  -> undefined
        Num _ -> undefined
        _     -> undefined
      |]
