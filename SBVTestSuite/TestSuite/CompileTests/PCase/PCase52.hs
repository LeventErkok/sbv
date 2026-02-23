{-# LANGUAGE QuasiQuotes #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module T where

import Expr
import Data.SBV
import Data.SBV.TP

-- Negative: guarded wildcard before explicit constructor matches
t :: SExpr -> Proof SBool
t e = [pCase|Expr e of
        Zero       -> undefined
        _ | sTrue  -> undefined
        Num _      -> undefined
      |]
