{-# LANGUAGE QuasiQuotes #-}

module T where

import Expr
import Data.SBV

t :: SExpr -> SInteger
t e = [sCase|Expr e of
        Zero  -> 0
        Num i -> i
      |]
