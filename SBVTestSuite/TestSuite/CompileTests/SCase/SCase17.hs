{-# LANGUAGE QuasiQuotes #-}

module T where

import Expr
import Data.SBV

t :: SExpr -> SInteger
t e = [sCase|Expr e of
               Zero           -> 0
               Num i | i .< 3 -> i
               Var s          -> ite (s .== literal "a") 1 2
               Add a b        -> t e + t b
               Num i          -> i+1
               Let _   _a  b  -> t b
      |]
