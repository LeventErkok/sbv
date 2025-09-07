{-# LANGUAGE QuasiQuotes #-}

module SCase05 where

import Expr
import Data.SBV

t :: SExpr -> SInteger
t e = [sCase|Expr e of
               Zero          -> 0
               Num i | Just 1 <- Just i         -> i
               Var s        -> ite (s .== "a") 1 else 2
               Add a b       -> t e + t b
               Let _   _a  b -> t b
      |]
