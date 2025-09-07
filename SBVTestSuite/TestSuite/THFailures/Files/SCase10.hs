{-# LANGUAGE QuasiQuotes #-}

module T where

import Expr
import Data.SBV

t :: SExpr -> SInteger
t e = [sCase|Expr e of
               Zero          -> 0
               Num (Num i)   -> i
               Viar s         -> ite (s .== "a") 1 2
               Add a b       -> t e + t b
               Let _   _a  b -> t b
      |]
