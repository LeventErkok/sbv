{-# LANGUAGE QuasiQuotes #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module T where

import Expr
import Data.SBV

t :: SExpr -> SInteger
t e = [sCase|Expr e of
               Zero           -> 0
               Num i -> 4
               Num i | i .< 3 -> i
               Var s          -> ite (s .== literal "a") 1 2
               Add a b        -> t e + t b
               Let _   _a  b  -> t b
      |]
