{-# LANGUAGE QuasiQuotes #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module T where

import Expr
import Data.SBV

-- Negative: nested constructor with wrong arity (Num takes 1 arg, given 2)
t :: SExpr -> SInteger
t e = [sCase|Expr e of
               Zero              -> 0
               Num k             -> k
               Var s             -> ite (s .== literal "a") 1 2
               Add (Num i j) b   -> i + t b
               Add a b           -> t a + t b
               Let _   _a  b     -> t b
      |]
