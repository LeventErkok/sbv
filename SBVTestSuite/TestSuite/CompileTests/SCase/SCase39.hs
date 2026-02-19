{-# LANGUAGE QuasiQuotes #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module T where

import Expr
import Data.SBV

-- Negative: nested constructor that is not in scope
t :: SExpr -> SInteger
t e = [sCase|Expr e of
               Zero              -> 0
               Num k             -> k
               Var s             -> ite (s .== literal "a") 1 2
               Add (Numb i) b    -> i + t b
               Add a b           -> t a + t b
               Let _   _a  b     -> t b
      |]
