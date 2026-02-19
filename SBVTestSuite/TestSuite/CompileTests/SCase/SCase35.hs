{-# LANGUAGE QuasiQuotes #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module T where

import Expr
import Data.SBV

-- Positive: nested patterns on both sides of Add
t :: SExpr -> SInteger
t e = [sCase|Expr e of
               Zero              -> 0
               Num k             -> k
               Var s             -> ite (s .== literal "a") 1 2
               Add (Num i) (Num j) -> i + j
               Add a b           -> t a + t b
               Let _   _a  b     -> t b
      |]
