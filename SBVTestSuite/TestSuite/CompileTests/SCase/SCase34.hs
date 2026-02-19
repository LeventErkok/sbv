{-# LANGUAGE QuasiQuotes #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module T where

import Expr
import Data.SBV

-- Positive: nested pattern combined with a guard
t :: SExpr -> SInteger
t e = [sCase|Expr e of
               Zero                -> 0
               Num k               -> k
               Var s               -> ite (s .== literal "a") 1 2
               Add (Num i) j | i .> 0 -> i + t j
               Add a b             -> t a + t b
               Let _   _a  b       -> t b
      |]
