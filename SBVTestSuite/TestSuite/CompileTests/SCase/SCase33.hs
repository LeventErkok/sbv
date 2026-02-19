{-# LANGUAGE QuasiQuotes #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module T where

import Expr
import Data.SBV

-- Positive: deeply nested pattern Add (Add (Num i) j) k
t :: SExpr -> SInteger
t e = [sCase|Expr e of
               Zero                  -> 0
               Num k                 -> k
               Var s                 -> ite (s .== literal "a") 1 2
               Add (Add (Num i) j) k -> i + t j + t k
               Add a b               -> t a + t b
               Let _   _a  b         -> t b
      |]
