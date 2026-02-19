{-# LANGUAGE QuasiQuotes #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module T where

import Expr
import Data.SBV

-- Negative: nested pattern covers only a subset of Add; missing fallback for Add _ _
t :: SExpr -> SInteger
t e = [sCase|Expr e of
               Zero          -> 0
               Num k         -> k
               Var s         -> ite (s .== literal "a") 1 2
               Add (Num i) j -> i + t j
               Let _   _a  b -> t b
      |]
