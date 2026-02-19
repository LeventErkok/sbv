{-# LANGUAGE QuasiQuotes #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module T where

import Expr
import Data.SBV

-- Positive: nested pattern with wildcard inside the nested constructor
t :: SExpr -> SInteger
t e = [sCase|Expr e of
               Zero          -> 0
               Num k         -> k
               Var s         -> ite (s .== literal "a") 1 2
               Add (Num _) j -> 1 + t j
               Add a b       -> t a + t b
               Let _   _a  b -> t b
      |]
