{-# LANGUAGE QuasiQuotes #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module T where

import Expr
import Data.SBV

-- Negative: deeply nested pattern covers only a subset of the outermost Add; missing fallback
t :: SExpr -> SInteger
t e = [sCase|Expr e of
               Zero                          -> 0
               Num k                         -> k
               Var s                         -> ite (s .== literal "a") 1 2
               Add (Add (Add (Num _) b) c) d -> t b + t c + t d
               Let _   _a  b                 -> t b
      |]
