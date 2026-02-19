{-# LANGUAGE QuasiQuotes #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module T where

import Expr
import Data.SBV

-- Positive: integer literal in nested position (Add (Num 0) j -> ...)
t :: SExpr -> SInteger
t e = [sCase|Expr e of
               Zero          -> 0
               Num k         -> k
               Var _         -> -1
               Add (Num 0) j -> t j
               Add a       b -> t a + t b
               Let _ _     b -> t b
      |]
