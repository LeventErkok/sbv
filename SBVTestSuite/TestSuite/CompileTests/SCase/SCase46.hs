{-# LANGUAGE QuasiQuotes #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module T where

import Expr
import Data.SBV

-- Positive: integer literals on both sides of nested pattern (Add (Num 1) (Num 2) -> ...)
t :: SExpr -> SInteger
t e = [sCase|Expr e of
               Zero              -> 0
               Num k             -> k
               Var _             -> -1
               Add (Num 1) (Num 2) -> 99
               Add a           b -> t a + t b
               Let _       _   b -> t b
      |]
