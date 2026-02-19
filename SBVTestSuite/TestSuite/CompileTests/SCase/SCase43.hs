{-# LANGUAGE QuasiQuotes #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module T where

import Expr
import Data.SBV

-- Positive: integer literal at top level (Num 1 -> ...)
t :: SExpr -> SInteger
t e = [sCase|Expr e of
               Zero  -> 0
               Num 1 -> 100
               Num k -> k
               Var _ -> -1
               Add a b -> t a + t b
               Let _ _ b -> t b
      |]
