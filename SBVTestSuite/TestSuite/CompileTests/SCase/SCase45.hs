{-# LANGUAGE QuasiQuotes #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module T where

import Expr
import Data.SBV

-- Positive: string literal in nested position (Var "x" -> ...)
t :: SExpr -> SInteger
t e = [sCase|Expr e of
               Zero      -> 0
               Num k     -> k
               Var "x"   -> 42
               Var _     -> -1
               Add a b   -> t a + t b
               Let _ _ b -> t b
      |]
