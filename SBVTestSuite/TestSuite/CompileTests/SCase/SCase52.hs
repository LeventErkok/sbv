{-# LANGUAGE QuasiQuotes #-}

{-# OPTIONS_GHC -Wall -Werror -ddump-splices #-}

module T where

import Expr
import Data.SBV

-- Dump test: nested pattern with literal (synthetic guards, accessors, let-bindings)
t :: SExpr -> SInteger
t e = [sCase|Expr e of
               Add (Num 0) j -> t j
               Add a b       -> t a + t b
               Zero          -> 0
               Num i         -> i
               Var _         -> 1
               Let _ _ _     -> 3
      |]
