{-# LANGUAGE QuasiQuotes #-}

{-# OPTIONS_GHC -Wall -Werror -ddump-splices #-}

module T where

import Expr
import Data.SBV

-- Dump test: simple unguarded, all constructors, no guards/wildcards/nesting
t :: SExpr -> SInteger
t e = [sCase|Expr e of
               Zero          -> 0
               Num i         -> i
               Var _         -> 1
               Add _ _       -> 2
               Let _ _ _     -> 3
      |]
