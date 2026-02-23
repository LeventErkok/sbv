{-# LANGUAGE QuasiQuotes #-}

{-# OPTIONS_GHC -Wall -Werror -ddump-splices #-}

module T where

import Expr
import Data.SBV

-- Dump test: wildcard catch-all after some constructors (ite chain with default)
t :: SExpr -> SInteger
t e = [sCase|Expr e of
               Zero          -> 0
               Num i         -> i
               _             -> 99
      |]
