{-# LANGUAGE QuasiQuotes #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module T where

import Expr
import Data.SBV

-- Negative: Add (Num 1) j without a fallback for the Add constructor
t :: SExpr -> SInteger
t e = [sCase|Expr e of
               Zero          -> 0
               Num k         -> k
               Var _         -> -1
               Add (Num 1) j -> 100 + t j
               Let _ _     b -> t b
      |]
