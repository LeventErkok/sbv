{-# LANGUAGE QuasiQuotes #-}

module T where

import Expr
import Data.SBV

-- bad syntax
t :: SExpr -> SInteger
t e = [sCase|Expr e + 1|]
