{-# LANGUAGE QuasiQuotes     #-}

module SCase01 where

import Expr
import Data.SBV

t :: SExpr -> SInteger
t e = [sCase|Expr e of|]
