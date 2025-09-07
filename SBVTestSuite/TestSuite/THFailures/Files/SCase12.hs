{-# LANGUAGE QuasiQuotes #-}

module SCase05 where

import Expr
import Data.SBV

t :: SExpr -> SInteger
t e = [sCase|Expr e of
               Zero          -> 0
               Num i         -> i
               _ -> 3
               _ -> 5
      |]
