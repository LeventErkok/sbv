{-# LANGUAGE QuasiQuotes #-}

module T where

import Expr
import Data.SBV

-- Rejected at the top level
[sCase|Expr e of
        Zero  -> 0
        Num i -> i
      |]
