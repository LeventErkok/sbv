{-# LANGUAGE QuasiQuotes #-}

{-# OPTIONS_GHC -Wall -Werror -ddump-splices #-}

module T where

import Expr
import Data.SBV

t :: SExpr -> SInteger
t e = [sCase| e of
               Zero          -> 0
               Num i         -> i
               _ -> 3
               _ -> 5
      |]
