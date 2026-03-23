{-# LANGUAGE QuasiQuotes #-}

{-# OPTIONS_GHC -Wall -Werror -ddump-splices #-}

module T where

import Expr
import Data.SBV

t :: SExpr -> SInteger
t e = [sCase| e of
               Zero          -> 0
               Num i         -> i
               Var s         -> ite (s .== "a") 1 2
               Add a b       -> t e + t b
               _ _ -> 3
      |]
