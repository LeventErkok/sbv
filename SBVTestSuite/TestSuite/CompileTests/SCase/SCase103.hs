{-# LANGUAGE QuasiQuotes #-}

{-# OPTIONS_GHC -Wall -Werror -ddump-splices #-}

-- Positive: As-pattern with Expr ADT (recursive use of as-bound name)
module T where

import Expr
import Data.SBV

t :: SExpr -> SInteger
t e = [sCase| e of
               whole@(Add a _) -> t a + t whole
               Num k           -> k
               _               -> 0
      |]
