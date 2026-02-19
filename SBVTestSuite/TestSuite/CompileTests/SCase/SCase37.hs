{-# LANGUAGE QuasiQuotes #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module T where

import Expr
import Data.SBV

-- Negative: literal pattern inside nested position is not supported
t :: SExpr -> SInteger
t e = [sCase|Expr e of
               Zero          -> 0
               Num k         -> k
               Var s         -> ite (s .== literal "a") 1 2
               Add (Num 0) j -> t j
               Add a b       -> t a + t b
               Let _   _a  b -> t b
      |]
