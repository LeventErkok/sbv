{-# LANGUAGE QuasiQuotes #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module T where

import Expr
import Data.SBV

f :: SExpr -> SInteger
f e = [sCase|Expr e of
         Var s     | s .== literal "a"                       -> 0
                   | s .== literal "b" .|| s .== literal "c" -> 1
                   | sTrue                                   -> 2

         Num i     | sTrue                                   -> 3

         _                                                   -> 6
      |]
