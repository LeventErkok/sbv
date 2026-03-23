{-# LANGUAGE QuasiQuotes #-}

{-# OPTIONS_GHC -Wall -Werror -ddump-splices #-}

module T where

import Expr
import Data.SBV

-- bad syntax
t :: SExpr -> SInteger
t e = [sCase| e + 1|]
