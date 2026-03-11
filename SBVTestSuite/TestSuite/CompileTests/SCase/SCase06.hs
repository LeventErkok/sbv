{-# LANGUAGE QuasiQuotes #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module T where

import Expr
import Data.SBV

-- Unknown constructor
t :: SExpr -> SInteger
t e = [sCase| e of FooBar _ -> 1|]
