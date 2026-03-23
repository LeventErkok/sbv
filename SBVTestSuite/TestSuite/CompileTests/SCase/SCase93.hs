{-# LANGUAGE QuasiQuotes #-}

{-# OPTIONS_GHC -Wall -Werror -ddump-splices #-}

-- Positive: Nested case in multiple branches of outer case.
module T where

import Expr
import Data.SBV

t :: SExpr -> SBool -> SInteger
t e b = [sCase| e of
                Zero      -> case b of
                               True  -> 1
                               False -> 0
                Num k     -> case b of
                               True  -> k
                               False -> -k
                Var _     -> -1
                Add a _   -> t a b
                Let _ _ c -> t c b
       |]
