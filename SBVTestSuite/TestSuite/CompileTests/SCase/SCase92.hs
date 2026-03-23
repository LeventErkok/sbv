{-# LANGUAGE QuasiQuotes #-}

{-# OPTIONS_GHC -Wall -Werror -ddump-splices #-}

-- Positive: Deep nesting (3 levels). Outer Expr, inner Maybe, innermost Either.
module T where

import Expr
import Data.SBV

t :: SExpr -> SMaybe (Either Integer Bool) -> SInteger
t e m = [sCase| e of
                Zero  -> case m of
                           Nothing -> 0
                           Just v  -> case v of
                                        Left  x -> x
                                        Right _ -> 1
                Num k     -> k
                Var _     -> -1
                Add a b   -> t a m + t b m
                Let _ _ b -> t b m
       |]
