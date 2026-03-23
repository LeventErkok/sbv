{-# LANGUAGE QuasiQuotes #-}

{-# OPTIONS_GHC -Wall -Werror -ddump-splices #-}

-- Positive: Deep nesting (4 levels). Outer Expr, inner Maybe, inner Either, innermost Bool.
module T where

import Expr
import Data.SBV

t :: SExpr -> SMaybe (Either Integer Bool) -> SBool -> SInteger
t e m b = [sCase| e of
                  Zero      -> case m of
                                 Nothing -> 0
                                 Just v  -> case v of
                                              Left x  -> case b of
                                                           True  -> x
                                                           False -> -x
                                              Right _ -> 1
                  Num k     -> k
                  Var _     -> -1
                  Add a _   -> t a m b
                  Let _ _ c -> t c m b
         |]
