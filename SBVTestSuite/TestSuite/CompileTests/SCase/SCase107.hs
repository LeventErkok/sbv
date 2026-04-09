{-# LANGUAGE QuasiQuotes #-}

{-# OPTIONS_GHC -Wall -Werror -Wno-name-shadowing -ddump-splices #-}

-- Positive: Scoping regression test. Nested pattern var 'k' from 'Add (Num k) _'
-- is used in one branch of a nested case on SMaybe, while a sibling branch shadows
-- 'k' with a let binding. Old scope-unaware freeVars would drop the accessor binding
-- for 'k', causing a compilation error. See also PCase77 for the pCase counterpart.
module T where

import Expr
import Data.SBV

t :: SExpr -> SMaybe Integer -> SInteger
t e m = [sCase| e of
                Zero          -> 0
                Num _         -> 0
                Var _         -> 0
                Add (Num k) _ -> case m of
                                   Nothing -> let k = 42 in k
                                   Just v  -> k + v
                Add _ _       -> 0
                Let _ _ _     -> 0
       |]
