-----------------------------------------------------------------------------
-- |
-- Module    : Documentation.SBV.Examples.ADT.Basic
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Basic ADT examples.
-----------------------------------------------------------------------------
-- {-# OPTIONS_GHC -Wall -Werror #-}
{-# OPTIONS_GHC -Wall -Werror -ddump-splices #-}

{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell     #-}

module Documentation.SBV.Examples.ADT.Basic where

import Data.SBV
import Data.SBV.Tuple
import qualified Data.SBV.List as SL

-- | A basic arithmetic expression type
data Expr = Num Integer
          | Var String
          | Add Expr Expr
          | Let String Expr Expr

mkSymbolic ''Expr

eval :: SExpr -> SInteger
eval = go SL.nil
 where go :: SList (String, Integer) -> SExpr -> SInteger
       go = smtFunction "eval" $ \env expr -> sCaseExpr expr
                                                        (\{- Num -} i     -> i)
                                                        (\{- Var -} s     -> get env s)
                                                        (\{- Add -} l r   -> go env l + go env r)
                                                        (\{- Let -} s e r -> go (tuple (s, go env e) SL..: env) r)

       get :: SList (String, Integer) -> SString -> SInteger
       get = smtFunction "get" $ \env s -> ite (SL.null env) 0
                                         $ let (k, v) = untuple (SL.head env)
                                           in ite (s .== k) v (get (SL.tail env) s)

-- | Create two different values:
--
-- >>> test
test :: IO SatResult
test = satWith z3{verbose=True} $ do
          x :: SExpr <- free "x"
          y :: SExpr <- free "y"

          q :: SInteger <- free "q"

          constrain $ x ./== (y :: SExpr)
          constrain $ y .=== sLet (literal "x") (sNum q) (sAdd (sVar (literal "x")) (sNum 3))
          constrain $ isLet x
          constrain $ eval x .== 3
          constrain $ eval x .== eval y + 5
