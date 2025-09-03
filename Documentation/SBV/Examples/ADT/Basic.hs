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
{-# OPTIONS_GHC -Wall -Werror #-}

{-# LANGUAGE QuasiQuotes         #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell     #-}

module Documentation.SBV.Examples.ADT.Basic where

import Data.SBV
import Data.SBV.RegExp
import Data.SBV.Tuple
import qualified Data.SBV.List as SL

-- | A basic arithmetic expression type
data Expr = Num Integer
          | Var String
          | Add Expr Expr
          | Let String Expr Expr
          deriving Show

-- | Create a symbolic version of expressions.
mkSymbolic ''Expr

-- | Validity: We require each variable appearing to be an identifier (lowercase letter followed by
-- any number of upper-lower case letters and digits), and all expressions are closed; i.e., any
-- variable referenced is introduced by an enclosing let expression.
isValid :: SExpr -> SBool
isValid = go SL.nil
  where isId s = s `match` (asciiLower * KStar (asciiLetter + digit))
        go :: SList String -> SExpr -> SBool
        go = smtFunction "valid" $ \env expr -> [sCase|Expr expr of
                                                   Var s     -> isId s .&& s `SL.elem` env
                                                   Num _     -> sTrue
                                                   Add l r   -> go env l .&& go env r
                                                   Let s a b -> isId s .&& go env a .&& go (s SL..: env) b
                                                |]

-- | Evaluate an expression.
eval :: SExpr -> SInteger
eval = go SL.nil
 where go :: SList (String, Integer) -> SExpr -> SInteger
       go = smtFunction "eval" $ \env expr -> [sCase|Expr expr of
                                                 Num i     -> i
                                                 Var s     -> get env s
                                                 Add l r   -> go env l + go env r
                                                 Let s e r -> go (tuple (s, go env e) SL..: env) r
                                              |]

       get :: SList (String, Integer) -> SString -> SInteger
       get = smtFunction "get" $ \env s -> ite (SL.null env) 0
                                         $ let (k, v) = untuple (SL.head env)
                                           in ite (s .== k) v (get (SL.tail env) s)


-- | A basic test, generating a few examples
--
-- >>> test
-- Satisfiable. Model:
--   e1 =    Let "n" (Num 3) (Var "n") :: Expr
--   e2 = Let "h" (Num (-2)) (Var "h") :: Expr
test :: IO SatResult
test = sat $ do e1 :: SExpr <- free "e1"
                e2 :: SExpr <- free "e2"

                constrain $ isValid e1
                constrain $ isValid e2

                constrain $ e1 ./== e2
                constrain $ isLet e1
                constrain $ eval e1 .== 3
                constrain $ eval e1 .== eval e2 + 5
