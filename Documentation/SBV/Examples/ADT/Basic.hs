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
{-# OPTIONS_GHC -Wall -Werror -Wno-partial-type-signatures #-}

{-# LANGUAGE DeriveAnyClass      #-}
{-# LANGUAGE DeriveDataTypeable  #-}
{-# LANGUAGE FlexibleInstances   #-}
{-# LANGUAGE StandaloneDeriving  #-}
{-# LANGUAGE QuasiQuotes         #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell     #-}
{-# LANGUAGE PartialTypeSignatures#-}
{-# LANGUAGE FlexibleContexts     #-}

module Documentation.SBV.Examples.ADT.Basic where

import Data.SBV
import Data.SBV.Tuple
import qualified Data.SBV.List as SL

import Data.SBV.Control

-- | A basic arithmetic expression type
data Expr = Num Integer
          | Var String
          | Add Expr Expr
          | Let String Expr Expr
          deriving Show

reconstruct :: SymVal Expr => String -> [_] -> Expr
reconstruct "Num" [i]    = Num $ fromCV i
reconstruct "Var" [s]    = Var $ fromCV s
reconstruct "Add" [a, b] = Add (fromCV a) (fromCV b)
reconstruct "Let" [s, a, b] = Let (fromCV s) (fromCV a) (fromCV b)
reconstruct _ _ = error "reconstruct"

mkSymbolic ''Expr

data I = I1 | I2 deriving (Enum, Bounded)
mkSymbolic ''I

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

-- | Create two different values:
--
-- >>> test
test :: IO SatResult
test = satWith z3{verbose=True} $ do
          x :: SExpr <- free "x"
          y :: SExpr <- free "y"

          q :: SInteger <- free "q"

          constrain $ x ./== y
          constrain $ y .=== sLet (literal "x") (sNum q) (sAdd (sVar (literal "x")) (sNum 3))
          constrain $ isLet x
          constrain $ eval x .== 3
          constrain $ eval x .== eval y + 5

test2 :: IO ()
test2 = runSMT $ do a :: SExpr <- free "a"
                    constrain $ isAdd a
                    query $ do cs <- checkSat
                               case cs of
                                 Sat{} -> do v <- getValue a
                                             io $ putStrLn $ "Got: " ++ show v
                                 _     -> error $ "Unexpected: " ++ show cs
