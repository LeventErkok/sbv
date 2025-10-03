-----------------------------------------------------------------------------
-- |
-- Module    : Documentation.SBV.Examples.ADT.Expr
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- A basic expression ADT example.
-----------------------------------------------------------------------------

{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE FlexibleInstances   #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE QuasiQuotes         #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell     #-}
{-# LANGUAGE TypeApplications    #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module Documentation.SBV.Examples.ADT.Expr where

import Data.SBV
import Data.SBV.Control
import Data.SBV.RegExp
import Data.SBV.Tuple
import qualified Data.SBV.List as SL

-- | A basic arithmetic expression type.
data Expr = Val Integer
          | Var String
          | Add Expr Expr
          | Mul Expr Expr
          | Let String Expr Expr

-- | Create a symbolic version of expressions.
mkSymbolic [''Expr]

-- | Show instance for 'Expr'.
instance Show Expr where
  show (Val i)     = show i
  show (Var a)     = a
  show (Add l r)   = "(" ++ show l ++ " + " ++ show r ++ ")"
  show (Mul l r)   = "(" ++ show l ++ " * " ++ show r ++ ")"
  show (Let s a b) = "(let " ++ s ++ " = " ++ show a ++ " in " ++ show b ++ ")"

-- | Num instance, simplifies construction of values
instance Num Expr where
  fromInteger = Val
  (+)         = Add
  (*)         = Mul
  abs         = error "Num Expr: undefined abs"
  signum      = error "Num Expr: undefined signum"
  negate      = error "Num Expr: undefined negate"

-- | Num instance for the symbolic version
instance Num SExpr where
  fromInteger = sVal . literal
  (+)         = sAdd
  (*)         = sMul
  abs         = error "Num SExpr: undefined abs"
  signum      = error "Num SExpr: undefined signum"
  negate      = error "Num SExpr: undefined negate"

-- | Validity: We require each variable appearing to be an identifier (lowercase letter followed by
-- any number of upper-lower case letters and digits), and all expressions are closed; i.e., any
-- variable referenced is introduced by an enclosing let expression.
isValid :: SExpr -> SBool
isValid = go SL.nil
  where isId s = s `match` (asciiLower * KStar (asciiLetter + digit))
        go :: SList String -> SExpr -> SBool
        go = smtFunction "valid" $ \env expr -> [sCase|Expr expr of
                                                   Var s     -> isId s .&& s `SL.elem` env
                                                   Val _     -> sTrue
                                                   Add l r   -> go env l .&& go env r
                                                   Mul l r   -> go env l .&& go env r
                                                   Let s a b -> isId s .&& go env a .&& go (s SL..: env) b
                                                |]

-- | Evaluate an expression.
eval :: SExpr -> SInteger
eval = go SL.nil
 where go :: SList (String, Integer) -> SExpr -> SInteger
       go = smtFunction "eval" $ \env expr -> [sCase|Expr expr of
                                                 Val i     -> i
                                                 Var s     -> get env s
                                                 Add l r   -> go env l + go env r
                                                 Mul l r   -> go env l * go env r
                                                 Let s e r -> go (tuple (s, go env e) SL..: env) r
                                              |]

       get :: SList (String, Integer) -> SString -> SInteger
       get = smtFunction "get" $ \env s -> ite (SL.null env) 0
                                         $ let (k, v) = untuple (SL.head env)
                                           in ite (s .== k) v (get (SL.tail env) s)

-- | A basic theorem about 'eval'.
-- >>> evalPlus5
-- Q.E.D.
evalPlus5 :: IO ThmResult
evalPlus5 = prove $ do e :: SExpr <- free "e"
                       pure $ eval (e + 5) .== 5 + eval e

-- | A simple sat result example.
--
-- >>> evalSat
-- Satisfiable. Model:
--   e = Let "k" (Val 1) (Var "k") :: Expr
--   a =                         9 :: Integer
--   b =                        10 :: Integer
evalSat :: IO SatResult
evalSat = sat $ do e :: SExpr    <- free "e"
                   constrain $ isValid e
                   constrain $ isLet   e

                   a :: SInteger <- free "a"
                   b :: SInteger <- free "b"
                   constrain $ a .>= 4
                   constrain $ b .>= 10

                   pure $ eval (e + sVal a) .== b * eval e

-- | Another test, generating some (mildly) interesting examples.
--
-- >>> genE
-- Satisfiable. Model:
--   e1 = Let "p" (Val 5) (Val 3) :: Expr
--   e2 =                Val (-2) :: Expr
genE :: IO SatResult
genE = sat $ do e1 :: SExpr <- free "e1"
                e2 :: SExpr <- free "e2"

                constrain $ isValid e1
                constrain $ isValid e2

                constrain $ e1 ./== e2
                constrain $ isLet e1
                constrain $ eval e1 .== 3
                constrain $ eval e1 .== eval e2 + 5

-- | Query mode example.
--
-- >>> queryE
-- e1: (let p = 5 in 3)
-- e2: -2
queryE :: IO ()
queryE = runSMT $ do
           e1 :: SExpr <- free "e1"
           e2 :: SExpr <- free "e2"

           constrain $ isValid e1
           constrain $ isValid e2

           constrain $ e1 ./== e2
           constrain $ isLet e1
           constrain $ eval e1 .== 3
           constrain $ eval e1 .== eval e2 + 5

           query $ do cs <- checkSat
                      case cs of
                        Sat -> do e1v <- getValue e1
                                  e2v <- getValue e2
                                  io $ putStrLn $ "e1: " ++ show e1v
                                  io $ putStrLn $ "e2: " ++ show e2v
                        _   -> error $ "Unexpected result: " ++ show cs
