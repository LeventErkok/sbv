-----------------------------------------------------------------------------
-- |
-- Module    : Documentation.SBV.Examples.ADT.Param
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- A basic parameterized expression ADT example.
-----------------------------------------------------------------------------

{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE FlexibleInstances   #-}
{-# LANGUAGE QuasiQuotes         #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell     #-}
{-# LANGUAGE TypeApplications    #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module Documentation.SBV.Examples.ADT.Param where

import Data.SBV
import Data.SBV.Control
import Data.SBV.RegExp
import Data.SBV.Tuple
import qualified Data.SBV.List as SL

-- | A basic arithmetic expression type.
data Expr nm val = Val val
                 | Var nm
                 | Add (Expr nm val) (Expr nm val)
                 | Mul (Expr nm val) (Expr nm val)
                 | Let nm (Expr nm val) (Expr nm val)

-- | Create a symbolic version of expressions.
mkSymbolic [''Expr]

-- | Show instance for 'Expr'.
instance (Show nm, Show val) => Show (Expr nm val) where
  show (Val i)     = show i
  show (Var a)     = show a
  show (Add l r)   = "(" ++ show l ++ " + " ++ show r ++ ")"
  show (Mul l r)   = "(" ++ show l ++ " * " ++ show r ++ ")"
  show (Let s a b) = "(let " ++ show s ++ " = " ++ show a ++ " in " ++ show b ++ ")"

-- | Show instance for 'Expr', specialized when name is string.
instance {-# OVERLAPPING #-} Show val => Show (Expr String val) where
  show (Val i)     = show i
  show (Var a)     = a
  show (Add l r)   = "(" ++ show l ++ " + " ++ show r ++ ")"
  show (Mul l r)   = "(" ++ show l ++ " * " ++ show r ++ ")"
  show (Let s a b) = "(let " ++ s ++ " = " ++ show a ++ " in " ++ show b ++ ")"

-- | Num instance, simplifies construction of values
instance Integral val => Num (Expr nm val) where
  fromInteger = Val . fromIntegral
  (+)         = Add
  (*)         = Mul
  abs         = error "Num Expr: undefined abs"
  signum      = error "Num Expr: undefined signum"
  negate      = error "Num Expr: undefined negate"

-- | Num instance for the symbolic version
instance (SymVal nm, SymVal val, Integral val) => Num (SExpr nm val) where
  fromInteger = sVal . literal . fromIntegral
  (+)         = sAdd
  (*)         = sMul
  abs         = error "Num SExpr: undefined abs"
  signum      = error "Num SExpr: undefined signum"
  negate      = error "Num SExpr: undefined negate"

-- | Validity: We require each variable appearing to be an identifier to satisfy the predicate given.
-- any number of upper-lower case letters and digits), and all expressions are closed; i.e., any
-- variable referenced is introduced by an enclosing let expression.
isValid :: (SymVal nm, Eq nm, SymVal val) => (SBV nm -> SBool) -> SExpr nm val -> SBool
isValid nmChk = go SL.nil
  where go = smtFunction "valid" $ \env expr -> [sCase|Expr expr of
                                                   Var s     -> nmChk s  .&& s `SL.elem` env
                                                   Val _     -> sTrue
                                                   Add l r   -> go env l .&& go env r
                                                   Mul l r   -> go env l .&& go env r
                                                   Let s a b -> nmChk s  .&& go env a .&& go (s SL..: env) b
                                                |]

-- | Evaluate an expression.
eval :: (SymVal nm, SymVal val, Num (SBV val)) => SExpr nm val -> SBV val
eval = go SL.nil
 where go = smtFunction "eval" $ \env expr -> [sCase|Expr expr of
                                                 Val i     -> i
                                                 Var s     -> get env s
                                                 Add l r   -> go env l + go env r
                                                 Mul l r   -> go env l * go env r
                                                 Let s e r -> go (tuple (s, go env e) SL..: env) r
                                              |]

       get = smtFunction "get" $ \env s -> ite (SL.null env) 0
                                         $ let (k, v) = untuple (SL.head env)
                                           in ite (s .== k) v (get (SL.tail env) s)

-- | A basic theorem about 'eval'.
-- >>> evalPlus5
-- Q.E.D.
evalPlus5 :: IO ThmResult
evalPlus5 = prove $ do e :: SExpr String Integer <- free "e"
                       pure $ eval (e + 5) .== 5 + eval e

-- | Is this a string identifier? Lowercase letter followed by any number of upeer-lower case letters nd digits.
isId :: SString -> SBool
isId s = s `match` (asciiLower * KStar (asciiLetter + digit))

-- | A simple sat result example.
--
-- >>> evalSat
-- Satisfiable. Model:
--   e = Let "h" (Val 1) (Var "h") :: Expr String Integer
--   a =                         9 :: Integer
--   b =                        10 :: Integer
evalSat :: IO SatResult
evalSat = sat $ do e :: SExpr String Integer  <- free "e"
                   constrain $ isValid isId e
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
--   e1 =                      Let "s" (Val 6) (Val 3) :: Expr String Integer
--   e2 = Let "h" (Val (-1)) (Add (Var "h") (Var "h")) :: Expr String Integer
genE :: IO SatResult
genE = sat $ do e1 :: SExpr String Integer <- free "e1"
                e2 :: SExpr String Integer <- free "e2"

                constrain $ isValid isId e1
                constrain $ isValid isId e2

                constrain $ e1 ./== e2
                constrain $ isLet e1
                constrain $ eval e1 .== 3
                constrain $ eval e1 .== eval e2 + 5

-- | Query mode example.
--
-- >>> queryE
-- e1: (let p = (-1 * 1) in (-3 * p))
-- e2: -2
-- e3: (let q = 95 % 96 in q)
queryE :: IO ()
queryE = runSMT $ do
           e1 :: SExpr String Integer <- free "e1"
           e2 :: SExpr String Integer <- free "e2"

           e3 :: SExpr String Rational <- free "e3"

           constrain $ isValid isId e1
           constrain $ isValid isId e2
           constrain $ isValid isId e3

           constrain $ e1 ./== e2
           constrain $ isLet e1
           constrain $ eval e1 .== 3
           constrain $ eval e1 .== eval e2 + 5

           constrain $ isLet e3
           constrain $ isMul (getLet_2 e1)
           constrain $ isMul (getLet_3 e1)

           query $ do cs <- checkSat
                      case cs of
                        Sat -> do e1v <- getValue e1
                                  e2v <- getValue e2
                                  e3v <- getValue e3
                                  io $ putStrLn $ "e1: " ++ show e1v
                                  io $ putStrLn $ "e2: " ++ show e2v
                                  io $ putStrLn $ "e3: " ++ show e3v
                        _   -> error $ "Unexpected result: " ++ show cs

{- HLint ignore module "Reduce duplication" -}
