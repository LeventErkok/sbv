-----------------------------------------------------------------------------
-- |
-- Module      :  Documentation.SBV.Examples.Queries.Transformer
-- Copyright   :  (c) Brian Schroeder
-- License     :  BSD3
-- Maintainer  :  erkokl@gmail.com
-- Stability   :  experimental
--
-- A demonstration of the use of the 'SymbolicT' and 'QueryT' transformers in
-- the setting of symbolic program evaluation.
-----------------------------------------------------------------------------

{-# LANGUAGE DeriveFunctor              #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE GADTs                      #-}
{-# LANGUAGE KindSignatures             #-}

module Documentation.SBV.Examples.Queries.Transformer where

import Control.Monad.Except   (Except, ExceptT, MonadError, mapExceptT,
                               runExceptT, throwError)
import Control.Monad.Identity (Identity(runIdentity))
import Control.Monad.IO.Class (MonadIO)
import Control.Monad.Reader   (MonadReader(ask, reader), ReaderT, runReaderT)
import Control.Monad.Trans    (lift)

import Data.SBV.Dynamic   (SVal)
import Data.SBV.Internals (SBV(SBV), unSBV)
import Data.SBV.Trans
import Data.SBV.Trans.Control

-- * Allocation of symbolic variables, so we can extract a model later.

newtype Alloc a = Alloc { runAlloc :: SymbolicT (ExceptT String IO) a }
    deriving (Functor, Applicative, Monad, MonadIO,
              MonadError String, MonadSymbolic)

data Env = Env { envX   :: SBV Integer
               , envY   :: SBV Integer
               , result :: Maybe SVal -- could be integer or bool. during
                                      -- program evaluation, this is Nothing.
                                      -- we only have a value during property
                                      -- evaluation.
               }
    deriving (Eq, Show)

alloc :: String -> Alloc (SBV Integer)
alloc "" = throwError "tried to allocate unnamed value"
alloc nm = free nm

allocEnv :: Alloc Env
allocEnv = do
    x <- alloc "x"
    y <- alloc "y"
    pure $ Env x y Nothing

-- * Symbolic term evaluation

data Term :: * -> * where
    Var      :: String                       -> Term r
    Lit      :: Integer                      -> Term Integer
    Plus     :: Term Integer -> Term Integer -> Term Integer
    LessThan :: Term Integer -> Term Integer -> Term Bool

newtype Eval a = Eval { unEval :: ReaderT Env (Except String) a }
    deriving (Functor, Applicative, Monad,
              MonadReader Env, MonadError String)

-- Unsafe. In real code, we would check types.
unsafeCastSBV :: SBV a -> SBV b
unsafeCastSBV = SBV . unSBV

eval :: Term r -> Eval (SBV r)
eval (Var "x")        = unsafeCastSBV . envX <$> ask
eval (Var "y")        = unsafeCastSBV . envY <$> ask
eval (Var "result")   = do mRes <- reader result
                           case mRes of
                             Nothing -> throwError "unknown variable"
                             Just sv -> pure $ SBV sv
eval (Var _)          = throwError "unknown variable"
eval (Lit i)          = pure $ literal i
eval (Plus t1 t2)     = (+)  <$> eval t1 <*> eval t2
eval (LessThan t1 t2) = (.<) <$> eval t1 <*> eval t2

runEval :: Env -> Term a -> Except String (SBV a)
runEval env term = runReaderT (unEval $ eval term) env

newtype Result = Result SVal

mkResult :: SBV a -> Result
mkResult = Result . unSBV

runProgramEval :: Env -> Term a -> Except String Result
runProgramEval env term = mkResult <$> runEval env term

-- * Property evaluation

newtype Property = Property (Term Bool)

runPropertyEval :: Result -> Env -> Property -> Except String (SBV Bool)
runPropertyEval (Result res) env (Property term) =
    runEval (env { result = Just res }) term

-- * Checking whether a program satisfies a property

data CheckResult = Proved | Counterexample Integer Integer
    deriving (Show)

generalize :: Monad m => Identity a -> m a
generalize = pure . runIdentity

check :: Term a -> Property -> IO (Either String CheckResult)
check term prop = runExceptT $ runSMTWith z3 $ do
    env <- runAlloc allocEnv
    test <- lift $ mapExceptT generalize $ do
        res <- runProgramEval env term
        runPropertyEval res env prop
    constrain $ bnot test
    query $ do
        satResult <- checkSat
        case satResult of
            Sat   -> Counterexample <$> getValue (envX env)
                                    <*> getValue (envY env)
            Unsat -> pure Proved
            Unk   -> throwError "unknown"

-- * An example

ex1 :: IO (Either String CheckResult)
ex1 = check program (Property property)
    where program  = Var "x" `Plus` Lit 1 `Plus` Var "y"
          property = Var "result" `LessThan` Lit 10

-- λ> ex1
-- Right (Counterexample 0 9)
