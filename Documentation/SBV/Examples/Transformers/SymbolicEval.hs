-----------------------------------------------------------------------------
-- |
-- Module      :  Documentation.SBV.Examples.Transformers.SymbolicEval
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

module Documentation.SBV.Examples.Transformers.SymbolicEval where

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
    Var         :: String                       -> Term r
    Lit         :: Integer                      -> Term Integer
    Plus        :: Term Integer -> Term Integer -> Term Integer
    LessThan    :: Term Integer -> Term Integer -> Term Bool
    GreaterThan :: Term Integer -> Term Integer -> Term Bool
    Equals      :: Term Integer -> Term Integer -> Term Bool
    Not         :: Term Bool                    -> Term Bool
    Or          :: Term Bool    -> Term Bool    -> Term Bool
    And         :: Term Bool    -> Term Bool    -> Term Bool
    Implies     :: Term Bool    -> Term Bool    -> Term Bool

newtype Eval a = Eval { unEval :: ReaderT Env (Except String) a }
    deriving (Functor, Applicative, Monad,
              MonadReader Env, MonadError String)

-- Unsafe. In real code, we would check types.
unsafeCastSBV :: SBV a -> SBV b
unsafeCastSBV = SBV . unSBV

eval :: Term r -> Eval (SBV r)
eval (Var "x")           = unsafeCastSBV . envX <$> ask
eval (Var "y")           = unsafeCastSBV . envY <$> ask
eval (Var "result")      = do mRes <- reader result
                              case mRes of
                                Nothing -> throwError "unknown variable"
                                Just sv -> pure $ SBV sv
eval (Var _)             = throwError "unknown variable"
eval (Lit i)             = pure $ literal i
eval (Plus t1 t2)        = (+)  <$> eval t1 <*> eval t2
eval (LessThan t1 t2)    = (.<) <$> eval t1 <*> eval t2
eval (GreaterThan t1 t2) = (.>) <$> eval t1 <*> eval t2
eval (Equals t1 t2)      = (.==) <$> eval t1 <*> eval t2
eval (Not t)             = bnot <$> eval t
eval (Or t1 t2)          = (|||) <$> eval t1 <*> eval t2
eval (And t1 t2)         = (&&&) <$> eval t1 <*> eval t2
eval (Implies t1 t2)     = (==>) <$> eval t1 <*> eval t2

runEval :: Env -> Term a -> Except String (SBV a)
runEval env term = runReaderT (unEval $ eval term) env

newtype Program a = Program (Term a)

newtype Result = Result SVal

mkResult :: SBV a -> Result
mkResult = Result . unSBV

runProgramEval :: Env -> Program a -> Except String Result
runProgramEval env (Program term) = mkResult <$> runEval env term

-- * Property evaluation

newtype Property = Property (Term Bool)

runPropertyEval :: Result -> Env -> Property -> Except String (SBV Bool)
runPropertyEval (Result res) env (Property term) =
    runEval (env { result = Just res }) term

-- * Checking whether a program satisfies a property

data CheckResult = Proved | Counterexample Integer Integer
    deriving (Eq, Show)

generalize :: Monad m => Identity a -> m a
generalize = pure . runIdentity

newtype Q a = Q { runQ :: QueryT (ExceptT String IO) a }
    deriving (Functor, Applicative, Monad, MonadIO,
              MonadError String, MonadQuery)

mkQuery :: Env -> Q CheckResult
mkQuery env = do
    satResult <- checkSat
    case satResult of
        Sat   -> Counterexample <$> getValue (envX env)
                                <*> getValue (envY env)
        Unsat -> pure Proved
        Unk   -> throwError "unknown"

check :: Program a -> Property -> IO (Either String CheckResult)
check program prop = runExceptT $ runSMTWith z3 $ do
    env <- runAlloc allocEnv
    test <- lift $ mapExceptT generalize $ do
        res <- runProgramEval env program
        runPropertyEval res env prop
    constrain $ bnot test
    query $ runQ $ mkQuery env

-- * Some examples

ex1 :: IO (Either String CheckResult)
ex1 = check (Program  $ Var "x" `Plus` Lit 1 `Plus` Var "y")
            (Property $ Var "result" `LessThan` Lit 10)

-- λ> ex1
-- Right (Counterexample 0 9)

ex2 :: IO (Either String CheckResult)
ex2 = check (Program  $ Var "x" `Plus` Var "y")
            (Property $ (positive (Var "x") `And` positive (Var "y"))
                `Implies` (Var "result" `GreaterThan` Lit 1))
  where positive t = t `GreaterThan` Lit 0

-- λ> ex2
-- Right Proved

ex3 :: IO (Either String CheckResult)
ex3 = check (Program  $ Var "notAValidVar")
            (Property $ Var "result" `LessThan` Lit 10)

-- λ> ex3
-- Left "unknown variable"
