-----------------------------------------------------------------------------
-- |
-- Module    : Documentation.SBV.Examples.Transformers.SymbolicEval
-- Copyright : (c) Brian Schroeder
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- A demonstration of the use of the 'SymbolicT' and 'QueryT' transformers in
-- the setting of symbolic program evaluation.
--
-- In this example, we perform symbolic evaluation across three steps:
--
-- 1. allocate free variables, so we can extract a model after evaluation
-- 2. perform symbolic evaluation of a program and an associated property
-- 3. querying the solver for whether it's possible to find a set of program
--    inputs that falsify the property. if there is, we extract a model.
--
-- To simplify the example, our programs always have exactly two integer inputs
-- named @x@ and @y@.
-----------------------------------------------------------------------------

{-# LANGUAGE CPP                        #-}
{-# LANGUAGE DeriveFunctor              #-}
{-# LANGUAGE GADTs                      #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE KindSignatures             #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module Documentation.SBV.Examples.Transformers.SymbolicEval where

import Control.Monad.Except   (Except, ExceptT, MonadError, mapExceptT, runExceptT, throwError)
import Control.Monad.Identity (Identity(runIdentity))
import Control.Monad.IO.Class (MonadIO)
import Control.Monad.Reader   (MonadReader(reader), asks, ReaderT, runReaderT)
import Control.Monad.Trans    (lift)
import Data.Kind              (Type)

import Data.SBV.Dynamic   (SVal)
import Data.SBV.Internals (SBV(SBV), unSBV)
import Data.SBV.Trans.Control

-- Starting with base 4.16; Data.Bits exports And, which conflicts with the definition here
#if MIN_VERSION_base(4,16,0)
import Data.SBV.Trans hiding(And)
#else
import Data.SBV.Trans
#endif

-- * Allocation of symbolic variables, so we can extract a model later.

-- | Monad for allocating free variables.
newtype Alloc a = Alloc { runAlloc :: SymbolicT (ExceptT String IO) a }
    deriving (Functor, Applicative, Monad, MonadIO,
              MonadError String, MonadSymbolic)

-- | Environment holding allocated variables.
data Env = Env { envX   :: SBV Integer
               , envY   :: SBV Integer
               , result :: Maybe SVal -- could be integer or bool. during
                                      -- program evaluation, this is Nothing.
                                      -- we only have a value during property
                                      -- evaluation.
               }
    deriving (Eq, Show)

-- | Allocate an integer variable with the provided name.
alloc :: String -> Alloc (SBV Integer)
alloc "" = throwError "tried to allocate unnamed value"
alloc nm = free nm

-- | Allocate an 'Env' holding all input variables for the program.
allocEnv :: Alloc Env
allocEnv = do
    x <- alloc "x"
    y <- alloc "y"
    pure $ Env x y Nothing

-- * Symbolic term evaluation

-- | The term language we use to express programs and properties.
data Term :: Type -> Type where
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

-- | Monad for performing symbolic evaluation.
newtype Eval a = Eval { unEval :: ReaderT Env (Except String) a }
    deriving (Functor, Applicative, Monad, MonadReader Env, MonadError String)

-- | Unsafe cast for symbolic values. In production code, we would check types instead.
unsafeCastSBV :: SBV a -> SBV b
unsafeCastSBV = SBV . unSBV

-- | Symbolic evaluation function for 'Term'.
eval :: Term r -> Eval (SBV r)
eval (Var "x")           = asks $ unsafeCastSBV . envX
eval (Var "y")           = asks $ unsafeCastSBV . envY
eval (Var "result")      = do mRes <- reader result
                              case mRes of
                                Nothing -> throwError "unknown variable"
                                Just sv -> pure $ SBV sv
eval (Var _)             = throwError "unknown variable"
eval (Lit i)             = pure $ literal i
eval (Plus        t1 t2) = (+)   <$> eval t1 <*> eval t2
eval (LessThan    t1 t2) = (.<)  <$> eval t1 <*> eval t2
eval (GreaterThan t1 t2) = (.>)  <$> eval t1 <*> eval t2
eval (Equals      t1 t2) = (.==) <$> eval t1 <*> eval t2
eval (Not         t)     = sNot  <$> eval t
eval (Or          t1 t2) = (.||) <$> eval t1 <*> eval t2
eval (And         t1 t2) = (.&&) <$> eval t1 <*> eval t2
eval (Implies     t1 t2) = (.=>) <$> eval t1 <*> eval t2

-- | Runs symbolic evaluation, sending a 'Term' to a symbolic value (or
-- failing). Used for symbolic evaluation of programs and properties.
runEval :: Env -> Term a -> Except String (SBV a)
runEval env term = runReaderT (unEval $ eval term) env

-- | A program that can reference two input variables, @x@ and @y@.
newtype Program a = Program (Term a)

-- | A symbolic value representing the result of running a program -- its
-- output.
newtype Result = Result SVal

-- | Makes a 'Result' from a symbolic value.
mkResult :: SBV a -> Result
mkResult = Result . unSBV

-- | Performs symbolic evaluation of a 'Program'.
runProgramEval :: Env -> Program a -> Except String Result
runProgramEval env (Program term) = mkResult <$> runEval env term

-- * Property evaluation

-- | A property describes a quality of a 'Program'. It is a 'Term' yields a
-- boolean value.
newtype Property = Property (Term Bool)

-- | Performs symbolic evaluation of a 'Property.
runPropertyEval :: Result -> Env -> Property -> Except String (SBV Bool)
runPropertyEval (Result res) env (Property term) =
    runEval (env { result = Just res }) term

-- * Checking whether a program satisfies a property

-- | The result of 'check'ing the combination of a 'Program' and a 'Property'.
data CheckResult = Proved | Counterexample Integer Integer
    deriving (Eq, Show)

-- | Sends an 'Identity' computation to an arbitrary monadic computation.
generalize :: Monad m => Identity a -> m a
generalize = pure . runIdentity

-- | Monad for querying a solver.
newtype Q a = Q { runQ :: QueryT (ExceptT String IO) a }
    deriving (Functor, Applicative, Monad, MonadIO, MonadError String, MonadQuery)

-- | Creates a computation that queries a solver and yields a 'CheckResult'.
mkQuery :: Env -> Q CheckResult
mkQuery env = do
    satResult <- checkSat
    case satResult of
        Sat    -> Counterexample <$> getValue (envX env)
                                 <*> getValue (envY env)
        Unsat  -> pure Proved
        DSat{} -> throwError "delta-sat"
        Unk    -> throwError "unknown"

-- | Checks a 'Property' of a 'Program' (or fails).
check :: Program a -> Property -> IO (Either String CheckResult)
check program prop = runExceptT $ runSMTWith z3 $ do
    env <- runAlloc allocEnv
    test <- lift $ mapExceptT generalize $ do
        res <- runProgramEval env program
        runPropertyEval res env prop
    constrain $ sNot test
    query $ runQ $ mkQuery env

-- * Some examples

-- | Check that @x+1+y@ generates a counter-example for the property that the
-- result is less than @10@ when @x+y@ is at least @9@. We have:
--
-- >>> ex1
-- Right (Counterexample 0 9)
ex1 :: IO (Either String CheckResult)
ex1 = check (Program  $ Var "x" `Plus` Lit 1 `Plus` Var "y")
            (Property $ Var "result" `LessThan` Lit 10)

-- | Check that the program @x+y@ correctly produces a result greater than @1@ when
-- both @x@ and @y@ are at least @1@. We have:
--
-- >>> ex2
-- Right Proved
ex2 :: IO (Either String CheckResult)
ex2 = check (Program  $ Var "x" `Plus` Var "y")
            (Property $ (positive (Var "x") `And` positive (Var "y"))
                `Implies` (Var "result" `GreaterThan` Lit 1))
  where positive t = t `GreaterThan` Lit 0

-- | Check that we catch the cases properly through the monad stack when there is a
-- syntax error, like an undefined variable. We have:
--
-- >>> ex3
-- Left "unknown variable"
ex3 :: IO (Either String CheckResult)
ex3 = check (Program  $ Var "notAValidVar")
            (Property $ Var "result" `LessThan` Lit 10)

{- HLint ignore module "Use fewer imports" -}
