-----------------------------------------------------------------------------
-- |
-- Module    : Data.SBV.Lambda
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- A simple expression language over closed terms, used in creating
-- lambda-expressions for (limited) higher-order function support.
-----------------------------------------------------------------------------

{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NamedFieldPuns        #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TypeApplications      #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module Data.SBV.Lambda (
          lambda
        ) where

import Control.Monad.Trans

import Data.SBV.Core.Data
import Data.SBV.Core.Symbolic

import Data.List
import Data.Proxy

-- | Extract an SMTLib compliand lambda string
-- >>> lambda (2 :: SInteger)
-- WHAT
-- >>> lambda (\x -> x+1::SInteger)
-- WHAT
-- >>> lambda (\x y -> x+y*2 :: SInteger)
-- WHAT
-- >>> lambda (\x (y, z) -> x+y*2+z :: SInteger)
-- WHAT
-- >>> lambda (\x (y, z) k -> x+y*2+z + k :: SInteger)
-- WHAT
lambda :: Lambda Symbolic a => a -> IO String
lambda f = do st  <- mkNewState Lambda
              res <- fst <$> runSymbolicInState st (mkLambda st f)
              pure $ toLambda res

-- | Values that we can turn into a lambda abstraction
class MonadSymbolic m => Lambda m a where
  mkLambda :: State -> a -> m Result

-- | Turn a symbolic computation to an encapsulated lambda
instance MonadSymbolic m => Lambda m (SymbolicT m (SBV a)) where
  mkLambda st cmp = do ((), res) <- runSymbolicInState st (cmp >>= output >> return ())
                       pure res

-- | Base case, simple values
instance MonadSymbolic m => Lambda m (SBV a) where
  mkLambda st = mkLambda st . (pure :: SBV a -> SymbolicT m (SBV a))

-- | Functions
instance (SymVal a, Lambda m r) => Lambda m (SBV a -> r) where
  mkLambda st fn = mkLambda st =<< fn <$> mkArg
    where mkArg = do let k = kindOf (Proxy @a)
                     sv <- liftIO $ internalVariable st k
                     pure $ SBV $ SVal k (Right (cache (const (return sv))))

-- | Functions of 2-tuple argument
instance (SymVal a, SymVal b, Lambda m r) => Lambda m ((SBV a, SBV b) -> r) where
  mkLambda st fn = mkLambda st $ \a b -> fn (a, b)

-- | Functions of 3-tuple arguments
instance (SymVal a, SymVal b, SymVal c, Lambda m r) => Lambda m ((SBV a, SBV b, SBV c) -> r) where
  mkLambda st fn = mkLambda st $ \a b c -> fn (a, b, c)

-- | Functions of 4-tuple arguments
instance (SymVal a, SymVal b, SymVal c, SymVal d, Lambda m r) => Lambda m ((SBV a, SBV b, SBV c, SBV d) -> r) where
  mkLambda st fn = mkLambda st $ \a b c d-> fn (a, b, c, d)

-- | Functions of 5-tuple arguments
instance (SymVal a, SymVal b, SymVal c, SymVal d, SymVal e, Lambda m r) => Lambda m ((SBV a, SBV b, SBV c, SBV d, SBV e) -> r) where
  mkLambda st fn = mkLambda st $ \a b c d e -> fn (a, b, c, d, e)

-- | Functions of 6-tuple arguments
instance (SymVal a, SymVal b, SymVal c, SymVal d, SymVal e, SymVal f, Lambda m r) => Lambda m ((SBV a, SBV b, SBV c, SBV d, SBV e, SBV f) -> r) where
  mkLambda st fn = mkLambda st $ \a b c d e f -> fn (a, b, c, d, e, f)

-- | Functions of 7-tuple arguments
instance (SymVal a, SymVal b, SymVal c, SymVal d, SymVal e, SymVal f, SymVal g, Lambda m r) => Lambda m ((SBV a, SBV b, SBV c, SBV d, SBV e, SBV f, SBV g) -> r) where
  mkLambda st fn = mkLambda st $ \a b c d e f g -> fn (a, b, c, d, e, f, g)

-- | Convert the result of a symbolic run to an SMTLib lambda expression
toLambda :: Result -> String
toLambda = sh
 where bail xs = error $ unlines $ "*** Data.SBV.lambda: Unsupported construct."
                                 : map ("*** " ++) ("" : xs ++ report)
       report = [ ""
                , "Please request this as a feature at https://github.com/LeventErkok/sbv/issues"
                ]

       sh (Result _ki           -- Kind info, we're assuming that all the kinds used are already available in the surrounding context.
                                -- There's no way to create a new kind in a lambda. If a new kind is used, it should be registered.

                  _qcInfo       -- Quickcheck info, does not apply, ignored

                  observables   -- Observables: No way to display these, so if present we error out

                  codeSegs      -- UI code segments: Again, shouldn't happen; if present, error out

                  -- Left here
                  _is
                  _consts
                  _tbls
                  _arrs
                  _uis
                  _axs
                  _pgm
                  _cstrs
                  _assertions
                  _outputs
         )
         | not (null observables)
         = bail [ "Observable values inside lambda's are not supported."
                , "  Saw: " ++ intercalate ", " [o | (o, _, _) <- observables]
                ]
         | not (null codeSegs)
         = bail [ "Uninterpreted code segments inside lambda's are not supported."
                , "  Saw: " ++ intercalate ", " [o | (o, _) <- codeSegs]
                ]
         | True
         = "TBD"
