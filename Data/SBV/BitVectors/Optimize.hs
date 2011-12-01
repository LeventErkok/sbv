-----------------------------------------------------------------------------
-- |
-- Module      :  Data.SBV.BitVectors.Optimize
-- Copyright   :  (c) Levent Erkok
-- License     :  BSD3
-- Maintainer  :  erkokl@gmail.com
-- Stability   :  experimental
-- Portability :  portable
--
-- Number representations in hex/bin
-----------------------------------------------------------------------------

{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeSynonymInstances #-}

module Data.SBV.BitVectors.Optimize (optimize, minimize, maximize) where

import Data.SBV.BitVectors.Data
import Data.SBV.BitVectors.Model (OrdSymbolic(..))
import Data.SBV.Provers.Prover   (satWith, z3)
import Data.SBV.SMT.SMT          (SatModel, getModel)
import Data.SBV.Utils.Boolean

-- | Symbolic optimization. Generalization on 'minimize' and 'maximize' that allows arbitrary
-- cost functions and comparisons.
optimize :: (SatModel a, SymWord a)
         => (cost -> cost -> SBool)           -- ^ comparator
         -> ([SBV a] -> cost)                 -- ^ cost function
         -> Int                               -- ^ how many elements?
         -> ([SBV a] -> SBool)                -- ^ validity constraint
         -> IO (Maybe [a])
optimize cmp cost n valid = do
        m <- satWith z3 $ do
                xs <- mkExistVars  n
                ys <- mkForallVars n
                return $ valid xs &&& (valid ys ==> cost xs `cmp` cost ys)
        case getModel m of
          Right (False, a) -> return $ Just a
          _                -> return Nothing

-- | Maximizes a cost function with respect to a constraint. Examples:
--
--   >>> maximize sum 3 (bAll (.< (10 :: SInteger)))
--   Just [9,9,9]
--
--   >>> maximize sum 3 (bAll (.> (10 :: SInteger)))
--   Nothing
maximize :: (SatModel a, SymWord a, OrdSymbolic cost) => ([SBV a] -> cost) -> Int -> ([SBV a] -> SBool) -> IO (Maybe [a])
maximize = optimize (.>=)

-- | Minimizes a cost function with respect to a constraint. Examples:
--
--   >>> minimize sum 3 (bAll (.> (10 :: SInteger)))
--   Just [11,11,11]
--
--   >>> minimize sum 3 (bAll (.< (10 :: SInteger)))
--   Nothing
minimize :: (SatModel a, SymWord a, OrdSymbolic cost) => ([SBV a] -> cost) -> Int -> ([SBV a] -> SBool) -> IO (Maybe [a])
minimize = optimize (.<=)
