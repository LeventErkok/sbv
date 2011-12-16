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

module Data.SBV.BitVectors.Optimize (OptimizeOpts(..), optimize, optimizeWith, minimize, minimizeWith, maximize, maximizeWith) where

import Data.SBV.BitVectors.Data
import Data.SBV.BitVectors.Model (OrdSymbolic(..), EqSymbolic(..))
import Data.SBV.Provers.Prover   (satWith, z3)
import Data.SBV.SMT.SMT          (SatModel, getModel, modelExists, SMTConfig(..))
import Data.SBV.Utils.Boolean

-- | Optimizer configuration. Note that iterative and quantified approaches are in general not interchangeable.
-- For instance, iterative solutions will loop infinitely when there is no optimal value, but quantified solutions
-- can handle such problems. Of course, quantified problems are harder for SMT solvers, naturally.
data OptimizeOpts = Iterative  Bool   -- ^ Iteratively search. if True, it will be reporting progress
                  | Quantified        -- ^ Use quantifiers

-- | Symbolic optimization. Generalization on 'minimize' and 'maximize' that allows arbitrary
-- cost functions and comparisons.
optimizeWith :: (Show cost, OrdSymbolic cost, Show a, SatModel a, SymWord a)
             => SMTConfig                         -- ^ SMT configuration
             -> OptimizeOpts                      -- ^ Optimization options
             -> (cost -> cost -> SBool)           -- ^ comparator
             -> ([SBV a] -> cost)                 -- ^ cost function
             -> Int                               -- ^ how many elements?
             -> ([SBV a] -> SBool)                -- ^ validity constraint
             -> IO (Maybe [a])
optimizeWith cfg (Iterative chatty) = iterOptimize chatty cfg
optimizeWith cfg Quantified         = quantOptimize cfg

-- | Variant of 'optimizeWith' using z3
optimize :: (Show a, Show cost, OrdSymbolic cost, SatModel a, SymWord a) => OptimizeOpts -> (cost -> cost -> SBool) -> ([SBV a] -> cost) -> Int -> ([SBV a] -> SBool) -> IO (Maybe [a])
optimize = optimizeWith z3

-- | Variant of 'maximize' allowing the use of a user specified solver
maximizeWith :: (Show a, Show cost, SatModel a, SymWord a, OrdSymbolic cost) => SMTConfig -> OptimizeOpts -> ([SBV a] -> cost) -> Int -> ([SBV a] -> SBool) -> IO (Maybe [a])
maximizeWith cfg opts = optimizeWith cfg opts (.>=)

-- | Maximizes a cost function with respect to a constraint. Examples:
--
--   >>> maximize Quantified sum 3 (bAll (.< (10 :: SInteger)))
--   Just [9,9,9]
--
--   >>> maximize Quantified sum 3 (bAll (.> (10 :: SInteger)))
--   Nothing
maximize :: (Show a, Show cost, SatModel a, SymWord a, OrdSymbolic cost) => OptimizeOpts -> ([SBV a] -> cost) -> Int -> ([SBV a] -> SBool) -> IO (Maybe [a])
maximize = maximizeWith z3

-- | Variant of 'minimize' allowing the use of a user specified solver
minimizeWith :: (Show a, Show cost, SatModel a, SymWord a, OrdSymbolic cost) => SMTConfig -> OptimizeOpts -> ([SBV a] -> cost) -> Int -> ([SBV a] -> SBool) -> IO (Maybe [a])
minimizeWith cfg opts = optimizeWith cfg opts (.<=)

-- | Minimizes a cost function with respect to a constraint. Examples:
--
--   >>> minimize Quantified sum 3 (bAll (.> (10 :: SInteger)))
--   Just [11,11,11]
--
--   >>> minimize Quantified sum 3 (bAll (.< (10 :: SInteger)))
--   Nothing
minimize :: (Show a, Show cost, SatModel a, SymWord a, OrdSymbolic cost) => OptimizeOpts -> ([SBV a] -> cost) -> Int -> ([SBV a] -> SBool) -> IO (Maybe [a])
minimize = minimizeWith z3

-- | Optimization using quantifiers
quantOptimize :: (SatModel a, SymWord a) => SMTConfig -> (cost -> cost -> SBool) -> ([SBV a] -> cost) -> Int -> ([SBV a] -> SBool) -> IO (Maybe [a])
quantOptimize cfg cmp cost n valid = do
           m <- satWith cfg $ do xs <- mkExistVars  n
                                 ys <- mkForallVars n
                                 return $ valid xs &&& (valid ys ==> cost xs `cmp` cost ys)
           case getModel m of
             Left e           -> error $ "SBV: Optimization call failed:\n" ++ e
             Right (False, a) -> return $ Just a
             _                -> return Nothing

-- | Optimization using iteration
iterOptimize :: (Show cost, OrdSymbolic cost, Show a, SatModel a, SymWord a) => Bool -> SMTConfig -> (cost -> cost -> SBool) -> ([SBV a] -> cost) -> Int -> ([SBV a] -> SBool) -> IO (Maybe [a])
iterOptimize chatty cfg cmp cost n valid = do
        msg "Trying to find a satisfying solution."
        m <- satWith cfg $ valid `fmap` mkExistVars n
        if not (modelExists m)
           then do msg "The problem is unsatisfiable"
                   return Nothing
           else case getModel m of
                  Left e           -> error $ "SBV: Optimization call failed:\n" ++ e
                  Right (True, _)  -> error "SBV: Unexpected alleged model received."
                  Right (False, a) -> do msg $ "First solution found: " ++ show a
                                         let c = cost (map literal a)
                                         msg $ "Initial cost is     : " ++ show c
                                         msg "Starting iterative search."
                                         go (1::Int) a c
  where msg m | chatty = putStrLn $ "*** " ++ m
              | True   = return ()
        go i curSol curCost = do
                msg $ "Round " ++ show i ++ " ****************************"
                m <- satWith cfg $ do xs <- mkExistVars n
                                      return $ let c = cost xs in valid xs &&& (c `cmp` curCost &&& c ./= curCost)
                if not (modelExists m)
                   then do msg "The current solution is optimal. Terminating search."
                           return $ Just curSol
                   else case getModel m of
                          Left e           -> error $ "SBV: Optimization call failed:\n" ++ e
                          Right (True, _)  -> error "SBV: Unexpected alleged model received."
                          Right (False, a) -> do msg $ "Solution: " ++ show a
                                                 let c = cost (map literal a)
                                                 msg $ "Cost    : " ++ show c
                                                 go (i+1) a c
