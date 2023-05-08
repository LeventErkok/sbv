-----------------------------------------------------------------------------
-- |
-- Module    : Data.SBV.Tools.BMC
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Bounded model checking interface. See "Documentation.SBV.Examples.ProofTools.BMC"
-- for an example use case.
-----------------------------------------------------------------------------

{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeFamilies     #-}
{-# LANGUAGE TypeOperators    #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module Data.SBV.Tools.BMC (
         bmc, bmcWith
       ) where

import Data.SBV
import Data.SBV.Control

import Control.Monad (when)

-- | Bounded model checking, using the default solver. See "Documentation.SBV.Examples.ProofTools.BMC"
-- for an example use case.
--
-- Note that the BMC engine does *not* guarantee that the solution is unique. However, if it does
-- find a solution at depth @i@, it is guaranteed that there are no shorter solutions.
bmc :: (EqSymbolic st, Queriable IO st, res ~ QueryResult st)
    => Maybe Int                            -- ^ Optional bound
    -> Bool                                 -- ^ Verbose: prints iteration count
    -> Symbolic ()                          -- ^ Setup code, if necessary. (Typically used for 'Data.SBV.setOption' calls. Pass @return ()@ if not needed.)
    -> (st -> SBool)                        -- ^ Initial condition
    -> (st -> [st])                         -- ^ Transition relation
    -> (st -> SBool)                        -- ^ Goal to cover, i.e., we find a set of transitions that satisfy this predicate.
    -> IO (Either String (Int, [res]))      -- ^ Either a result, or a satisfying path of given length and intermediate observations.
bmc = bmcWith defaultSMTCfg

-- | Bounded model checking, configurable with the solver
bmcWith :: (EqSymbolic st, Queriable IO st, res ~ QueryResult st)
        => SMTConfig
        -> Maybe Int
        -> Bool
        -> Symbolic ()
        -> (st -> SBool)
        -> (st -> [st])
        -> (st -> SBool)
        -> IO (Either String (Int, [res]))
bmcWith cfg mbLimit chatty setup initial trans goal
  = runSMTWith cfg $ do setup
                        query $ do state <- create
                                   constrain $ initial state
                                   go 0 state []
   where go i _ _
          | Just l <- mbLimit, i >= l
          = return $ Left $ "BMC limit of " ++ show l ++ " reached"
         go i curState sofar = do when chatty $ io $ putStrLn $ "BMC: Iteration: " ++ show i
                                  push 1
                                  constrain $ goal curState
                                  cs <- checkSat
                                  case cs of
                                    DSat{} -> error "BMC: Solver returned an unexpected delta-sat result."
                                    Sat    -> do when chatty $ io $ putStrLn $ "BMC: Solution found at iteration " ++ show i
                                                 ms <- mapM project (curState : sofar)
                                                 return $ Right (i, reverse ms)
                                    Unk    -> do when chatty $ io $ putStrLn $ "BMC: Backend solver said unknown at iteration " ++ show  i
                                                 return $ Left $ "BMC: Solver said unknown in iteration " ++ show i
                                    Unsat  -> do pop 1
                                                 nextState <- create
                                                 constrain $ sAny (nextState .==) (trans curState)
                                                 go (i+1) nextState (curState : sofar)
