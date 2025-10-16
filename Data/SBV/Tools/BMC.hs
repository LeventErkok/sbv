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
{-# LANGUAGE TypeOperators    #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module Data.SBV.Tools.BMC (
         bmcRefute, bmcRefuteWith, bmcCover, bmcCoverWith
       ) where

import Data.SBV
import Data.SBV.Control

import Control.Monad (when)

-- | Are we covering or refuting?
data BMCKind = Refute
             | Cover

-- | Refutation using bounded model checking, using the default solver. This version tries to refute the goal
-- in a depth-first fashion. Note that this method can find a refutation, but will never find a "proof."
-- If it finds a refutation, it will be the shortest, though not necessarily unique.
bmcRefute :: (Queriable IO st, res ~ QueryResult st)
    => Maybe Int                            -- ^ Optional bound
    -> Bool                                 -- ^ Verbose: prints iteration count
    -> Symbolic ()                          -- ^ Setup code, if necessary. (Typically used for 'Data.SBV.setOption' calls. Pass @return ()@ if not needed.)
    -> (st -> SBool)                        -- ^ Initial condition
    -> (st -> st -> SBool)                  -- ^ Transition relation
    -> (st -> SBool)                        -- ^ Goal to cover, i.e., we find a set of transitions that satisfy this predicate.
    -> IO (Either String (Int, [res]))      -- ^ Either a result, or a satisfying path of given length and intermediate observations.
bmcRefute = bmcRefuteWith defaultSMTCfg

-- | Refutation using a given solver.
bmcRefuteWith :: (Queriable IO st, res ~ QueryResult st)
    => SMTConfig                            -- ^ Solver to use
    -> Maybe Int                            -- ^ Optional bound
    -> Bool                                 -- ^ Verbose: prints iteration count
    -> Symbolic ()                          -- ^ Setup code, if necessary. (Typically used for 'Data.SBV.setOption' calls. Pass @return ()@ if not needed.)
    -> (st -> SBool)                        -- ^ Initial condition
    -> (st -> st -> SBool)                  -- ^ Transition relation
    -> (st -> SBool)                        -- ^ Goal to cover, i.e., we find a set of transitions that satisfy this predicate.
    -> IO (Either String (Int, [res]))      -- ^ Either a result, or a satisfying path of given length and intermediate observations.
bmcRefuteWith = bmcWith Refute

-- | Covers using bounded model checking, using the default solver. This version tries to cover the goal
-- in a depth-first fashion. Note that this method can find a cover, but will never find determine that a goal is
-- not coverable. If it finds a cover, it will be the shortest, though not necessarily unique.
bmcCover :: (Queriable IO st, res ~ QueryResult st)
    => Maybe Int                            -- ^ Optional bound
    -> Bool                                 -- ^ Verbose: prints iteration count
    -> Symbolic ()                          -- ^ Setup code, if necessary. (Typically used for 'Data.SBV.setOption' calls. Pass @return ()@ if not needed.)
    -> (st -> SBool)                        -- ^ Initial condition
    -> (st -> st -> SBool)                  -- ^ Transition relation
    -> (st -> SBool)                        -- ^ Goal to cover, i.e., we find a set of transitions that satisfy this predicate.
    -> IO (Either String (Int, [res]))      -- ^ Either a result, or a satisfying path of given length and intermediate observations.
bmcCover = bmcCoverWith defaultSMTCfg

-- | Cover using a given solver.
bmcCoverWith :: (Queriable IO st, res ~ QueryResult st)
    => SMTConfig                            -- ^ Solver to use
    -> Maybe Int                            -- ^ Optional bound
    -> Bool                                 -- ^ Verbose: prints iteration count
    -> Symbolic ()                          -- ^ Setup code, if necessary. (Typically used for 'Data.SBV.setOption' calls. Pass @return ()@ if not needed.)
    -> (st -> SBool)                        -- ^ Initial condition
    -> (st -> st -> SBool)                  -- ^ Transition relation
    -> (st -> SBool)                        -- ^ Goal to cover, i.e., we find a set of transitions that satisfy this predicate.
    -> IO (Either String (Int, [res]))      -- ^ Either a result, or a satisfying path of given length and intermediate observations.
bmcCoverWith = bmcWith Cover

-- | Bounded model checking, configurable with the solver. Not exported; use 'bmcCover', 'bmcRefute' and their "with" variants.
bmcWith :: (Queriable IO st, res ~ QueryResult st)
        => BMCKind -> SMTConfig -> Maybe Int -> Bool -> Symbolic () -> (st -> SBool) -> (st -> st -> SBool) -> (st -> SBool)
        -> IO (Either String (Int, [res]))
bmcWith kind cfg mbLimit chatty setup initial trans goal
  = runSMTWith cfg $ do setup
                        query $ do state <- create
                                   constrain $ initial state
                                   go 0 state []
   where (what, badResult, goodResult) = case kind of
                                           Cover  -> ("BMC Cover",  "Cover can't be established.", "Satisfying")
                                           Refute -> ("BMC Refute", "Cannot refute the claim.",    "Failing")

         go i _ _
          | Just l <- mbLimit, i >= l
          = return $ Left $ what ++ " limit of " ++ show l ++ " reached. " ++ badResult

         go i curState sofar = do when chatty $ io $ putStrLn $ what ++ ": Iteration: " ++ show i

                                  push 1

                                  let g = goal curState
                                  constrain $ case kind of
                                                Cover  ->      g   -- Covering the goal
                                                Refute -> sNot g   -- Trying to refute the goal, so satisfy the negation

                                  cs <- checkSat

                                  case cs of
                                    DSat{} -> error $ what ++ ": Solver returned an unexpected delta-sat result."
                                    Sat    -> do when chatty $ io $ putStrLn $ what ++ ": " ++ goodResult ++ " state found at iteration " ++ show i
                                                 ms <- mapM project (curState : sofar)
                                                 return $ Right (i, reverse ms)
                                    Unk    -> do when chatty $ io $ putStrLn $ what ++ ": Backend solver said unknown at iteration " ++ show  i
                                                 return $ Left $ what ++ ": Solver said unknown in iteration " ++ show i
                                    Unsat  -> do pop 1
                                                 nextState <- create
                                                 constrain $ curState `trans` nextState
                                                 go (i+1) nextState (curState : sofar)
