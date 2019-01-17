-----------------------------------------------------------------------------
-- |
-- Module    : Data.SBV.Tools.WeakestPreconditions
-- Author    : Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- A toy imperative language with a proof system based on Dijkstra's weakest
-- preconditions methodology to establish total correctness proofs.
--
-- See "Documentation.SBV.Examples.ProofTools.WPSum" for an example proof.
-----------------------------------------------------------------------------

{-# LANGUAGE FlexibleContexts       #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE ScopedTypeVariables    #-}

module Data.SBV.Tools.WeakestPreconditions (
        -- * Programs and statements
          Program, Stmt(..)

        -- * Invariants and measures
        , Invariant, Measure

        -- * Result of a proof
        , ProofResult(..)

        -- * Checking WP total correctness
        , check, checkWith

        -- * Tracing concrete execution
        , Status(..), traceExecution
        ) where

import Data.List   (intercalate)
import Data.Maybe  (fromMaybe)

import Control.Monad (when, unless)

import Data.SBV
import Data.SBV.Control

-- | A Program over a state is simply a statement.
type Program st = Stmt st

-- | A statement in our imperative program, parameterized over the state.
data Stmt st = Skip                                                                -- ^ Skip, do nothing.
             | Abort                                                               -- ^ Abort execution.
             | Assign (st -> st)                                                   -- ^ Assignment: Transform the state by a function.
             | If (st -> SBool) (Stmt st) (Stmt st)                                -- ^ Conditional: @If condition thenBranch elseBranch@.
             | While String (st -> SBool) (st -> SInteger) (st -> SBool) (Stmt st) -- ^ A while loop: @While name invariant measure condition body@.
                                                                                   -- The string @name@ is merely for diagnostic purposes.
             | Seq [Stmt st]                                                       -- ^ A sequence of statements.

-- | The result of a weakest-precondition proof.
data ProofResult st = Proven                     -- ^ The property holds, and termination is guaranteed.
                    | Indeterminate String       -- ^ The property fails, but no causing start state is found.
                                                 --   This typically happens if the loop invariants are not strong enough.
                    | Failed st                  -- ^ The property fails, when the program is executed in the indicated state.

-- | 'Show' instance for proofs, for readability.
instance Show st => Show (ProofResult st) where
  show Proven            = "Q.E.D."
  show (Indeterminate s) = "Indeterminate: " ++ s
  show (Failed st)       = intercalate "\n" [ "Property fails, starting at program state:"
                                            , intercalate "\n" ["  " ++ l | l <- lines (show st)]
                                            ]

-- | An invariant takes a state and evaluates to a boolean.
type Invariant st = st -> SBool

-- | A measure takes the state and returns an integer valued metric.
type Measure st = st -> SInteger

-- | Checking correctness.
checkWith :: forall st res. (Show st, Queriable IO st res)
          => SMTConfig             -- ^ Solver to use
          -> Bool                  -- ^ Be chatty
          -> Program st            -- ^ Program to check
          -> (st -> SBool)         -- ^ Property to establish
          -> IO (ProofResult res)
checkWith cfg chatty prog prop = runSMTWith cfg $ query $ do

        weakestPrecondition <- wp prog prop

        st <- create
        constrain $ sNot (weakestPrecondition st)

        do cs <- checkSat
           case cs of
             Unk   -> Indeterminate . show <$> getUnknownReason
             Unsat -> do msg "Total correctness is established."
                         return Proven
             Sat   -> do bad <- project st
                         do os <- getObservables
                            let plu w (_:_:_) = w ++ "s"
                                plu w _       = w
                            unless (null os) $ do let m = "Following proof " ++ plu "obligation" os ++ " failed: "
                                                  msg m
                                                  msg $ replicate (length m) '='
                                                  mapM_ (msg . ("  " ++) . fst) os
                                                  msg ""
                            msg "Execution leading to failed proof obligation:"
                            msg "============================================="
                            lst <- embed bad
                            finalState <- io $ traceExecution chatty lst prog
                            case finalState of
                              Stuck end -> return $ Indeterminate $ "Program execution aborted in state: " ++ show end
                              Good  end -> case unliteral (prop end) of
                                             Nothing    -> error "Impossible happened, property evaluated to a symbolic value in the end."
                                             Just True  -> return $ Indeterminate "Not all proof obligations were established. Might need stronger invariants."
                                             Just False -> return $ Failed bad

  where msg = io . when chatty . putStrLn

        -- Compute the weakest precondition to establish the property:
        wp :: Stmt st -> (st -> SBool) -> Query (st -> SBool)
        wp Skip                 post = return post
        wp Abort                _    = return (const sFalse)
        wp (Assign f)           post = return $ post . f
        wp (If c tb fb)         post = do tWP <- wp tb post
                                          fWP <- wp fb post
                                          return $ \st -> ite (c st) (tWP st) (fWP st)
        wp (Seq [])             post = return post
        wp (Seq (s:ss))         post = wp s =<< wp (Seq ss) post
        wp (While nm inv m c s) post = do
                let tag  what = observeIf (== False) ("Loop " ++ show nm ++ ": Invariant must " ++ what)
                    term what = observeIf (== False) ("Loop " ++ show nm ++ ": Termination measure must " ++ what)
                st'  <- create
                inv' <- wp s inv
                m'   <- wp s (\st -> m st .< m st')
                return $ \st -> sAnd [ tag  "hold prior to loop entry"     $ inv st
                                     , tag  "be maintained by the loop"    $ inv st' .&&       c st'  .=> inv' st'
                                     , tag  "establish the post condition" $ inv st' .&& sNot (c st') .=> post st'
                                     , term "get smaller"                  $ inv st' .&&       c st'  .=> m' st'
                                     , term "always be non-negative"       $ inv st' .&&       c st'  .=> m  st' .>= 0
                                     ]

-- | Check correctness using the default solver.
check :: (Show st, Queriable IO st res)
      => Bool
      -> Program st
      -> (st -> SBool)
      -> IO (ProofResult res)
check = checkWith defaultSMTCfg

-- * Concrete execution of a program

-- | Tracking locations: Either a line (sequence) number, or an iteration count
data Location = Line Int
               | Iteration Int

-- | A 'Loc' is a nesting of locations. We store this in reverse order.
type Loc = [Location]

-- | Are we in a good state, or in a stuck state?
data Status st = Good st
               | Stuck st

-- | Trace the execution of a program. The return value will have a 'Good' state to indicate
-- the program ended successfully, if that is the case. The result will be 'Stuck' if the program aborts without
-- completing: This can happen either by executing an 'Abort' statement, or some invariant gets violated,
-- or if a metric fails to go down through a loop body. In these latter cases, turning verbosity on will print
-- a readable trace of the program execution.
traceExecution :: forall st. Show st
               => Bool                  -- ^ Verbose output
               -> st                    -- ^ Starting state
               -> Program st            -- ^ Program
               -> IO (Status st)
traceExecution chatty start prog = do printST start

                                      endState <- go [Line 1] prog (Good start)

                                      case endState of
                                        Good  end -> do msg "\nProgram successfully terminated in state:"
                                                        printST end
                                        Stuck end -> do msg "\nProgram execution aborted in state:"
                                                        printST end

                                      return endState
  where msg :: String -> IO ()
        msg = when chatty . putStrLn

        sLoc :: Loc -> String
        sLoc l = "===> [" ++ intercalate "." (map sh (reverse l)) ++ "]"
          where sh (Line  i)     = show i
                sh (Iteration i) = "{" ++ show i ++ "}"

        step :: Loc -> st -> String -> IO (Status st)
        step l st m = do msg $ sLoc l ++ " " ++ m
                         printST st
                         return $ Good st

        stop :: Loc -> st -> String -> IO (Status st)
        stop l st m = do msg $ sLoc l ++ " " ++ m
                         return $ Stuck st

        dispST :: st -> String
        dispST st = intercalate "\n" ["  " ++ l | l <- lines (show st)]

        printST :: st -> IO ()
        printST = msg . dispST

        unwrap :: SymVal a => Loc -> String -> SBV a -> a
        unwrap l m = fromMaybe die . unliteral
           where die = error $ "*** traceExecution: " ++ sLoc l ++ ": Failed to extract concrete value while " ++ show m

        go :: Loc -> Program st -> Status st -> IO (Status st)
        go _   _ (Stuck st) = return $ Stuck st
        go loc p (Good  st) = analyze p
          where analyze Skip         = step loc st "Skip"

                analyze Abort        = step loc st "Abort"

                analyze (Assign f)   = step loc (f st) "Assign"

                analyze (If c tb eb)
                  | branchTrue       = go (Line 1 : loc) tb =<< step loc st "Conditional, taking the \"then\" branch"
                  | True             = go (Line 2 : loc) eb =<< step loc st "Conditional, taking the \"else\" branch"
                  where branchTrue = unwrap loc "evaluating the test condition" (c st)

                analyze (Seq stmts)  = walk stmts 1 (Good st)
                  where walk []     _ is = return is
                        walk (s:ss) c is = walk ss (c+1) =<< go (Line c : loc) s is

                analyze (While loopName invariant measure condition body)
                   | currentInvariant st
                   = while 1 (currentMeasure st) (Good st)
                   | True
                   = stop loc st $ "Loop " ++ loopName ++ ": invariant fails to hold prior to loop entry"
                   where tag s = "Loop " ++ loopName ++ ": " ++ s

                         currentCondition = unwrap loc (tag  "evaluating the while condition") . condition
                         currentMeasure   = unwrap loc (tag  "evaluating the measure")         . measure
                         currentInvariant = unwrap loc (tag  "evaluating the invariant")       . invariant

                         while _ _     (Stuck is) = return $ Stuck is
                         while c mPrev (Good  is)
                           | not (currentCondition is)
                           = step loc st $ tag "condition fails, terminating"
                           | not (currentInvariant is)
                           = stop loc st $ tag "invariant fails to hold in iteration " ++ show c
                           | True
                           = do nextState <- go (Iteration c : loc) body =<< step loc is (tag "condition holds, executing the body")
                                case nextState of
                                  Stuck end -> return $ Stuck end
                                  Good  end -> let abort = stop loc end . tag
                                                   mCur  = currentMeasure   end
                                               in case (mCur <= mPrev, mCur < 0) of
                                                    (False, _    ) -> abort $ "measure failed to decrease, prev = " ++ show mPrev ++ ", current = " ++ show mCur
                                                    (True,  False) -> abort $ "measure must be non-negative, evaluated to: " ++ show mCur
                                                    (True,  True ) -> while (c+1) mCur (Good end)
