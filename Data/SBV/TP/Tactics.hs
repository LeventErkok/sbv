-----------------------------------------------------------------------------
-- |
-- Module    : Data.SBV.TP.Tactics
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- A tactic-based interface for theorem proving, complementing the
-- calculational proof style in "Data.SBV.TP". Unlike traditional
-- tactic systems (Coq, Lean, Isabelle), these tactics work without
-- AST inspection since SBV formulas are opaque handles to the SMT solver.
--
-- The tactics focus on:
--   * Managing proof context (assumptions and lemmas)
--   * Manipulating goal stack
--   * Invoking SMT solver with different contexts
--   * Structuring complex proofs
-----------------------------------------------------------------------------

{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE NamedFieldPuns     #-}
{-# LANGUAGE RecordWildCards    #-}
{-# LANGUAGE ScopedTypeVariables #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module Data.SBV.TP.Tactics (
    -- * Core types
    Tactic, ProofState(..), Goal(..)

    -- * Running tactics
  , theorem, theoremWith
  , runTactic, evalTactic

    -- * Goal inspection
  , goals, numGoals, currentGoal, showGoals

    -- * Basic tactics
  , auto, autoUsing
  , using, withLemmas

    -- * Goal manipulation
  , focus, swap, defer, rotate

    -- * Case analysis (user-provided)
  , splitOn, considerCases

    -- * Tactic combinators
  , (>>), (>=>)
  , tryTactic, tryAll
  , allGoals
  , done, isDone

    -- * Re-exports from TP
  , module Data.SBV.TP
  ) where

import Prelude hiding ((>>))
import qualified Prelude as P

import Data.SBV hiding (rotate)
import Data.SBV.TP
import Data.SBV.TP.Utils (ProofObj(..), getTPConfig)

import Control.Monad.Trans (liftIO)
import Data.List (intercalate)

-- | A named goal to be proven
data Goal = Goal
  { goalId      :: Int
  , goalName    :: String
  , goalClaim   :: SBool
  , goalContext :: [(String, SBool)]  -- named assumptions
  } deriving (Show)

-- | Proof state tracking goals, assumptions, and available lemmas
data ProofState = ProofState
  { psGoals      :: [Goal]        -- Goals to prove (head is current)
  , psNextId     :: Int           -- Counter for generating goal IDs
  , psLemmas     :: [ProofObj]    -- Available lemmas
  , psGlobalCtx  :: [(String, SBool)]  -- Global assumptions
  , psTrace      :: [String]      -- Trace for debugging/output
  }

instance Show ProofState where
  show ProofState{..} = unlines
    [ "ProofState {"
    , "  psGoals = " ++ show psGoals
    , "  psNextId = " ++ show psNextId
    , "  psLemmas = [" ++ intercalate ", " (map proofName psLemmas) ++ "]"
    , "  psGlobalCtx = " ++ show (map fst psGlobalCtx)
    , "  psTrace = " ++ show psTrace
    , "}"
    ]

-- | A tactic transforms proof state, possibly failing with an error message
type Tactic = ProofState -> TP (Either String ProofState)

-- * Running tactics

-- | Create initial proof state from a goal
initialState :: String -> SBool -> ProofState
initialState name claim = ProofState
  { psGoals      = [Goal 0 name claim []]
  , psNextId     = 1
  , psGlobalCtx  = []
  , psLemmas     = []
  , psTrace      = []
  }

-- | Run a tactic and return the final proof state
runTactic :: Tactic -> ProofState -> TP (Either String ProofState)
runTactic = id

-- | Run a tactic and extract the result, erroring on failure
evalTactic :: Tactic -> ProofState -> TP ProofState
evalTactic tac st = do
  result <- runTactic tac st
  case result of
    Left err -> error $ "Tactic failed: " ++ err
    Right st' -> pure st'

-- | Prove a theorem using tactics, with default config
theorem :: Proposition a => String -> a -> Tactic -> TP (Proof a)
theorem name prop tac = getTPConfig P.>>= \cfg -> theoremWith cfg name prop tac

-- | Prove a theorem using tactics, with specific config
theoremWith :: Proposition a => SMTConfig -> String -> a -> Tactic -> TP (Proof a)
theoremWith cfg name prop tac = do
  let goal = quantifiedBool prop
      st0  = initialState name goal

  -- Run the tactic
  stFinal <- evalTactic tac st0

  -- Check all goals are solved
  case psGoals stFinal of
    [] -> do
      -- All goals proven! Now create the actual proof using lemma infrastructure
      -- We build a trivial proof directly with the proposition
      lemmaWith cfg name prop []

    remainingGoals -> do
      let goalNames = intercalate ", " [goalName g | g <- remainingGoals]
      error $ unlines
        [ "Tactic proof incomplete!"
        , "Remaining goals: " ++ goalNames
        , ""
        , "Use 'showGoals' to see what's left to prove."
        ]

-- * Goal inspection

-- | Get all current goals
goals :: Tactic
goals st = pure $ Right st  -- Identity tactic, user can inspect the state

-- | Get number of remaining goals
numGoals :: ProofState -> Int
numGoals ProofState{psGoals} = length psGoals

-- | Get the current goal (if any)
currentGoal :: ProofState -> Maybe Goal
currentGoal ProofState{psGoals = []} = Nothing
currentGoal ProofState{psGoals = g:_} = Just g

-- | Display current goals (for debugging)
showGoals :: Tactic
showGoals st@ProofState{psGoals} = do
  liftIO $ case psGoals of
    [] -> putStrLn "No goals remaining."
    gs -> do
      putStrLn $ "Goals (" ++ show (length gs) ++ "):"
      mapM_ printGoal (zip [(1::Int)..] gs)
  pure $ Right st
  where
    printGoal (i, Goal{goalName, goalContext}) = do
      putStrLn $ "  " ++ show i ++ ". " ++ goalName
      case goalContext of
        [] -> pure ()
        ctx -> do
          putStrLn "     Assumptions:"
          mapM_ (\(n, _) -> putStrLn $ "       " ++ n) ctx

-- * Basic tactics

-- | Try to prove the current goal using the SMT solver with available context
auto :: Tactic
auto st@ProofState{psGoals = []} = pure $ Right st
auto st@ProofState{psGoals = Goal{..} : rest, psGlobalCtx, psLemmas} = do
  -- Build the formula to prove: globalCtx /\ goalContext => goalClaim
  let allAssumptions = map snd psGlobalCtx ++ map snd goalContext
      toProve = sAnd allAssumptions .=> goalClaim

  -- Prove it using lemma infrastructure with available lemmas
  let uniqueName = "tactic_auto_" ++ goalName
  _ <- lemma uniqueName toProve psLemmas

  -- If we get here, the proof succeeded
  pure $ Right st { psGoals = rest
                  , psTrace = psTrace st ++ ["Solved: " ++ goalName]
                  }

-- | Try to prove using specific lemmas
autoUsing :: [Proof a] -> Tactic
autoUsing proofs st =
  let lemmas = map proofOf proofs
      st' = st { psLemmas = psLemmas st ++ lemmas }
  in auto st'

-- | Add lemmas to the proof context
using :: [Proof a] -> Tactic
using proofs st =
  pure $ Right st { psLemmas = psLemmas st ++ map proofOf proofs }

-- | Synonym for 'using'
withLemmas :: [Proof a] -> Tactic
withLemmas = using

-- * Goal manipulation

-- | Focus on the nth goal (1-indexed)
focus :: Int -> Tactic -> Tactic
focus n tac st@ProofState{psGoals}
  | n < 1 || n > length psGoals =
      pure $ Left $ "focus: invalid goal number " ++ show n
  | otherwise =
      case splitAt (n - 1) psGoals of
        (before, g : after) -> do
          let st' = st { psGoals = g : before ++ after }
          result <- tac st'
          case result of
            Left err -> pure $ Left err
            Right st''@ProofState{psGoals = goals'} -> do
              -- Restore goal order (approximately - current goal goes back to position n)
              let (remaining, rest') = case goals' of
                                          [] -> ([], [])
                                          r:rs -> ([r], rs)
              pure $ Right st'' { psGoals = before ++ remaining ++ after ++ rest' }
        _ -> pure $ Left "focus: invalid goal index"

-- | Swap the first two goals
swap :: Tactic
swap st@ProofState{psGoals = g1 : g2 : rest} =
  pure $ Right st { psGoals = g2 : g1 : rest }
swap _ = pure $ Left "swap: need at least 2 goals"

-- | Move current goal to the end
defer :: Tactic
defer st@ProofState{psGoals = []} = pure $ Right st
defer st@ProofState{psGoals = g : rest} =
  pure $ Right st { psGoals = rest ++ [g] }

-- | Rotate goals by n positions
rotate :: Int -> Tactic
rotate n st@ProofState{psGoals}
  | null psGoals = pure $ Right st
  | otherwise =
      let n' = n `mod` length psGoals
          (front, back) = splitAt n' psGoals
      in pure $ Right st { psGoals = back ++ front }

-- * Case analysis

-- | Split on user-provided cases. Each case becomes a separate goal.
-- Also adds an exhaustiveness goal to ensure the cases cover all possibilities.
splitOn :: [(String, SBool)] -> Tactic
splitOn _ ProofState{psGoals = []} =
  pure $ Left "splitOn: no goal to split"
splitOn [] _ =
  pure $ Left "splitOn: empty case list"
splitOn caseList st@ProofState{psGoals = Goal{..} : rest, ..} =
  -- Create a goal for each case
  let makeGoal idx (caseName, condition) =
        Goal { goalId = psNextId + idx
             , goalName = goalName ++ "_case_" ++ caseName
             , goalClaim = goalClaim
             , goalContext = goalContext ++ [(caseName, condition)]
             }
      caseGoals = [makeGoal i c | (i, c) <- zip [0..] caseList]

      -- Exhaustiveness check: at least one case must hold
      exhaustivenessGoal = Goal
        { goalId = psNextId + length caseList
        , goalName = goalName ++ "_exhaustive"
        , goalClaim = sOr [cond | (_, cond) <- caseList]
        , goalContext = goalContext
        }

  in pure $ Right st { psGoals = caseGoals ++ [exhaustivenessGoal] ++ rest
                     , psNextId = psNextId + length caseList + 1
                     }

-- | Split into cases with individual tactics for each
-- Automatically proves the exhaustiveness goal using auto.
considerCases :: [(String, SBool, Tactic)] -> Tactic
considerCases [] _ = pure $ Left "considerCases: empty case list"
considerCases caseList st = do
  -- First split on the conditions (this creates case goals + exhaustiveness goal)
  let conditions = [(name, cond) | (name, cond, _) <- caseList]
  result <- splitOn conditions st

  case result of
    Left err -> pure $ Left err
    Right st' -> do
      -- Now apply each tactic to its corresponding goal
      let tactics = [tac | (_, _, tac) <- caseList]
      st'' <- applyTacticsToGoals tactics st'
      case st'' of
        Left err -> pure $ Left err
        Right st''' ->
          -- Finally, prove the exhaustiveness goal with auto
          auto st'''
  where
    applyTacticsToGoals :: [Tactic] -> Tactic
    applyTacticsToGoals [] st' = pure $ Right st'
    applyTacticsToGoals (tac : tacs) st' = do
      result <- tac st'
      case result of
        Left err -> pure $ Left err
        Right st'' -> applyTacticsToGoals tacs st''

-- * Tactic combinators

-- | Sequential composition (specialized to Tactic)
(>>) :: Tactic -> Tactic -> Tactic
t1 >> t2 = \st -> do
  result <- t1 st
  case result of
    Left err -> pure $ Left err
    Right st' -> t2 st'

infixl 1 >>

-- | Kleisli composition for tactics
(>=>) :: Tactic -> Tactic -> Tactic
(>=>) = (>>)

infixl 1 >=>

-- | Try a tactic, but don't fail if it doesn't work
tryTactic :: Tactic -> Tactic
tryTactic tac st = do
  result <- tac st
  case result of
    Left _ -> pure $ Right st  -- Ignore failure
    Right st' -> pure $ Right st'

-- | Try multiple tactics in order, taking the first that succeeds
tryAll :: [Tactic] -> Tactic
tryAll [] _ = pure $ Left "tryAll: all tactics failed"
tryAll (t : ts) st = do
  result <- t st
  case result of
    Right st' -> pure $ Right st'
    Left _ -> tryAll ts st

-- | Apply a tactic to all current goals
allGoals :: Tactic -> Tactic
allGoals _ st@ProofState{psGoals = []} = pure $ Right st
allGoals tac st@ProofState{psGoals = origGoals} = do
  -- Apply tactic to first goal
  result <- tac st
  case result of
    Left err -> pure $ Left err
    Right st'@ProofState{psGoals = newGoals} ->
      -- If there are more goals, recurse
      if length newGoals < length origGoals
      then allGoals tac st'  -- A goal was solved, continue
      else pure $ Right st'  -- No progress on current goal, stop

-- | Check if all goals are solved
isDone :: ProofState -> Bool
isDone ProofState{psGoals = []} = True
isDone _ = False

-- | Succeed only if all goals are solved
done :: Tactic
done st@ProofState{psGoals = []} = pure $ Right st
done st = pure $ Left $ "done: " ++ show (numGoals st) ++ " goal(s) remaining"
