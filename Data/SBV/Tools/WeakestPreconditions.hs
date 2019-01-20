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
-- See @Documentation.SBV.Examples.WeakestPreconditions@ directory for
-- several example proofs.
-----------------------------------------------------------------------------

{-# LANGUAGE FlexibleContexts       #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE NamedFieldPuns         #-}
{-# LANGUAGE ScopedTypeVariables    #-}

module Data.SBV.Tools.WeakestPreconditions (
        -- * Programs and statements
          Program(..), Stmt(..)

        -- * Invariants and measures
        , Invariant, Measure

        -- * Result of a proof
        , ProofResult(..)

        -- * Checking WP total correctness
        , wpProve, wpProveWith, WPConfig(..), defaultWPCfg

        -- * Tracing concrete execution
        , Status(..), traceExecution
        ) where

import Data.List   (intercalate)
import Data.Maybe  (fromMaybe)

import Control.Monad (when, unless, void)

import Data.SBV
import Data.SBV.Control

-- | A Program over a state is simply a statement, together with
-- a pre-condition capturing environmental assumptions and
-- a post-condition that states its correctness. In the usual
-- Hoare-triple notation, it captures:
--
--   @
--     {precondition} program {postcondition}
--   @
data Program st = Program { precondition  :: st -> SBool   -- ^ Environmental assumptions
                          , program       :: Stmt st       -- ^ Program
                          , postcondition :: st -> SBool   -- ^ Correctness statement
                          }

-- | A statement in our imperative program, parameterized over the state.
data Stmt st = Skip                                                                -- ^ Skip, do nothing.
             | Abort                                                               -- ^ Abort execution.
             | Assign (st -> st)                                                   -- ^ Assignment: Transform the state by a function.
             | If (st -> SBool) (Stmt st) (Stmt st)                                -- ^ Conditional: @If condition thenBranch elseBranch@.
             | While String (st -> SBool) (st -> SInteger) (st -> SBool) (Stmt st) -- ^ A while loop: @While name invariant measure condition body@.
                                                                                   -- The string @name@ is merely for diagnostic purposes.
             | Seq [Stmt st]                                                       -- ^ A sequence of statements.

-- | The result of a weakest-precondition proof.
data ProofResult res = Proven                     -- ^ The property holds, and termination is guaranteed.
                     | Indeterminate String       -- ^ The property fails, but no causing start state is found.
                                                  --   This typically happens if the loop invariants are not strong enough.
                     | Failed String res res      -- ^ The property fails. The string is the reason for failure, and the
                                                  --   two @res@ values are the starting and ending states, respectively.

-- | 'Show' instance for proofs, for readability.
instance Show res => Show (ProofResult res) where
  show Proven             = "Q.E.D."
  show (Indeterminate s)  = "Indeterminate: " ++ s
  show (Failed s beg end) = intercalate "\n" [ "Proof failure: "++ s
                                             , "Starting state:"
                                             , intercalate "\n" ["  " ++ l | l <- lines (show beg)]
                                             , "Failed in state:"
                                             , intercalate "\n" ["  " ++ l | l <- lines (show end)]
                                             ]

-- | An invariant takes a state and evaluates to a boolean.
type Invariant st = st -> SBool

-- | A measure takes the state and returns an integer valued metric.
type Measure st = st -> SInteger

-- | Checking WP based correctness
proveWP :: forall st res. (Show st, Mergeable st, Queriable IO st res) => WPConfig -> Program st -> IO (ProofResult res)
proveWP cfg@WPConfig{wpVerbose} prog@Program{precondition, program, postcondition} = runSMTWith (wpSolver cfg) $ query $ do

        weakestPrecondition <- wp program postcondition

        -- The program is correct if we can prove the precondition
        -- implies the post-condition for all starting states
        let correctness st = precondition st .=> weakestPrecondition st

        -- As usual, assert the negation of the requirement and do a check-sat:
        start <- create
        constrain $ sNot (correctness start)

        cs <- checkSat
        case cs of
          Unk   -> Indeterminate . show <$> getUnknownReason
          Unsat -> do msg "Total correctness is established."
                      return Proven
          Sat   -> do os <- getObservables

                      let plu w (_:_:_) = w ++ "s"
                          plu w _       = w

                      unless (null os) $ do let m = "Following proof " ++ plu "obligation" os ++ " failed: "
                                            msg m
                                            msg $ replicate (length m) '='
                                            mapM_ (msg . ("  " ++) . fst) os

                      startState  <- project start
                      lStartState <- embed   startState
                      finalState  <- io $ traceExecution cfg{wpVerbose=False} prog lStartState

                      let giveUp endState s = do lEndState <- project endState
                                                 return $ Failed s startState lEndState

                      case finalState of
                        Stuck end s -> do when wpVerbose $ do msg ""
                                                              msg "Execution trace:"
                                                              msg "================"
                                                              void (io $ traceExecution cfg prog lStartState)
                                          giveUp end s
                        Good  _     -> return $ Indeterminate "Not all proof obligations were established."

  where msg = io . when wpVerbose . putStrLn

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

-- | Do a forward proof at a given bound for each one of its @While@ loops. If there are nested loops, each will be unrolled
-- @bound@ times, so the unrolling is multiplicative. In case we cannot establish correctness, try to find a starting state that
-- violates one of the conditions. This is good old bounded-model checking, but comes in quite handy.
unrollBound :: forall st res. (Show st, Show res, Mergeable st, Queriable IO st res) => WPConfig -> Int -> Program st -> IO (Maybe (ProofResult res))
unrollBound cfg@WPConfig{wpVerbose} bound prog@Program{precondition, program, postcondition} = runSMTWith (wpSolver cfg) $ query $ do

        let go :: Int -> SBool -> Stmt st -> st -> (SBool, SBool, st)
            go _ pCond Skip                            st = (pCond, sTrue,      st)
            go _ pCond Abort                           st = (pCond, sNot pCond, st)
            go _ pCond (Assign f)                      st = (pCond, sTrue,      f st)
            go b pCond (If c tb fb)                    st = ite (c st) (go b (pCond .&&       c st)  tb st)
                                                                       (go b (pCond .&& sNot (c st)) fb st)
            go _ pCond (Seq [])                        st = (pCond, sTrue, st)
            go b pCond (Seq (s:ss))                    st = let (r1, p1, st')  = go b pCond          s        st
                                                                (r2, p2, st'') = go b (pCond .&& r1) (Seq ss) st'
                                                            in (r2, p1 .&& p2, st'')
            go b pCond (While _ inv measure cond body) st = while b pCond st
               where while 0 p curST = (p .&& sNot (cond curST), sTrue, curST)    -- loop is terminating, condition must fail
                     while i p curST = let c1 = cond curST                        -- loop is executing, condition must hold
                                           c2 = inv  curST                        -- invariant must hold
                                           c3 = measure curST .>= 0               -- measure must be non-negative

                                           -- execute the body
                                           (rBody, c4, st') = go b (p .&& c1) body curST

                                           c5 = c1 .&& c2 .&& c4 .&& cond st' .&& rBody .=> measure st' .< measure curST -- measure must decrease

                                           -- execute the remainder of the loop, decrementing the counter
                                           (rRest, c6, st'') = while (i-1) rBody st'

                                       in (p .&& c1 .&& rBody .&& rRest, sAnd [c1, c2, c3, c4, c5, c6], st'')

        startState <- create

        let (reachability, constraints, endState) = go bound sTrue program startState

            pre  = precondition startState
            post = postcondition endState

        -- A good counter-example would be one that satisfies the pre-condition
        -- but fails the constraints or the endState
        constrain $ pre .&& reachability .&& (sNot constraints .|| sNot post)

        cs <- checkSat

        case cs of
          Unk   -> return Nothing
          Unsat -> return Nothing
          Sat   -> do ls <- project startState
                      es <- project endState

                      msg ". Found!\n"
                      lStartState <- embed ls
                      res <- io $ traceExecution cfg prog lStartState
                      msg ""
                      case res of
                        Good{}    -> error $ unlines [ "Impossible happened! Unrolling semantics found a bad state, but executor did not reach it."
                                                     , "Start state: " ++ show ls
                                                     , "End   state: " ++ show es
                                                     , "Please report this as a bug in SBV!"
                                                     ]

                        -- Make sure to return the final state from the trace-executor
                        -- since the SMT solver can pick an arbitrary state so long as
                        -- the constraints fail here:
                        Stuck end r -> do msg "Analysis complete. Proof failed."
                                          le <- project end
                                          return $ Just $ Failed r ls le

   where msg = when wpVerbose . io . putStrLn

-- | Try to find a good counter-example by unrolling up to 10 times
unroll :: forall st res. (Show st, Show res, Mergeable st, Queriable IO st res) => WPConfig -> String -> Program st -> IO (ProofResult res)
unroll cfg@WPConfig{wpVerbose, wpCexDepth} reason prog = go 0
  where msg     = when wpVerbose . putStrLn
        msgNoLn = when wpVerbose . putStr

        go i | i > wpCexDepth = do msg $ ".\nNo violating trace found. (Searched up to depth " ++ show wpCexDepth ++ ".)"
                                   return $ Indeterminate reason
             | True           = do let comma = if i == 0 then "" else ", "
                                   msgNoLn $ comma ++ show i
                                   mbRes <- unrollBound cfg i prog
                                   case mbRes of
                                     Nothing -> go (i+1)
                                     Just r  -> return r

-- | Configuration for WP proofs.
data WPConfig = WPConfig { wpSolver   :: SMTConfig   -- ^ SMT Solver to use
                         , wpVerbose  :: Bool        -- ^ Should we be chatty?
                         , wpCexDepth :: Int         -- ^ In case of proof failure, search for cex's upto this depth
                         }

-- | Default WP configuration.
defaultWPCfg :: WPConfig
defaultWPCfg = WPConfig { wpSolver   = defaultSMTCfg
                        , wpVerbose  = False
                        , wpCexDepth = 10
                        }

-- | Checking WP based correctness
wpProveWith :: forall st res. (Show st, Show res, Mergeable st, Queriable IO st res)
            => WPConfig              -- ^ Configuration to use
            -> Program st            -- ^ Program to check
            -> IO (ProofResult res)
wpProveWith cfg@WPConfig{wpVerbose} prog = do

        let msg     = when wpVerbose . putStrLn
            msgNoLn = when wpVerbose . putStr

        res <- proveWP cfg prog
        case res of
          Failed{}             -> do msg "\nAnalysis complete. Proof failed."
                                     return res
          Proven{}             -> return res
          Indeterminate reason -> do msg "\nAnalysis is indeterminate, not all proof obligations were established. Searching for a counter-example."
                                     msgNoLn "Looking at depth: "
                                     unroll cfg reason prog

-- | Check correctness using the default solver. Equivalent to @'wpProveWith' 'defaultWPCfg'@.
wpProve :: (Show st, Show res, Mergeable st, Queriable IO st res) => Program st -> IO (ProofResult res)
wpProve = wpProveWith defaultWPCfg

-- * Concrete execution of a program

-- | Tracking locations: Either a line (sequence) number, or an iteration count
data Location = Line Int
               | Iteration Int

-- | A 'Loc' is a nesting of locations. We store this in reverse order.
type Loc = [Location]

-- | Are we in a good state, or in a stuck state?
data Status st = Good st                -- ^ Execution finished in the given state.
               | Stuck st String        -- ^ Execution got stuck in the state, with some explanation why.

-- | Trace the execution of a program. The return value will have a 'Good' state to indicate
-- the program ended successfully, if that is the case. The result will be 'Stuck' if the program aborts without
-- completing: This can happen either by executing an 'Abort' statement, or some invariant gets violated,
-- or if a metric fails to go down through a loop body. In these latter cases, turning verbosity on will print
-- a readable trace of the program execution.
traceExecution :: forall st. Show st
               => WPConfig              -- ^ Configuration
               -> Program st            -- ^ Program
               -> st                    -- ^ Starting state
               -> IO (Status st)
traceExecution WPConfig{wpVerbose} Program{precondition, program, postcondition} start = do

                printST start

                status <- if unwrap [] "checking precondition" (precondition start)
                          then go [Line 1] program =<< step [] start "Precondition holds, starting execution"
                          else stop [] start "Initial state does not satisfy the precondition"

                case status of
                  s@Stuck{} -> return s
                  Good end  -> if unwrap [] "checking postcondition" (postcondition end)
                               then step [] end "Program successfully terminated, post condition holds of the final state"
                               else stop [] end "final state does not satisfy the postcondition"

  where msg :: String -> IO ()
        msg = when wpVerbose . putStrLn

        sLoc :: Loc -> String
        sLoc l
          | null l = "===>"
          | True   = "===> [" ++ intercalate "." (map sh (reverse l)) ++ "]"
          where sh (Line  i)     = show i
                sh (Iteration i) = "{" ++ show i ++ "}"

        step :: Loc -> st -> String -> IO (Status st)
        step l st m = do msg $ sLoc l ++ " " ++ m
                         printST st
                         return $ Good st

        stop :: Loc -> st -> String -> IO (Status st)
        stop l st m = do msg $ sLoc l ++ " " ++ m
                         return $ Stuck st m

        dispST :: st -> String
        dispST st = intercalate "\n" ["  " ++ l | l <- lines (show st)]

        printST :: st -> IO ()
        printST = msg . dispST

        unwrap :: SymVal a => Loc -> String -> SBV a -> a
        unwrap l m = fromMaybe die . unliteral
           where die = error $ "*** traceExecution: " ++ sLoc l ++ ": Failed to extract concrete value while " ++ show m

        go :: Loc -> Stmt st -> Status st -> IO (Status st)
        go _   _ s@Stuck{}  = return s
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
                   = while 1 Nothing (Good st)
                   | True
                   = stop loc st $ "Loop " ++ loopName ++ ": invariant fails to hold prior to loop entry"
                   where tag s = "Loop " ++ loopName ++ ": " ++ s

                         currentCondition = unwrap loc (tag  "evaluating the while condition") . condition
                         currentMeasure   = unwrap loc (tag  "evaluating the measure")         . measure
                         currentInvariant = unwrap loc (tag  "evaluating the invariant")       . invariant

                         while _ _      s@Stuck{}  = return s
                         while c mbPrev (Good  is)
                           | not (currentCondition is)
                           = step loc is $ tag "condition fails, terminating"
                           | not (currentInvariant is)
                           = stop loc is $ tag "invariant fails to hold in iteration " ++ show c
                           | mCur < 0
                           = stop loc is $ tag "measure must be non-negative, evaluated to: " ++ show mCur
                           | Just mPrev <- mbPrev, mCur >= mPrev
                           = stop loc is $ tag "measure failed to decrease, prev = " ++ show mPrev ++ ", current = " ++ show mCur
                           | True
                           = do nextState <- go (Iteration c : loc) body =<< step loc is (tag "condition holds, executing the body")
                                while (c+1) (Just mCur) nextState
                           where mCur = currentMeasure is
