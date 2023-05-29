-----------------------------------------------------------------------------
-- |
-- Module    : Data.SBV.Tools.WeakestPreconditions
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- A toy imperative language with a proof system based on Dijkstra's weakest
-- preconditions methodology to establish partial/total correctness proofs.
--
-- See @Documentation.SBV.Examples.WeakestPreconditions@ directory for
-- several example proofs.
-----------------------------------------------------------------------------

{-# LANGUAGE FlexibleContexts       #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE NamedFieldPuns         #-}
{-# LANGUAGE ScopedTypeVariables    #-}
{-# LANGUAGE TypeFamilies           #-}
{-# LANGUAGE TypeOperators          #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module Data.SBV.Tools.WeakestPreconditions (
        -- * Programs and statements
          Program(..), Stmt(..), assert, stable

        -- * Invariants, measures, and stability
        , Invariant, Measure, Stable

        -- * Verification conditions
        , VC(..)

        -- * Result of a proof
        , ProofResult(..)

        -- * Configuring the WP engine
        , WPConfig(..), defaultWPCfg

        -- * Checking WP correctness
        , wpProve, wpProveWith

        -- * Concrete runs of programs
        , traceExecution, Status(..)
        ) where

import Data.List   (intercalate)
import Data.Maybe  (fromJust, isJust, isNothing)

import Control.Monad (when)

import Data.SBV
import Data.SBV.Control

-- | A program over a state is simply a statement, together with
-- a pre-condition capturing environmental assumptions and
-- a post-condition that states its correctness. In the usual
-- Hoare-triple notation, it captures:
--
--   @ {precondition} program {postcondition} @
--
-- We also allow for a stability check, which is ensured at
-- every assignment statement to deal with ghost variables.
-- In general, this is useful for making sure what you consider
-- as "primary inputs" remain unaffected. Of course, you can
-- also put any arbitrary condition you want to check that you
-- want performed for each 'Assign' statement.
--
-- Note that stability is quite a strong condition: It is intended
-- to capture constants that never change during execution. So,
-- if you have a program that changes an input temporarily but
-- always restores it at the end, it would still fail the stability
-- condition.
--
-- The 'setup' field is reserved for any symbolic code you might
-- want to run before the proof takes place, typically for calls
-- to 'Data.SBV.setOption'. If not needed, simply pass @return ()@.
-- For an interesting use case where we use setup to axiomatize
-- the spec, see "Documentation.SBV.Examples.WeakestPreconditions.Fib"
-- and "Documentation.SBV.Examples.WeakestPreconditions.GCD".
data Program st = Program { setup         :: Symbolic ()  -- ^ Any set-up required
                          , precondition  :: st -> SBool  -- ^ Environmental assumptions
                          , program       :: Stmt st      -- ^ Program
                          , postcondition :: st -> SBool  -- ^ Correctness statement
                          , stability     :: Stable st    -- ^ Each assignment must satisfy stability
                          }

-- | A stability condition captures a primary input that does not change. Use 'stable'
-- to create elements of this type.
type Stable st = [st -> st -> (String, SBool)]

-- | An invariant takes a state and evaluates to a boolean.
type Invariant st = st -> SBool

-- | A measure takes the state and returns a sequence of integers. The ordering
-- will be done lexicographically over the elements.
type Measure st = st -> [SInteger]

-- | A statement in our imperative program, parameterized over the state.
data Stmt st = Skip                                                                     -- ^ Skip, do nothing.
             | Abort String                                                             -- ^ Abort execution. The name is for diagnostic purposes.
             | Assign (st -> st)                                                        -- ^ Assignment: Transform the state by a function.
             | If (st -> SBool) (Stmt st) (Stmt st)                                     -- ^ Conditional: @If condition thenBranch elseBranch@.
             | While String (Invariant st) (Maybe (Measure st)) (st -> SBool) (Stmt st) -- ^ A while loop: @While name invariant measure condition body@.
                                                                                        -- The string @name@ is merely for diagnostic purposes.
                                                                                        -- If the measure is 'Nothing', then only partial correctness
                                                                                        -- of this loop will be proven.
             | Seq [Stmt st]                                                            -- ^ A sequence of statements.

-- | An 'assert' is a quick way of ensuring some condition holds. If it does,
-- then it's equivalent to 'Skip'. Otherwise, it is equivalent to 'Abort'.
assert :: String -> (st -> SBool) -> Stmt st
assert nm cond = If cond Skip (Abort nm)

-- | Stability: A call of the form @stable "f" f@ means the value of the field @f@
-- does not change during any assignment. The string argument is for diagnostic
-- purposes only. Note that we use strong-equality here, so if the program
-- is manipulating floats, we don't get a false-positive on @NaN@ and also
-- not miss @+0@ and @-@@ changes.
stable :: EqSymbolic a => String -> (st -> a) -> st -> st -> (String, SBool)
stable nm f before after = (nm, f before .=== f after)

-- | Are all the termination measures provided?
isTotal :: Stmt st -> Bool
isTotal Skip                = True
isTotal (Abort _)           = True
isTotal (Assign _)          = True
isTotal (If _ tb fb)        = all isTotal [tb, fb]
isTotal (While _ _ msr _ s) = isJust msr && isTotal s
isTotal (Seq ss)            = all isTotal ss

-- | A verification condition. Upon failure, each 'VC' carries enough state and diagnostic information
-- to indicate what particular proof obligation failed for further debugging.
data VC st m = BadPrecondition          st                  -- ^ The precondition doesn't hold. This can only happen in 'traceExecution'.
             | BadPostcondition         st st               -- ^ The postcondition doesn't hold
             | Unstable          String st st               -- ^ Stability condition is violated
             | AbortReachable    String st st               -- ^ The named abort condition is reachable
             | InvariantPre      String st                  -- ^ Invariant doesn't hold upon entry to the named loop
             | InvariantMaintain String st st               -- ^ Invariant isn't maintained by the body
             | MeasureBound      String (st, [m])           -- ^ Measure cannot be shown to be non-negative
             | MeasureDecrease   String (st, [m]) (st, [m]) -- ^ Measure cannot be shown to decrease through each iteration

-- | Helper function to display VC's nicely
dispVC :: String -> [(String, String)] -> String
dispVC tag flds = intercalate "\n" $ col tag : map showField flds
  where col "" = ""
        col t  = t ++ ":"

        showField (t, c) = intercalate "\n" $ zipWith mark [(1::Int)..] (lines c)
           where tt   = if null t then "" else col t ++ " "
                 sp   = replicate (length tt) ' '
                 mark i s = "  " ++ (if i == 1 then tt else sp) ++ s

-- If a measure is a singleton, just show the number. Otherwise as a list:
showMeasure :: Show a => [a] -> String
showMeasure [x] = show x
showMeasure xs  = show xs

-- | Show instance for VC's
instance (Show st, Show m) => Show (VC st m) where
  show (BadPrecondition   s)                    = dispVC "Precondition fails"
                                                         [("", show s)]
  show (BadPostcondition  s1 s2)                = dispVC "Postcondition fails"
                                                         [ ("Start", show s1)
                                                         , ("End  ", show s2)
                                                         ]
  show (Unstable          m s1 s2)              = dispVC ("Stability fails for " ++ show m)
                                                         [ ("Before", show s1)
                                                         , ("After ", show s2)
                                                         ]
  show (AbortReachable    nm s1 s2)             = dispVC ("Abort " ++ show nm ++ " condition is satisfiable")
                                                         [ ("Before", show s1)
                                                         , ("After ", show s2)
                                                         ]
  show (InvariantPre      nm s)                 = dispVC ("Invariant for loop " ++ show nm ++ " fails upon entry")
                                                         [("", show s)]
  show (InvariantMaintain nm s1 s2)             = dispVC ("Invariant for loop " ++ show nm ++ " is not maintained by the body")
                                                         [ ("Before", show s1)
                                                         , ("After ", show s2)
                                                         ]
  show (MeasureBound      nm (s, m))            = dispVC ("Measure for loop "   ++ show nm ++ " is negative")
                                                         [ ("State  ", show s)
                                                         , ("Measure", showMeasure m )
                                                         ]
  show (MeasureDecrease   nm (s1, m1) (s2, m2)) = dispVC ("Measure for loop "   ++ show nm ++ " does not decrease")
                                                         [ ("Before ", show s1)
                                                         , ("Measure", showMeasure m1)
                                                         , ("After  ", show s2)
                                                         , ("Measure", showMeasure m2)
                                                         ]

-- | The result of a weakest-precondition proof.
data ProofResult res = Proven Bool                -- ^ The property holds. If 'Bool' is 'True', then total correctness, otherwise partial.
                     | Indeterminate String       -- ^ Failed to establish correctness. Happens when the proof obligations lead to
                                                  -- the SMT solver to return @Unk@. This can happen, for instance, if you have
                                                  -- non-linear constraints, causing the solver to give up.
                     | Failed [VC res Integer]    -- ^ The property fails, failing to establish the conditions listed.

-- | 'Show' instance for proofs, for readability.
instance Show res => Show (ProofResult res) where
  show (Proven True)     = "Q.E.D."
  show (Proven False)    = "Q.E.D. [Partial: not all termination measures were provided.]"
  show (Indeterminate s) = "Indeterminate: " ++ s
  show (Failed vcs)      = intercalate "\n" $ ("Proof failure. Failing verification condition" ++ if length vcs > 1 then "s:" else ":")
                                              : map (\vc -> intercalate "\n" ["  " ++ l | l <- lines (show vc)]) vcs



-- | Checking WP based correctness
wpProveWith :: forall st res. (Show res, Mergeable st, Queriable IO st, res ~ QueryResult st) => WPConfig -> Program st -> IO (ProofResult res)
wpProveWith cfg@WPConfig{wpVerbose} Program{setup, precondition, program, postcondition, stability} =
   runSMTWith (wpSolver cfg) $ do setup
                                  query q
  where q = do start <- create

               weakestPrecondition <- wp start program (\st -> [(postcondition st, BadPostcondition start st)])

               let vcs = weakestPrecondition start

               constrain $ sNot $ precondition start .=> sAnd (map fst vcs)

               cs <- checkSat
               case cs of
                 Unk    -> Indeterminate . show <$> getUnknownReason

                 Unsat  -> do let t = isTotal program

                              if t then msg "Total correctness is established."
                                   else msg "Partial correctness is established."

                              pure $ Proven t

                 DSat{} -> pure $ Indeterminate "Unsupported: Solver returned a delta-satisfiable answer."

                 Sat    -> do let checkVC :: (SBool, VC st SInteger) -> Query [VC res Integer]
                                  checkVC (cond, vc) = do c <- getValue cond
                                                          if c
                                                             then return []   -- The VC was OK
                                                             else do vc' <- case vc of
                                                                              BadPrecondition     s                 -> BadPrecondition     <$> project s
                                                                              BadPostcondition    s1 s2             -> BadPostcondition    <$> project s1 <*> project s2
                                                                              Unstable          l s1 s2             -> Unstable          l <$> project s1 <*> project s2
                                                                              AbortReachable    l s1 s2             -> AbortReachable    l <$> project s1 <*> project s2
                                                                              InvariantPre      l s                 -> InvariantPre      l <$> project s
                                                                              InvariantMaintain l s1 s2             -> InvariantMaintain l <$> project s1 <*> project s2
                                                                              MeasureBound      l (s, m)            -> do r <- project s
                                                                                                                          v <- mapM getValue m
                                                                                                                          return $ MeasureBound l (r, v)
                                                                              MeasureDecrease   l (s1, i1) (s2, i2) -> do r1 <- project s1
                                                                                                                          v1 <- mapM getValue i1
                                                                                                                          r2 <- project s2
                                                                                                                          v2 <- mapM getValue i2
                                                                                                                          return $ MeasureDecrease l (r1, v1) (r2, v2)
                                                                     return [vc']

                              badVCs <- concat <$> mapM checkVC vcs

                              when (null badVCs) $ error "Data.SBV.proveWP: Impossible happened. Proof failed, but no failing VC found!"

                              let plu w (_:_:_) = w ++ "s"
                                  plu w _       = w

                                  m = "Following proof " ++ plu "obligation" badVCs ++ " failed:"

                              msg m
                              msg $ replicate (length m) '='

                              let disp c = mapM_ msg ["  " ++ l | l <- lines (show c)]
                              mapM_ disp badVCs

                              return $ Failed badVCs

        msg = io . when wpVerbose . putStrLn

        -- Compute the weakest precondition to establish the property:
        wp :: st -> Stmt st -> (st -> [(SBool, VC st SInteger)]) -> Query (st -> [(SBool, VC st SInteger)])

        -- Skip simply keeps the conditions
        wp _ Skip post = return post

        -- Abort is never satisfiable. The only way to have Abort's VC to pass is
        -- to run it in a precondition (either via program or in an if branch) that
        -- evaluates to false, i.e., it must not be reachable.
        wp start (Abort nm) _ = return $ \st -> [(sFalse, AbortReachable nm start st)]

        -- Assign simply transforms the state and passes on. It also checks that the
        -- stability constraints are not violated.
        wp _ (Assign f) post = return $ \st -> let st'       = f st
                                                   vcs       = map (\s -> let (nm, b) = s st st' in (b, Unstable nm st st')) stability
                                               in vcs ++ post st'

        -- Conditional: We separately collect the VCs, and predicate with the proper branch condition
        wp start (If c tb fb) post = do tWP <- wp start tb post
                                        fWP <- wp start fb post
                                        return $ \st -> let cond = c st
                                                        in   [(     cond .=> b, v) | (b, v) <- tWP st]
                                                          ++ [(sNot cond .=> b, v) | (b, v) <- fWP st]

        -- Sequencing: Simply run through the statements
        wp _     (Seq [])              post = return post
        wp start (Seq (s:ss))          post = wp start s =<< wp start (Seq ss) post

        -- While loop, where all the WP magic happens!
        wp start (While nm inv mm cond body) post = do
                st'  <- create

                let noMeasure = isNothing mm
                    m         = fromJust mm
                    curM      = m st'
                    zero      = map (const 0) curM

                    iterates   = inv st' .&&       cond st'
                    terminates = inv st' .&& sNot (cond st')


                -- Condition 1: Invariant must hold prior to loop entry
                invHoldsPrior <- wp start Skip (\st -> [(inv st, InvariantPre nm st)])

                -- Condition 2: If we iterate, invariant must be maitained by the body
                invMaintained <- wp st' body (\st -> [(iterates .=> inv st, InvariantMaintain nm st' st)])

                -- Condition 3: If we terminate, invariant must be strong enough to establish the post condition
                invEstablish <- wp st' body (const [(terminates .=> b, v) | (b, v) <- post st'])

                -- Condition 4: If we iterate, measure must always be non-negative
                measureNonNegative <- if noMeasure
                                      then return  (const [])
                                      else wp st' Skip (const [(iterates .=> curM .>= zero, MeasureBound nm (st', curM))])

                -- Condition 5: If we iterate, the measure must decrease
                measureDecreases <- if noMeasure
                                    then return  (const [])
                                    else wp st' body (\st -> let prevM = m st in [(iterates .=> prevM .< curM, MeasureDecrease nm (st', curM) (st, prevM))])

                -- Simply concatenate the VCs from all our conditions:
                return $ \st ->    invHoldsPrior      st
                                ++ invMaintained      st'
                                ++ invEstablish       st'
                                ++ measureNonNegative st'
                                ++ measureDecreases   st'

-- | Check correctness using the default solver. Equivalent to @'wpProveWith' 'defaultWPCfg'@.
wpProve :: (Show res, Mergeable st, Queriable IO st, res ~ QueryResult st) => Program st -> IO (ProofResult res)
wpProve = wpProveWith defaultWPCfg

-- | Configuration for WP proofs.
data WPConfig = WPConfig { wpSolver  :: SMTConfig   -- ^ SMT Solver to use
                         , wpVerbose :: Bool        -- ^ Should we be chatty?
                         }

-- | Default WP configuration: Uses the default solver, and is not verbose.
defaultWPCfg :: WPConfig
defaultWPCfg = WPConfig { wpSolver  = defaultSMTCfg
                        , wpVerbose = False
                        }

-- * Concrete execution of a program

-- | Tracking locations: Either a line (sequence) number, or an iteration count
data Location = Line      Int
              | Iteration Int

-- | A 'Loc' is a nesting of locations. We store this in reverse order.
type Loc = [Location]

-- | Are we in a good state, or in a stuck state?
data Status st = Good st               -- ^ Execution finished in the given state.
               | Stuck (VC st Integer) -- ^ Execution got stuck, with the failing VC

-- | Show instance for 'Status'
instance Show st => Show (Status st) where
  show (Good st)  = "Program terminated successfully. Final state:\n" ++ intercalate "\n" ["  " ++ l | l <- lines (show st)]
  show (Stuck vc) = "Program is stuck.\n" ++ show vc

-- | Trace the execution of a program, starting from a sufficiently concrete state. (Sufficiently here means that
-- all parts of the state that is used uninitialized must have concrete values, i.e., essentially the inputs.
-- You can leave the "temporary" variables initialized by the program before use undefined or even symbolic.)
-- The return value will have a 'Good' state to indicate the program ended successfully, if that is the case. The
-- result will be 'Stuck' if the program aborts without completing: This can happen either by executing an 'Abort'
-- statement, or some invariant gets violated, or if a metric fails to go down through a loop body.
traceExecution :: forall st. Show st
               => Program st            -- ^ Program
               -> st                    -- ^ Starting state. It must be fully concrete.
               -> IO (Status st)
traceExecution Program{precondition, program, postcondition, stability} start = do

                status <- if unwrap [] "checking precondition" (precondition start)
                          then go [Line 1] program =<< step [] start "*** Precondition holds, starting execution:"
                          else giveUp start (BadPrecondition start) "*** Initial state does not satisfy the precondition:"

                case status of
                  s@Stuck{} -> return s
                  Good end  -> if unwrap [] "checking postcondition" (postcondition end)
                               then step [] end "*** Program successfully terminated, post condition holds of the final state:"
                               else giveUp end (BadPostcondition start end) "*** Failed, final state does not satisfy the postcondition:"

  where sLoc :: Loc -> String -> String
        sLoc l m
          | null l = m
          | True   = "===> [" ++ intercalate "." (map sh (reverse l)) ++ "] " ++ m
          where sh (Line  i)     = show i
                sh (Iteration i) = "{" ++ show i ++ "}"

        step :: Loc -> st -> String -> IO (Status st)
        step l st m = do putStrLn $ sLoc l m
                         printST st
                         return $ Good st

        stop :: Loc -> VC st Integer -> String -> IO (Status st)
        stop l vc m = do putStrLn $ sLoc l m
                         return $ Stuck vc

        giveUp :: st -> VC st Integer -> String -> IO (Status st)
        giveUp st vc m = do r <- stop [] vc m
                            printST st
                            return r

        dispST :: st -> String
        dispST st = intercalate "\n" ["  " ++ l | l <- lines (show st)]

        printST :: st -> IO ()
        printST = putStrLn . dispST

        unwrap :: SymVal a => Loc -> String -> SBV a -> a
        unwrap l m v = case unliteral v of
                         Just c  -> c
                         Nothing -> error $ unlines [ ""
                                                    , "*** Data.SBV.WeakestPreconditions.traceExecution:"
                                                    , "***"
                                                    , "***    Unable to extract concrete value:"
                                                    , "***      "  ++ sLoc l m
                                                    , "***"
                                                    , "*** Make sure the starting state is fully concrete and"
                                                    , "*** there are no uninterpreted functions in play!"
                                                    ]

        go :: Loc -> Stmt st -> Status st -> IO (Status st)
        go _   _ s@Stuck{}  = return s
        go loc p (Good  st) = analyze p
          where analyze Skip = step loc st "Skip"

                analyze (Abort nm) = stop loc (AbortReachable nm start st) $ "Abort command executed, labeled: " ++ show nm

                analyze (Assign f) = case [nm | s <- stability, let (nm, b) = s st st', not (unwrap loc ("evaluation stability condition " ++ show nm) b)] of
                                       []  -> step loc st' "Assign"
                                       nms -> let comb = intercalate ", " nms
                                                  bad  = Unstable comb st st'
                                              in stop loc bad $ "Stability condition fails for: " ++ show comb
                    where st' = f st

                analyze (If c tb eb)
                  | branchTrue       = go (Line 1 : loc) tb =<< step loc st "Conditional, taking the \"then\" branch"
                  | True             = go (Line 2 : loc) eb =<< step loc st "Conditional, taking the \"else\" branch"
                  where branchTrue = unwrap loc "evaluating the test condition" (c st)

                analyze (Seq stmts)  = walk stmts 1 (Good st)
                  where walk []     _ is = return is
                        walk (s:ss) c is = walk ss (c+1) =<< go (Line c : loc) s is

                analyze (While loopName invariant mbMeasure condition body)
                   | currentInvariant st
                   = while 1 st Nothing (Good st)
                   | True
                   = stop loc (InvariantPre loopName st) $ tag "invariant fails to hold prior to loop entry"
                   where tag s = "Loop " ++ show loopName ++ ": " ++ s

                         hasMeasure = isJust mbMeasure
                         measure    = fromJust mbMeasure

                         currentCondition = unwrap loc (tag  "evaluating the while condition") . condition
                         currentMeasure   = map (unwrap loc (tag  "evaluating the measure"))   . measure
                         currentInvariant = unwrap loc (tag  "evaluating the invariant")       . invariant

                         while _ _      _      s@Stuck{}  = return s
                         while c prevST mbPrev (Good  is)
                           | not (currentCondition is)
                           = step loc is $ tag "condition fails, terminating"
                           | not (currentInvariant is)
                           = stop loc (InvariantMaintain loopName prevST is) $ tag "invariant fails to hold in iteration " ++ show c
                           | hasMeasure && mCur < zero
                           = stop loc (MeasureBound loopName (is, mCur)) $ tag "measure must be non-negative, evaluated to: " ++ show mCur
                           | hasMeasure, Just mPrev <- mbPrev, mCur >= mPrev
                           = stop loc (MeasureDecrease loopName (prevST, mPrev) (is, mCur)) $ tag $ "measure failed to decrease, prev = " ++ show mPrev ++ ", current = " ++ show mCur
                           | True
                           = do nextState <- go (Iteration c : loc) body =<< step loc is (tag "condition holds, executing the body")
                                while (c+1) is (Just mCur) nextState
                           where mCur = currentMeasure is
                                 zero = map (const 0) mCur

{- HLint ignore traceExecution "Use fromMaybe" -}
