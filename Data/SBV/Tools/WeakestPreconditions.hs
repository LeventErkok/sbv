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

module Data.SBV.Tools.WeakestPreconditions (
        -- * Programs and statements
          Program(..), Stmt(..), assert

        -- * Invariants and measures
        , Invariant, Measure

        -- * Verification conditions
        , VC(..)

        -- * Result of a proof
        , ProofResult(..)

        -- * Configuring the WP engine
        , WPConfig(..), defaultWPCfg

        -- * Checking WP correctness
        , wpProve, wpProveWith
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
data Program st = Program { precondition  :: st -> SBool   -- ^ Environmental assumptions
                          , program       :: Stmt st       -- ^ Program
                          , postcondition :: st -> SBool   -- ^ Correctness statement
                          }

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
data VC st m = BadPostcondition         st                  -- ^ The postcondition doesn't hold
             | AbortReachable    String st                  -- ^ The named abort condition is reachable
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
  show (BadPostcondition     s)                 = dispVC "Post condition must hold"                                             [("", show s)]
  show (AbortReachable    nm s)                 = dispVC ("Abort " ++ show nm ++ " condition is satisfiable")                   [("", show s)]
  show (InvariantPre      nm s)                 = dispVC ("Invariant for loop " ++ show nm ++ " must hold upon entry")          [("", show s)]
  show (InvariantMaintain nm s1 s2)             = dispVC ("Invariant for loop " ++ show nm ++ " must be maintaned by the body")
                                                         [ ("Before", show s1)
                                                         , ("After ", show s2)
                                                         ]
  show (MeasureBound      nm (s, m))            = dispVC ("Measure for loop "   ++ show nm ++ " must be non-negative")
                                                         [ ("State  ", show s)
                                                         , ("Measure", showMeasure m )
                                                         ]
  show (MeasureDecrease   nm (s1, m1) (s2, m2)) = dispVC ("Measure for loop "   ++ show nm ++ " must decrease")
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
wpProveWith :: forall st res. (Show res, Mergeable st, Queriable IO st res) => WPConfig -> Program st -> IO (ProofResult res)
wpProveWith cfg@WPConfig{wpVerbose} Program{precondition, program, postcondition} = runSMTWith (wpSolver cfg) $ query $ do

        weakestPrecondition <- wp program (\st -> [(postcondition st, BadPostcondition st)])

        start <- create
        let vcs = weakestPrecondition start

        constrain $ sNot $ precondition start .=> sAnd (map fst vcs)

        cs <- checkSat
        case cs of
          Unk   -> Indeterminate . show <$> getUnknownReason

          Unsat -> do let t = isTotal program

                      if t then msg "Total correctness is established."
                           else msg "Partial correctness is established."

                      return $ Proven t

          Sat   -> do let checkVC :: (SBool, VC st SInteger) -> Query [VC res Integer]
                          checkVC (cond, vc) = do c <- getValue cond
                                                  if c
                                                     then return []   -- The VC was OK
                                                     else do vc' <- case vc of
                                                                      BadPostcondition    s                 -> BadPostcondition    <$> project s
                                                                      AbortReachable    l s                 -> AbortReachable    l <$> project s
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

  where msg = io . when wpVerbose . putStrLn

        -- Compute the weakest precondition to establish the property:
        wp :: Stmt st -> (st -> [(SBool, VC st SInteger)]) -> Query (st -> [(SBool, VC st SInteger)])

        -- Skip simply keeps the conditions
        wp Skip post = return post

        -- Abort is never satisfiable. The only way to have Abort's VC to pass is
        -- to run it in a precondition (either via program or in an if branch) that
        -- evaluates to false, i.e., it must not be reachable.
        wp (Abort nm) _ = return $ \st -> [(sFalse, AbortReachable nm st)]

        -- Assign simply transforms the state and passes on
        wp (Assign f) post = return $ post . f

        -- Conditional: We separately collect the VCs, and predicate with the proper branch condition
        wp (If c tb fb) post = do tWP <- wp tb post
                                  fWP <- wp fb post
                                  return $ \st -> let cond = c st
                                                  in   [(     cond .=> b, v) | (b, v) <- tWP st]
                                                    ++ [(sNot cond .=> b, v) | (b, v) <- fWP st]

        -- Sequencing: Simply run through the statements
        wp (Seq [])              post = return post
        wp (Seq (s:ss))          post = wp s =<< wp (Seq ss) post

        -- While loop, where all the WP magic happens!
        wp (While nm inv mm cond body) post = do
                st'  <- create

                let noMeasure = isNothing mm
                    m         = fromJust mm
                    curM      = m st'
                    zero      = map (const 0) curM

                    iterates   = inv st' .&&       cond st'
                    terminates = inv st' .&& sNot (cond st')


                -- Condition 1: Invariant must hold prior to loop entry
                invHoldsPrior <- wp Skip (\st -> [(inv st, InvariantPre nm st)])

                -- Condition 2: If we iterate, invariant must be maitained by the body
                invMaintained <- wp body (\st -> [(iterates .=> inv st, InvariantMaintain nm st' st)])

                -- Condition 3: If we terminate, invariant must be strong enough to establish the post condition
                invEstablish <- wp body (const [(terminates .=> b, v) | (b, v) <- post st'])

                -- Condition 4: If we iterate, measure must always be non-negative
                measureNonNegative <- if noMeasure
                                      then return  (const [])
                                      else wp Skip (const [(iterates .=> curM .>= zero, MeasureBound nm (st', curM))])

                -- Condition 5: If we iterate, the measure must decrease
                measureDecreases <- if noMeasure
                                    then return  (const [])
                                    else wp body (\st -> let prevM = m st in [(iterates .=> prevM .< curM, MeasureDecrease nm (st', curM) (st, prevM))])

                -- Simply concatenate the VCs from all our conditions:
                return $ \st ->    invHoldsPrior      st
                                ++ invMaintained      st'
                                ++ invEstablish       st'
                                ++ measureNonNegative st'
                                ++ measureDecreases   st'

-- | Check correctness using the default solver. Equivalent to @'wpProveWith' 'defaultWPCfg'@.
wpProve :: (Show res, Mergeable st, Queriable IO st res) => Program st -> IO (ProofResult res)
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
