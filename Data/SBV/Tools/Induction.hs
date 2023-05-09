-----------------------------------------------------------------------------
-- |
-- Module    : Data.SBV.Tools.Induction
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Induction engine for state transition systems. See the following examples
-- for details:
--
--   * "Documentation.SBV.Examples.ProofTools.Strengthen": Use of strengthening
--     to establish inductive invariants.
--
--   * "Documentation.SBV.Examples.ProofTools.Sum": Proof for correctness of
--     an algorithm to sum up numbers,
--
--   * "Documentation.SBV.Examples.ProofTools.Fibonacci": Proof for correctness of
--     an algorithm to fast-compute fibonacci numbers, using axiomatization.
-----------------------------------------------------------------------------

{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeFamilies     #-}
{-# LANGUAGE TypeOperators    #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module Data.SBV.Tools.Induction (
         InductionResult(..), InductionStep(..), induct, inductWith
       ) where

import Data.SBV
import Data.SBV.Control

import Data.List     (intercalate)
import Control.Monad (when)

-- | A step in an inductive proof. If the tag is present (i.e., @Just nm@), then
-- the step belongs to the subproof that establishes the strengthening named @nm@.
data InductionStep = Initiation  (Maybe String)
                   | Consecution (Maybe String)
                   | PartialCorrectness

-- | Show instance for 'InductionStep', diagnostic purposes only.
instance Show InductionStep where
   show (Initiation  Nothing)  = "initiation"
   show (Initiation  (Just s)) = "initiation for strengthening " ++ show s
   show (Consecution Nothing)  = "consecution"
   show (Consecution (Just s)) = "consecution for strengthening " ++ show s
   show PartialCorrectness     = "partial correctness"

-- | Result of an inductive proof, with a counter-example in case of failure.
--
-- If a proof is found (indicated by a 'Proven' result), then the invariant holds
-- and the goal is established once the termination condition holds. If it fails, then
-- it can fail either in an initiation step or in a consecution step:
--
--    * A 'Failed' result in an 'Initiation' step means that the invariant does /not/ hold for
--      the initial state, and thus indicates a true failure.
--
--    * A 'Failed' result in a 'Consecution' step will return a state /s/. This state is known as a
--      CTI (counterexample to inductiveness): It will lead to a violation of the invariant
--      in one step. However, this does not mean the property is invalid: It could be the
--      case that it is simply not inductive. In this case, human intervention---or a smarter
--      algorithm like IC3 for certain domains---is needed to see if one can strengthen the
--      invariant so an inductive proof can be found. How this strengthening can be done remains
--      an art, but the science is improving with algorithms like IC3.
--
--    * A 'Failed' result in a 'PartialCorrectness' step means that the invariant holds, but assuming the
--      termination condition the goal still does not follow. That is, the partial correctness
--      does not hold.
data InductionResult a = Failed InductionStep a
                       | Proven

-- | Show instance for 'InductionResult', diagnostic purposes only.
instance Show a => Show (InductionResult a) where
  show Proven       = "Q.E.D."
  show (Failed s e) = intercalate "\n" [ "Failed while establishing " ++ show s ++ "."
                                       , "Counter-example to inductiveness:"
                                       , intercalate "\n" ["  " ++ l | l <- lines (show e)]
                                       ]

-- | Induction engine, using the default solver. See "Documentation.SBV.Examples.ProofTools.Strengthen"
-- and "Documentation.SBV.Examples.ProofTools.Sum" for examples.
induct :: (Show res, Queriable IO st, res ~ QueryResult st)
       => Bool                             -- ^ Verbose mode
       -> Symbolic ()                      -- ^ Setup code, if necessary. (Typically used for 'Data.SBV.setOption' calls. Pass @return ()@ if not needed.)
       -> (st -> SBool)                    -- ^ Initial condition
       -> (st -> [st])                     -- ^ Transition relation
       -> [(String, st -> SBool)]          -- ^ Strengthenings, if any. The @String@ is a simple tag.
       -> (st -> SBool)                    -- ^ Invariant that ensures the goal upon termination
       -> (st -> (SBool, SBool))           -- ^ Termination condition and the goal to establish
       -> IO (InductionResult res)         -- ^ Either proven, or a concrete state value that, if reachable, fails the invariant.
induct = inductWith defaultSMTCfg

-- | Induction engine, configurable with the solver
inductWith :: (Show res, Queriable IO st, res ~ QueryResult st)
           => SMTConfig
           -> Bool
           -> Symbolic ()
           -> (st -> SBool)
           -> (st -> [st])
           -> [(String, st -> SBool)]
           -> (st -> SBool)
           -> (st -> (SBool, SBool))
           -> IO (InductionResult res)
inductWith cfg chatty setup initial trans strengthenings inv goal =
     try "Proving initiation"
         (\s -> initial s .=> inv s)
         (Failed (Initiation Nothing))
         $ strengthen strengthenings
         $ try "Proving consecution"
               (\s -> sAnd (inv s : [st s | (_, st) <- strengthenings]) .=> sAll inv (trans s))
               (Failed (Consecution Nothing))
               $ try "Proving partial correctness"
                     (\s -> let (term, result) = goal s in inv s .&& term .=> result)
                     (Failed PartialCorrectness)
                     (msg "Done" >> return Proven)

  where msg = when chatty . putStrLn

        try m p wrap cont = do msg m
                               res <- check p
                               case res of
                                 Just ex -> return $ wrap ex
                                 Nothing -> cont

        check p = runSMTWith cfg $ do
                        setup
                        query $ do st <- create
                                   constrain $ sNot (p st)

                                   cs <- checkSat
                                   case cs of
                                     Unk    -> error "Solver said unknown"
                                     DSat{} -> error "Solver returned a delta-sat result"
                                     Unsat  -> return Nothing
                                     Sat    -> do io $ msg "Failed:"
                                                  ex <- project st
                                                  io $ msg $ show ex
                                                  return $ Just ex

        strengthen []             cont = cont
        strengthen ((nm, st):sts) cont = try ("Proving strengthening initiation  : " ++ nm)
                                             (\s -> initial s .=> st s)
                                             (Failed (Initiation (Just nm)))
                                             $ try ("Proving strengthening consecution: " ++ nm)
                                                   (\s -> st s .=> sAll st (trans s))
                                                   (Failed (Consecution (Just nm)))
                                                   (strengthen sts cont)
