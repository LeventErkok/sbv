-----------------------------------------------------------------------------
-- |
-- Module      :  Data.SBV.Tools.Induction
-- Copyright   :  (c) Levent Erkok
-- License     :  BSD3
-- Maintainer  :  erkokl@gmail.com
-- Stability   :  experimental
--
-- Induction engine for state transition systems. See "Documentation.SBV.Examples.Misc.Induct"
-- for an example use case.
-----------------------------------------------------------------------------

{-# LANGUAGE NamedFieldPuns #-}

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

-- | Show instance for 'InductionStep', diagnostic purposes only.
instance Show InductionStep where
   show (Initiation  Nothing)  = "initiation"
   show (Initiation  (Just s)) = "initiation for strengthening " ++ show s
   show (Consecution Nothing)  = "consecution"
   show (Consecution (Just s)) = "consecution for strengthening " ++ show s

-- | Result of an inductive proof, with a counter-example in case of failure.
--
-- If a proof is found (indicated by a 'Proven' result), then the goal is an
-- invariant of the system. If it fails, then it can fail either in an
-- initiation step or in a consecution step:
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
--      See "Documentation.SBV.Examples.Misc.Induct" for a worked out example of invariant
--      strengthening.
data InductionResult a = Failed InductionStep a
                       | Proven

-- | Show instance for 'InductionResult', diagnostic purposes only.
instance Show a => Show (InductionResult a) where
  show Proven       = "Q.E.D."
  show (Failed s e) = intercalate "\n" [ "Failed while establishing " ++ show s ++ "."
                                       , "Counter-example:"
                                       , intercalate "\n" ["  " ++ l | l <- lines (show e)]
                                       ]

-- | Induction engine, using the default solver. See "Documentation.SBV.Examples.Misc.Induct"
-- for an example use case.
induct :: Show res
       => Bool                       -- ^ Verbose mode
       -> Symbolic ()                -- ^ Setup code, if necessary. (Typically used for 'Data.SBV.setOption' calls. Pass @return ()@ if not needed.)
       -> Query st                   -- ^ How to create a new state
       -> (st -> Query res)          -- ^ How to query a symbolic state
       -> (st -> SBool)              -- ^ Initial condition
       -> [(String, st -> SBool)]    -- ^ Strengthenings, if any. The @String@ is a simple tag.
       -> (st -> [st])               -- ^ Transition relation
       -> (st -> SBool)              -- ^ Goal to prove, i.e., we establish this is an invariant of the state.
       -> IO (InductionResult res)   -- ^ Either proven, or a concrete state value that, if reachable, fails the invariant.
induct = inductWith defaultSMTCfg

-- | Induction engine, configurable with the solver
inductWith :: Show res
           => SMTConfig                   -- ^ Configuration to use
           -> Bool                        -- ^ Verbose mode
           -> Symbolic ()                 -- ^ Setup code, if any
           -> Query st                    -- ^ Get a fresh state
           -> (st -> Query res)           -- ^ Extract observable
           -> (st -> SBool)               -- ^ Initial condition
           -> [(String, st -> SBool)]     -- ^ Strengthenings
           -> (st -> [st])                -- ^ Transition relation
           -> (st -> SBool)               -- ^ Goal to prove
           -> IO (InductionResult res)
inductWith cfg chatty setup fresh extract initial strengthenings trans goal =
     try "Proving initiation"
         (\s -> initial s .=> goal s)
         (Failed (Initiation Nothing))
         $ strengthen strengthenings
         $ try "Proving consecution"
               (\s -> sAnd (goal s : [st s | (_, st) <- strengthenings]) .=> sAll goal (trans s))
               (Failed (Consecution Nothing))
               (msg "Done" >> return Proven)

  where msg = when chatty . putStrLn

        try m p wrap cont = do msg m
                               res <- check p
                               case res of
                                 Just ex -> return $ wrap ex
                                 Nothing -> cont

        check p = runSMTWith cfg $ do
                        setup
                        query $ do st <- fresh
                                   constrain $ sNot (p st)

                                   cs <- checkSat
                                   case cs of
                                     Unk   -> error "Solver said unknown"
                                     Unsat -> return Nothing
                                     Sat   -> do io $ msg "Failed:"
                                                 ex <- extract st
                                                 io $ msg $ show ex
                                                 return $ Just ex

        strengthen []             cont = cont
        strengthen ((nm, st):sts) cont = try ("Proving strengthening initation  : " ++ nm)
                                             (\s -> initial s .=> st s)
                                             (Failed (Initiation (Just nm)))
                                             $ try ("Proving strengthening consecution: " ++ nm)
                                                   (\s -> st s .=> sAll st (trans s))
                                                   (Failed (Consecution (Just nm)))
                                                   (strengthen sts cont)
