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

-- | A step in an inductive proof. If the tags are given (i.e., @Just nm@), then
-- the step belongs to the subproof that establishes the strengthening @nm@.
data InductionStep = Initiation  (Maybe String)
                   | Consecution (Maybe String)

-- | Show instance for 'InductionStep', diagnostic purposes only.
instance Show InductionStep where
   show (Initiation  Nothing)  = "initiation"
   show (Initiation  (Just s)) = "initiation for strengthening " ++ show s
   show (Consecution Nothing)  = "consecution"
   show (Consecution (Just s)) = "consecution for strengthening " ++ show s

-- | Result of an inductive proof, with a counter-example in case of failure.
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
--
-- Note that if a counter-example is returned then it is guaranteed to violate the invariant
-- we are trying to prove. However, it is __not__ guaranteed that this state is actually reachable
-- from the initial state. (That is, the property may not be inductive.) This is the role of
-- the strengthenings parameter: The art of induction is coming up the proper inductive strengthening
-- to establish properties of interest, and the user has to provide these strenghtenings in case
-- the invariant is not inductive.
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
