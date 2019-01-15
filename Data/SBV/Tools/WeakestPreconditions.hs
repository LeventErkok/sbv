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
-----------------------------------------------------------------------------

{-# LANGUAGE FlexibleContexts       #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE ScopedTypeVariables    #-}

module Data.SBV.Tools.WeakestPreconditions (ProofResult(..), Prog, Stmt(..), traceExecution, check, checkWith) where

import Data.List (intercalate)
import Data.Maybe (maybe)

import Control.Monad (when, unless)

import Data.SBV
import Data.SBV.Control

data Stmt st = Skip
             | Abort
             | Assign (st -> st)
             | If     (st -> SBool) (Stmt st) (Stmt st)
             | While  String            -- ^ Loop name (for diagnostic purposes)
                      (st -> SBool)     -- ^ Loop invariant
                      (st -> SInteger)  -- ^ Termination measure
                      (st -> SBool)     -- ^ Loop condition
                      (Stmt st)         -- ^ Loop body
             | Seq    [Stmt st]

type Prog st = Stmt st

data ProofResult a = Proven
                   | Indeterminate String
                   | Failed a

instance Show a => Show (ProofResult a) where
  show Proven            = "Q.E.D."
  show (Indeterminate s) = s
  show (Failed a)        = intercalate "\n" [ "Failed to establish correctness. Starting program state:"
                                            , intercalate "\n" ["  " ++ l | l <- lines (show a)]
                                            ]

traceExecution :: forall st. Show st => Bool -> st -> Prog st -> (st -> SBool) -> IO Bool
traceExecution chatty start prog prop = do printST start
                                           mbEnd <- go [1] prog start
                                           case mbEnd of
                                             Nothing  -> do msg ""
                                                            msg "Program execution aborted."
                                                            return False
                                             Just end -> do msg ""
                                                            msg $ "Final state: " ++ show end
                                                            msg ""
                                                            case unliteral (prop end) of
                                                              Just b  -> return b
                                                              Nothing -> error "Output predicate evaluated to a symbolic value on the final state!"
  where msg :: String -> IO ()
        msg = when chatty . putStrLn

        sLoc :: [Int] -> String
        sLoc l = "==> [" ++ intercalate "." (map show (reverse l)) ++ "]"

        step :: [Int] -> String -> Maybe st -> IO ()
        step l m mbST = do msg $ sLoc l ++ " " ++ m
                           maybe (return ()) printST mbST

        printST :: st -> IO ()
        printST st = msg $ " " ++ show st

        unwrap :: SymVal a => [Int] -> String -> SBV a -> a
        unwrap l m v = case unliteral v of
                         Nothing -> error $ "*** traceExecution: " ++ sLoc l ++ ": Failed to extract concrete value while " ++ show m
                         Just i  -> i

        go :: [Int] -> Prog st -> st -> IO (Maybe st)
        go loc p st = case p of
                        Skip       -> do step loc "Skip" (Just st)
                                         return $ Just st

                        Abort      -> do step loc "Abort" (Just st)
                                         return Nothing

                        Assign f   -> do step loc "Assign" (Just st)
                                         return $ Just $ f st

                        If c tb eb -> case unwrap loc "evaluating the test condition" (c st) of
                                        True  -> do step loc "Conditional, taking the \"then\" branch" (Just st)
                                                    go (1 : loc) tb st
                                        False -> do step loc "Conditional, taking the \"else\" branch" (Just st)
                                                    go (2 : loc) eb st

                        Seq stmts  -> let walk []     _ is = return $ Just is
                                          walk (s:ss) c is = do mbS <- go (c:loc) s is
                                                                case mbS of
                                                                  Just is' -> walk ss (c+1) is'
                                                                  Nothing  -> return Nothing
                                      in walk stmts 1 st

                        While loopName invariant measure condition body -> do
                                let currentCondition is = unwrap loc ("Loop " ++ loopName ++ ", evaluating the while condition") (condition is)
                                    currentMeasure   is = unwrap loc ("Loop " ++ loopName ++ ", evaluating the measure")         (measure   is)
                                    currentInvariant is = unwrap loc ("Loop " ++ loopName ++ ", evaluating the invariant")       (invariant is)

                                    while c mbmPrev is
                                      | not inv
                                      = do step loc ("Loop " ++ loopName ++ ": invariant fails to hold") Nothing
                                           return Nothing
                                      | stop
                                      = do step loc ("Loop " ++ loopName ++ ": condition fails, terminating") (Just is)
                                           return $ Just is
                                      | mCur < 0
                                      = do step loc ("Loop " ++ loopName ++ ": measure must be non-negative, evaluated to: " ++ show mCur) Nothing
                                           return Nothing
                                      | Just mPrev <- mbmPrev, mCur >= mPrev
                                      = do step loc ("Loop " ++ loopName ++ ": measure failed to decrease, prev = " ++ show mPrev ++ ", current = " ++ show mCur) Nothing
                                           return Nothing
                                      | True
                                      = do step loc ("Loop " ++ loopName ++ ": condition holds, executing body") (Just is)
                                           mbS <- go (c:loc) body is
                                           case mbS of
                                             Just is' -> while (c+1) (Just mCur) is'
                                             Nothing  -> return Nothing
                                      where stop = not $ currentCondition is
                                            mCur = currentMeasure   is
                                            inv  = currentInvariant is

                                while 1 Nothing st

checkWith :: forall st res. (Show st, Queriable IO st res)
          => SMTConfig
          -> Bool
          -> Prog st
          -> (st -> SBool)
          -> IO (ProofResult res)
checkWith cfg chatty prog prop = runSMTWith cfg $ query $ do

        weakestPrecondition <- wp prog prop

        st <- create
        constrain $ sNot (weakestPrecondition st)

        do cs <- checkSat
           case cs of
             Unk  -> do r <- getUnknownReason
                        return $ Indeterminate (show r)
             Unsat -> do msg "Total correctness is established."
                         return Proven
             Sat   -> do bad <- project st
                         do os <- getObservables
                            let plu w (_:_:_) = w ++ "s"
                                plu w _       = w
                            unless (null os) $ do let m = "Following proof " ++ plu "obligation" os ++ " failed: "
                                                  msg m
                                                  msg $ replicate (length m) '='
                                                  mapM_ (msg . ("  " ++)) (map fst os)
                                                  msg ""
                            msg $ "Execution leading to failed proof obligation:"
                            msg $ "============================================="
                            lst <- embed bad
                            res <- io $ traceExecution chatty lst prog prop
                            if res
                               then do msg "Failed to establish all proof obligations."
                                       return $ Indeterminate "Not all proof obligations were established."
                               else do msg "Found a starting state that failed the correctness predicate."
                                       return $ Failed bad

  where msg = io . when chatty . putStrLn

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
                return $ \st -> sAnd [ tag  "hold prior to loop"           $ inv st
                                     , tag  "establish the post condition" $ inv st' .&& sNot (c st') .=> post st'
                                     , tag  "be maintained by the loop"    $ inv st' .&&       c st'  .=> inv' st'
                                     , term "get smaller"                  $ inv st' .&&       c st'  .=> m' st'
                                     , term "always be non-negative"       $ inv st' .&&       c st'  .=> m  st' .>= 0
                                     ]

check :: (Show st, Queriable IO st res)
      => Bool
      -> Prog st
      -> (st -> SBool)
      -> IO (ProofResult res)
check = checkWith z3
