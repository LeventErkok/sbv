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
{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE ScopedTypeVariables    #-}

module Data.SBV.Tools.WeakestPreconditions (ProofResult(..), Prog, Stmt(..), traceExecution, check, checkWith) where

import Data.List (intercalate)
import Data.Maybe (fromMaybe)

import Control.Monad (when, unless)

import Data.SBV
import Data.SBV.Control

data Stmt st = Skip
             | Abort
             | Assign (st -> st)
             | If     (st -> SBool) (Stmt st) (Stmt st)
             | While  String            -- Loop name (for diagnostic purposes)
                      (st -> SBool)     -- Loop invariant
                      (st -> SInteger)  -- Termination measure
                      (st -> SBool)     -- Loop condition
                      (Stmt st)         -- Loop body
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


-- Left: Line no, Right iteration count
type Loc = [Either Int Int]

traceExecution :: forall st. Show st => Bool -> st -> Prog st -> (st -> SBool) -> IO Bool
traceExecution chatty start prog prop = do printST start
                                           mbEnd <- go [Left 1] prog start
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

        sLoc :: Loc -> String
        sLoc l = "==> [" ++ intercalate "." (map sh (reverse l)) ++ "]"
          where sh (Left  i) = show i
                sh (Right i) = "{" ++ show i ++ "}"

        step :: Loc -> String -> st -> IO st
        step l m st = do msg $ sLoc l ++ " " ++ m
                         printST st
                         return st

        stop :: Loc -> String -> IO (Maybe st)
        stop l m = do msg $ sLoc l ++ " " ++ m
                      return Nothing

        noChange :: Loc -> String -> st -> IO (Maybe st)
        noChange l m st = Just <$> step l m st

        printST :: st -> IO ()
        printST st = msg $ " " ++ show st

        unwrap :: SymVal a => Loc -> String -> SBV a -> a
        unwrap l m = fromMaybe die . unliteral
           where die = error $ "*** traceExecution: " ++ sLoc l ++ ": Failed to extract concrete value while " ++ show m

        go :: Loc -> Prog st -> st -> IO (Maybe st)
        go loc p st = analyze p
          where analyze Skip         = noChange loc "Skip"  st

                analyze Abort        = noChange loc "Abort" st

                analyze (Assign f)   = Just . f <$> step loc "Assign" st

                analyze (If c tb eb)
                  | branchTrue       = go (Left 1 : loc) tb =<< step loc "Conditional, taking the \"then\" branch" st
                  | True             = go (Left 2 : loc) eb =<< step loc "Conditional, taking the \"else\" branch" st
                  where branchTrue = unwrap loc "evaluating the test condition" (c st)

                analyze (Seq stmts)  = walk stmts 1 st
                  where walk []     _ is = return $ Just is
                        walk (s:ss) c is = do mbS <- go (Left c : loc) s is
                                              case mbS of
                                                Just is' -> walk ss (c+1) is'
                                                Nothing  -> return Nothing

                analyze (While loopName invariant measure condition body) = do
                          let currentCondition is = unwrap loc ("Loop " ++ loopName ++ ", evaluating the while condition") (condition is)
                              currentMeasure   is = unwrap loc ("Loop " ++ loopName ++ ", evaluating the measure")         (measure   is)
                              currentInvariant is = unwrap loc ("Loop " ++ loopName ++ ", evaluating the invariant")       (invariant is)

                              while c mbmPrev is
                                | not inv
                                = stop loc ("Loop " ++ loopName ++ ": invariant fails to hold")
                                | not cCur
                                = noChange loc ("Loop " ++ loopName ++ ": condition fails, terminating") is
                                | mCur < 0
                                = stop loc ("Loop " ++ loopName ++ ": measure must be non-negative, evaluated to: " ++ show mCur)
                                | Just mPrev <- mbmPrev, mCur >= mPrev
                                = stop loc ("Loop " ++ loopName ++ ": measure failed to decrease, prev = " ++ show mPrev ++ ", current = " ++ show mCur)
                                | True
                                = do mbS <- go (Right c : loc) body =<< step loc ("Loop " ++ loopName ++ ": condition holds, executing body") is
                                     case mbS of
                                       Just is' -> while (c+1) (Just mCur) is'
                                       Nothing  -> return Nothing

                                where cCur = currentCondition is
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
                                                  mapM_ (msg . (' ' :) . fst) os
                                                  msg ""
                            msg "Execution leading to failed proof obligation:"
                            msg "============================================="
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
