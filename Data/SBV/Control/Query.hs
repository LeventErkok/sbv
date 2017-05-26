-----------------------------------------------------------------------------
-- |
-- Module      :  Data.SBV.Control.Query
-- Copyright   :  (c) Levent Erkok
-- License     :  BSD3
-- Maintainer  :  erkokl@gmail.com
-- Stability   :  experimental
--
-- Querying a solver interactively.
-----------------------------------------------------------------------------

{-# LANGUAGE LambdaCase     #-}
{-# LANGUAGE NamedFieldPuns #-}

module Data.SBV.Control.Query (
       assert
     , send, ask
     , CheckSatResult(..), checkSat
     , getValue, getModel
     , SMTOption(..), setOption
     , ignoreExitCode
     , (|->)
     , result
     , success
     , failure
     , sbvResume
     , io
     ) where

import Control.Monad            (unless)
import Control.Monad.State.Lazy (get)

import Data.List (intercalate)

import Data.SBV.Core.Data
import Data.SBV.Core.Symbolic (QueryState(..), Query(..), SMTResult(..), State(..))

import Data.SBV.Utils.SExpr

import Data.SBV.Control.Types
import Data.SBV.Control.Utils

import Data.IORef (readIORef)

-- | Set an option.
setOption :: SMTOption -> Query ()
setOption o = send $ "(set-option " ++ show o ++ ")"

-- | Assert a new "fact"
assert :: SBool -> Query ()
assert s = do sw <- inNewContext (`sbvToSW` s)
              send $ "(assert " ++ show sw ++ ")"

-- | Check for satisfiability.
checkSat :: Query CheckSatResult
checkSat = do let cmd = "(check-sat)"
                  bad = unexpected "checkSat" cmd "one of sat/unsat/unknown"
              r <- ask cmd
              parse r bad $ \case ECon "sat"     -> return Sat
                                  ECon "unsat"   -> return Unsat
                                  ECon "unknown" -> return Unk
                                  _              -> bad r Nothing

-- | Make an assignment
infix 1 |->
(|->) :: SymWord a => SBV a -> a -> (SBV a, CW)
a |-> v = case literal v of
            SBV (SVal _ (Left cw)) -> (a, cw)
            r                      -> error $ "Data.SBV: Impossible happened in |->: Cannot construct a CW with literal: " ++ show r

-- | Produce the query result from an assignment.
success :: [(SBV a, CW)] -> Query [SMTResult]
success asgns = do QueryState{queryConfig} <- get
 
                   let grabValues st = do ss <- mapM (sbvToSW st . fst) asgns

                                          inps <- reverse <$> readIORef (rinps st)

                                          -- sanity checks
                                          --     - All existentials should be given a value
                                          --     - No duplicates
                                          --     - No bindings to vars that are not inputs
                                          let missing, extra, dup :: [String]
                                              missing = [n | (EX, (s, n)) <- inps, s `notElem` ss]
                                              extra   = [show s | s <- ss, s `notElem` map (fst . snd) inps]
                                              dup     = let walk []     = []
                                                            walk (n:ns)
                                                              | n `elem` ns = show n : walk (filter (/= n) ns)
                                                              | True        = walk ns
                                                        in walk ss

                                          unless (null (missing ++ extra ++ dup)) $ do

                                                let misTag = "***   Missing inputs"
                                                    dupTag = "***   Duplicate bindings"
                                                    extTag = "***   Extra bindings"

                                                    maxLen = maximum $  0
                                                                      : [length misTag | not (null missing)]
                                                                     ++ [length extTag | not (null extra)]
                                                                     ++ [length dupTag | not (null dup)]

                                                    align s = s ++ replicate (maxLen - length s) ' ' ++ ": "

                                                error $ unlines $ [""
                                                                  , "*** Data.SBV: Query model construction has a faulty assignment."
                                                                  ]
                                                               ++ [ align misTag ++ intercalate ", "  missing | not (null missing)]
                                                               ++ [ align extTag ++ intercalate ", "  extra   | not (null extra)  ]
                                                               ++ [ align dupTag ++ intercalate ", "  dup     | not (null dup)    ]
                                                               ++ [ "*** Data.SBV: Check your query result construction!" ]

                                          return $ zip (map show ss) (map snd asgns)

                   assocs <- inNewContext grabValues

                   let m = SMTModel { modelObjectives = []
                                    , modelAssocs     = assocs
                                    }

                   result $ Satisfiable queryConfig m

-- | Produce this answer as the result.
result :: SMTResult -> Query [SMTResult]
result x = return [x]

-- | Fail with error.
failure :: [String] -> Query [SMTResult]
failure ms = do QueryState{queryConfig} <- get
                result $ ProofError queryConfig ms

-- | Run what SBV would've run, should we not have taken control. Note that
-- if you call this function, SBV will issue a call to check-sat and then
-- collect the model with respect to all the changes the query has performed.
-- If you already do have a model built during the query, use 'result' to
-- return it, instead of telling sbv to do it on its own.
sbvResume :: Query [SMTResult]
sbvResume = do QueryState{queryDefault, queryIgnoreExitCode} <- get
               io $ queryDefault queryIgnoreExitCode
