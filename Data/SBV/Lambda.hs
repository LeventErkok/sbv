-----------------------------------------------------------------------------
-- |
-- Module    : Data.SBV.Lambda
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- A simple expression language over closed terms, used in creating
-- lambda-expressions for (limited) higher-order function support.
-----------------------------------------------------------------------------

{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NamedFieldPuns        #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TypeApplications      #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module Data.SBV.Lambda (
          lambda, lambdaTop
        ) where

import Control.Monad.Trans

import Data.SBV.Core.Data
import Data.SBV.Core.Kind
import Data.SBV.Core.Symbolic
import Data.SBV.Provers.Prover
import Data.SBV.SMT.SMTLib2
import Data.SBV.Utils.PrettyNum

import Data.IORef (readIORef)
import Data.List
import Data.Proxy

import qualified Data.Foldable      as F
import qualified Data.Map.Strict    as M
import qualified Data.IntMap.Strict as IM

-- | Create a lambda-expression at the top. Only for internal testing purposes
lambdaTop :: Lambda Symbolic a => a -> IO String
lambdaTop = lambdaAtLevel 0

-- | Create an SMTLib lambda, int he given state
lambda :: Lambda Symbolic a => State -> a -> IO String
lambda inState f = do ll <- readIORef (rLambdaLevel inState)
                      lambdaAtLevel (ll+1) f

lambdaAtLevel :: Lambda Symbolic a => Int -> a -> IO String
lambdaAtLevel l f = do
    st <- mkNewState $ Lambda l
    res <- fst <$> runSymbolicInState st (mkLambda st f)
    pure $ toLambda defaultSMTCfg{smtLibVersion = SMTLib2} res

-- | Values that we can turn into a lambda abstraction
class MonadSymbolic m => Lambda m a where
  mkLambda :: State -> a -> m Result

-- | Turn a symbolic computation to an encapsulated lambda
instance MonadSymbolic m => Lambda m (SymbolicT m (SBV a)) where
  mkLambda st cmp = do ((), res) <- runSymbolicInState st (cmp >>= output >> return ())
                       pure res

-- | Base case, simple values
instance MonadSymbolic m => Lambda m (SBV a) where
  mkLambda st = mkLambda st . (pure :: SBV a -> SymbolicT m (SBV a))

-- | Functions
instance (SymVal a, Lambda m r) => Lambda m (SBV a -> r) where
  mkLambda st fn = mkLambda st =<< fn <$> mkArg
    where mkArg = do let k = kindOf (Proxy @a)
                     sv <- liftIO $ lambdaVar st k
                     pure $ SBV $ SVal k (Right (cache (const (return sv))))

-- | Convert the result of a symbolic run to an SMTLib lambda expression
toLambda :: SMTConfig -> Result -> String
toLambda cfg = sh
 where tbd xs = error $ unlines $ "*** Data.SBV.lambda: Unsupported construct." : map ("*** " ++) ("" : xs ++ ["", report])
       bad xs = error $ unlines $ "*** Data.SBV.lambda: Impossible happened."   : map ("*** " ++) ("" : xs ++ ["", bugReport])
       report    = "Please request this as a feature at https://github.com/LeventErkok/sbv/issues"
       bugReport = "Please report this at https://github.com/LeventErkok/sbv/issues"

       sh (Result _ki           -- Kind info, we're assuming that all the kinds used are already available in the surrounding context.
                                -- There's no way to create a new kind in a lambda. If a new kind is used, it should be registered.

                  _qcInfo       -- Quickcheck info, does not apply, ignored

                  observables   -- Observables: No way to display these, so if present we error out

                  codeSegs      -- UI code segments: Again, shouldn't happen; if present, error out

                  is            -- Inputs

                  ( _allConsts  -- This contains the CV->SV map, which isn't needed for lambdas since we don't support tables
                  , consts      -- constants used
                  )

                  tbls          -- Tables: Not currently supported inside lambda's
                  arrs          -- Arrays: Not currently supported inside lambda's
                  uis           -- UIs:    Not currently supported inside lambda's
                  axs           -- Axioms: Not currently supported inside lambda's

                  pgm           -- Assignments

                  cstrs         -- Additional constraints: Not currently supported inside lambda's
                  assertions    -- Assertions: Not currently supported inside lambda's

                  outputs       -- Outputs of the lambda (should be singular)
         )
         | not (null observables)
         = tbd [ "Observable values."
               , "  Saw: " ++ intercalate ", " [o | (o, _, _) <- observables]
               ]
         | not (null codeSegs)
         = tbd [ "Uninterpreted code segments."
               , "  Saw: " ++ intercalate ", " [o | (o, _) <- codeSegs]
               ]
         | not (null tbls)
         = tbd [ "Auto-constructed tables."
               , "  Saw: " ++ intercalate ", " ["table" ++ show i | ((i, _, _), _) <- tbls]
               ]
         | not (null arrs)
         = tbd [ "Array values."
               , "  Saw: " ++ intercalate ", " ["arr" ++ show i | (i, _) <- arrs]
               ]
         | not (null uis)
         = tbd [ "Uninterpreted constants."
               , "  Saw: " ++ intercalate ", " (map fst uis)
               ]
         | not (null axs)
         = tbd [ "Axioms/definitions."
               , "  Saw: " ++ intercalate ", " [n | (_, n, _) <- axs]
               ]
         | not (null cstrs)
         = tbd [ "Constraints."
               , "  Saw: " ++ show (length cstrs) ++ " additional constraint(s)."
               ]
         | not (null assertions)
         = tbd [ "Assertions."
               , "  Saw: " ++ intercalate ", " [n | (n, _, _) <- assertions]
               ]
         | null params
         = body
         | True
         = "(lambda (" ++ params ++ ")\n" ++ body ++ ")"
         where params = case is of
                          (inps, trackers) | any ((== EX) . fst) inps
                                           -> bad [ "Unexpected existentially quantified variables as inputs"
                                                  , "   Saw: " ++ intercalate ", " [getUserName' n | (EX, n) <- inps]
                                                  ]
                                           | not (null trackers)
                                           -> tbd [ "Tracker variables"
                                                  , "   Saw: " ++ intercalate ", " (map getUserName' trackers)
                                                  ]
                                           | True
                                           -> unwords ['(' : getUserName' p ++ " " ++ smtType (kindOf (getSV p)) ++ ")" | (_, p) <- inps]
               body
                | null bindings = ' ' : out
                | True          = go bindings 0
                where go []     n = "   " ++ out ++ replicate n ')'
                      go (b:bs) n = tab ++ "(let (" ++ b ++ ")\n" ++ go bs (n+1)

                      tab | null params = ""
                          | True        = "   "

               bindings :: [String]
               bindings =  map mkConst (filter ((`notElem` [falseSV, trueSV]) . fst) consts)
                        ++ map mkAsgn  (F.toList (pgmAssignments pgm))

               mkConst :: (SV, CV) -> String
               mkConst (sv, cv) = "(" ++ v ++ " " ++ c ++ ")"
                  where v = show sv
                        c = cvToSMTLib (roundingMode cfg) cv

               out :: String
               out = case outputs of
                       [o] -> show o
                       _   -> bad [ "Unexpected non-singular output"
                                  , "   Saw: " ++ show outputs
                                  ]

               mkAsgn (s, e) = "(" ++ show s ++ " " ++ converter e ++ ")"
               converter = cvtExp solverCaps rm skolemMap tableMap funcMap
                 where solverCaps = capabilities (solver cfg)
                       rm         = roundingMode cfg
                       skolemMap  = M.empty
                       tableMap   = IM.empty
                       funcMap    = M.empty
