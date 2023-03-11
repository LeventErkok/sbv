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
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TypeApplications      #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module Data.SBV.Lambda (
          lambda, namedLambda, axiom, Lambda(..), Axiom(..)
        ) where

import Control.Monad
import Control.Monad.Trans

import Data.SBV.Core.Data
import Data.SBV.Core.Kind
import Data.SBV.Core.Symbolic
import Data.SBV.SMT.SMTLib2
import Data.SBV.Utils.PrettyNum

import Data.IORef (readIORef, newIORef)
import Data.List
import Data.Proxy

import qualified Data.Foldable      as F
import qualified Data.Map.Strict    as M
import qualified Data.IntMap.Strict as IM
import qualified Data.Set as Set

import qualified Data.Generics.Uniplate.Data as G

-- | What kind of output to generate?
data GenKind = GenLambda
             | GenDefn   String Kind  -- kind is the resulting kind (note, not the arguments kinds, the result type)
             | GenAxiom

-- | Create an SMTLib lambda, in the given state.
lambda :: Lambda Symbolic a => State -> a -> IO String
lambda inState f = do
   ll  <- readIORef (rLambdaLevel inState)
   st  <- mkNewState (stCfg inState) $ Lambda (ll + 1)
   -- in this case we ignore the firee vars
   snd <$> convert st Nothing GenLambda (mkLambda st f)

-- | Create a named SMTLib function, in the given state.
namedLambda :: Lambda Symbolic a => State -> String -> Kind -> a -> IO ([String], String)
namedLambda inState nm fk f = do
   ll      <- readIORef (rLambdaLevel inState)
   stEmpty <- mkNewState (stCfg inState) $ Lambda (ll + 1)

   -- if we're in a recursive loop, make sure we restore it
   st <- do curDefs <- readIORef (rUserFuncs inState)
            if nm `Set.member` curDefs
               then do nr <- newIORef (Set.singleton nm)
                       pure $ stEmpty {rUserFuncs = nr}
               else pure $ stEmpty

   convert st (Just nm) (GenDefn nm fk) (mkLambda st f)

-- | Create a forall quantified axiom at the top. The list of strings is the free vars in it.
axiom :: Axiom Symbolic a => State -> a -> IO ([String], String)
axiom inState f = do
   -- make sure we're at the top
   ll <- readIORef (rLambdaLevel inState)
   () <- case ll of
           0 -> pure ()
           _ -> error "Data.SBV.axiom: Not supported: axiom calls that are not at the top-level."

   st <- mkNewState (stCfg inState) $ Lambda 1
   convert st Nothing GenAxiom (mkAxiom st f)

-- | Convert to an appropriate SMTLib representation.
convert :: MonadIO m => State -> Maybe String -> GenKind -> SymbolicT m () -> m ([String], String)
convert st mbNm knd comp = do
   ((), res) <- runSymbolicInState st comp
   pure $ toLambda mbNm knd (stCfg st) res

-- | Values that we can turn into a lambda abstraction
class MonadSymbolic m => Lambda m a where
  mkLambda :: State -> a -> m ()

-- | Base case, simple values
instance MonadSymbolic m => Lambda m (SBV a) where
  mkLambda _ out = void $ output out

-- | Functions
instance (SymVal a, Lambda m r) => Lambda m (SBV a -> r) where
  mkLambda st fn = mkArg >>= mkLambda st . fn
    where mkArg = do let k = kindOf (Proxy @a)
                     sv <- liftIO $ lambdaVar st k
                     pure $ SBV $ SVal k (Right (cache (const (return sv))))

-- | Convert the result of a symbolic run to an SMTLib lambda expression
toLambda :: Maybe String -> GenKind -> SMTConfig -> Result -> ([String], String)
toLambda mbNm knd cfg result@Result{resAsgns = SBVPgm asgnsSeq} = sh result
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
                  _uis          -- Uninterpeted constants: nothing to do with them
                  _axs          -- Axioms definitions    : nothing to do with them

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
         | not (null cstrs)
         = tbd [ "Constraints."
               , "  Saw: " ++ show (length cstrs) ++ " additional constraint(s)."
               ]
         | not (null assertions)
         = tbd [ "Assertions."
               , "  Saw: " ++ intercalate ", " [n | (n, _, _) <- assertions]
               ]
         | True
         = (deps, genSMTLib isRecursive knd params body)
         where deps        = nub [nm | Uninterpreted nm <- G.universeBi asgnsSeq]
               isRecursive = maybe False (`elem` deps) mbNm

               params = case is of
                          (inps, trackers) | any ((== EX) . fst) inps
                                           -> bad [ "Unexpected existentially quantified variables as inputs"
                                                  , "   Saw: " ++ intercalate ", " [getUserName' n | (EX, n) <- inps]
                                                  ]
                                           | not (null trackers)
                                           -> tbd [ "Tracker variables"
                                                  , "   Saw: " ++ intercalate ", " (map getUserName' trackers)
                                                  ]
                                           | True
                                           -> ['(' : getUserName' p ++ " " ++ smtType (kindOf (getSV p)) ++ ")" | (_, p) <- inps]
               body
                | null bindings = tab ++ out
                | True          = go bindings 0
                where go []     n = extraTab ++ "   " ++ out ++ replicate n ')'
                      go (b:bs) n = extraTab ++ tab ++ "(let (" ++ b ++ ")\n" ++ go bs (n+1)

                      tab | null params = ""
                          | True        = "   "

                      extraTab = case knd of
                                   GenLambda     -> ""
                                   GenDefn   _ _ -> replicate (2 + length "define-fun")     ' '
                                   GenAxiom      -> replicate (2 + length "assert")         ' '

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

genSMTLib :: Bool -> GenKind -> [String] -> String -> String
genSMTLib isRec k = case k of
                      GenLambda       -> mkLam
                      GenDefn   nm fk -> mkDef nm (smtType fk)
                      GenAxiom        -> mkAxm
  where mkLam [] body = body
        mkLam ps body = "(lambda (" ++ unwords ps ++ ")\n" ++ body ++ ")"

        mkDef nm fk [] body = "(" ++ definer isRec ++ " " ++ nm ++ " () (" ++ fk ++ ")\n"                   ++ body ++ ")"
        mkDef nm fk ps body = "(" ++ definer isRec ++ " " ++ nm ++ " (" ++ unwords ps ++ ") " ++ fk ++ "\n" ++ body ++ ")"

        definer False = "define-fun"
        definer True  = "define-fun-rec"

        mkAxm [] body = "(assert " ++ body ++ ")"
        mkAxm ps body = "(assert (forall (" ++ unwords ps ++ ")\n" ++ body ++ "))"
