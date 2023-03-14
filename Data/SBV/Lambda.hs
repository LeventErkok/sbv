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
            lambda,      lambdaStr
          , namedLambda, namedLambdaStr
          , axiom,       axiomStr
          , Lambda(..), Axiom(..)
        ) where

import Control.Monad
import Control.Monad.Trans

import Data.SBV.Core.Data
import Data.SBV.Core.Kind
import Data.SBV.Core.Symbolic
import Data.SBV.SMT.SMTLib2
import Data.SBV.Utils.PrettyNum

import Data.IORef (readIORef)
import Data.List
import Data.Proxy

import qualified Data.Foldable      as F
import qualified Data.Map.Strict    as M
import qualified Data.IntMap.Strict as IM

import qualified Data.Generics.Uniplate.Data as G

data Defn = Defn [String]        -- The uninterpreted names referred to in the body
                 String          -- Param declaration. Empty if there are no params
                 (Int -> String) -- Body, given the tab amount.

data Free = Closed String -- Must be a closed definition, string is the function
          | Open          -- Free variables are OK

-- | Generic creator for anonymous lamdas.
lambdaGen :: Lambda Symbolic a => Free -> (Defn -> b) -> State -> Kind -> a -> IO b
lambdaGen freeKind trans inState fk f = do
   ll  <- readIORef (rLambdaLevel inState)
   st  <- mkNewState (stCfg inState) $ Lambda (ll + 1)

   trans <$> convert freeKind st fk (mkLambda st f)

-- | Create an SMTLib lambda, in the given state.
lambda :: Lambda Symbolic a => State -> Kind -> a -> IO SMTDef
lambda inState fk = lambdaGen Open mkLam inState fk
   where mkLam (Defn frees params body) = SMTLam fk frees params body

-- | Create an anonymous lambda, rendered as n SMTLib string
lambdaStr :: Lambda Symbolic a => State -> Kind -> a -> IO String
lambdaStr = lambdaGen Open mkLam
   where mkLam (Defn _frees params body) = "(lambda " ++ params ++ "\n" ++ body 2 ++ ")"

-- | Generaic creator for named functions,
namedLambdaGen :: Lambda Symbolic a => Free -> (Defn -> b) -> State -> Kind -> a -> IO b
namedLambdaGen freeKind trans inState@State{rUserFuncs, rDefns} fk f = do
   ll      <- readIORef (rLambdaLevel inState)
   stEmpty <- mkNewState (stCfg inState) $ Lambda (ll + 1)

   -- restore user-funcs and their definitions
   let st = stEmpty{rUserFuncs = rUserFuncs, rDefns = rDefns}

   trans <$> convert freeKind st fk (mkLambda st f)

-- | Create a named SMTLib function, in the given state.
namedLambda :: Lambda Symbolic a => State -> String -> Kind -> a -> IO SMTDef
namedLambda inState nm fk = namedLambdaGen (Closed nm) mkDef inState fk
   where mkDef (Defn frees params body) = SMTDef nm fk frees params body

-- | Create a named SMTLib function, in the given state, string version
namedLambdaStr :: Lambda Symbolic a => State -> String -> Kind -> a -> IO String
namedLambdaStr inState nm fk = namedLambdaGen (Closed nm) mkDef inState fk
   where mkDef (Defn frees params body) = concat $ declUserFuns [SMTDef nm fk frees params body]

-- | Generic axiom generator.
axiomGen :: Axiom Symbolic a => Free -> (Defn -> b) -> State -> a -> IO b
axiomGen freeKind trans inState f = do
   -- make sure we're at the top
   ll <- readIORef (rLambdaLevel inState)
   () <- case ll of
           0 -> pure ()
           _ -> error "Data.SBV.axiom: Not supported: axiom calls that are not at the top-level."

   st <- mkNewState (stCfg inState) $ Lambda 1

   trans <$> convert freeKind st KBool (mkAxiom st f)

-- | Create a named SMTLib axiom, in the given state.
axiom :: Axiom Symbolic a => State -> String -> a -> IO SMTDef
axiom inState nm = axiomGen (Closed nm) mkAx inState
   where mkAx (Defn deps params body) = SMTAxm nm deps $ "(assert (forall " ++ params ++ "\n" ++ body 10 ++ "))"

-- | Create a named SMTLib axiom, in the given state, string version.
axiomStr :: Axiom Symbolic a => State -> String -> a -> IO String
axiomStr inState nm = axiomGen (Closed nm) mkAx inState
   where mkAx (Defn frees params body) = intercalate "\n"
                ["; user given axiom for: " ++ nm ++ if null frees then "" else " [Refers to: " ++ intercalate ", " frees ++ "]"
                , "(assert (forall " ++ params ++ "\n" ++ body 10 ++ "))"
                ]

-- | Convert to an appropriate SMTLib representation.
convert :: MonadIO m => Free -> State -> Kind -> SymbolicT m () -> m Defn
convert freeKind st expectedKind comp = do
   ((), res) <- runSymbolicInState st comp
   pure $ toLambda freeKind (stCfg st) expectedKind res

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

-- | Convert the result of a symbolic run to a more abstract representation
toLambda :: Free -> SMTConfig -> Kind -> Result -> Defn
toLambda freeKind cfg expectedKind result@Result{resAsgns = SBVPgm asgnsSeq} = sh result
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
         | kindOf out /= expectedKind
         = bad [ "Expected kind and final kind do not match"
               , "   Saw     : " ++ show (kindOf out)
               , "   Expected: " ++ show expectedKind
               ]
         | True
         = case freeKind of
             Open                 -> res
             Closed nm | null fvs -> res
                       | True     -> bad [ "Function definition refers to free variable(s)"
                                         , ""
                                         , "   Function : " ++ nm
                                         , "   Refers to: " ++ intercalate ", " (map show fvs)
                                         , ""
                                         , "Check your smtFunction calls and make sure they don't have any free"
                                         , "variables in their definitions. (NB. The refers to variables are"
                                         , "internal names, unfortunately. Check the definition for " ++ show nm
                                         , "for any variables it doesn't take in as a parameter itsef."
                                         ]
         where res = Defn (nub [nm | Uninterpreted nm <- G.universeBi asgnsSeq])
                          paramStr
                          (intercalate "\n" . body)

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
                                           -> map (getSV . snd) inps

               paramStr = '(' : unwords (map (\p -> '(' : show p ++ " " ++ smtType (kindOf p) ++ ")")  params) ++ ")"

               body tabAmnt = let tab = replicate tabAmnt ' '
                              in    [tab ++ "(let ((" ++ show s ++ " " ++ v ++ "))" | (s, v) <- bindings]
                                 ++ [tab ++ show out ++ replicate (length bindings) ')']

               assignments = F.toList (pgmAssignments pgm)

               constants = filter ((`notElem` [falseSV, trueSV]) . fst) consts

               fvs :: [SV]
               fvs = reverse $ walk (params ++ map fst constants) [] assignments
                 where walk _     sofar []       = sofar
                       walk known sofar (a : as) = let (defines, uses) = extract a
                                                       currentFVs      = filter (`notElem` known) uses
                                                   in walk (defines : known) (currentFVs ++ sofar) as

                       extract :: (SV, SBVExpr) -> (SV, [SV])
                       extract (d, expr) = (d, G.universeBi expr)

               bindings :: [(SV, String)]
               bindings =  map mkConst constants ++ map mkAsgn  assignments

               mkConst :: (SV, CV) -> (SV, String)
               mkConst (sv, cv) = (sv, cvToSMTLib (roundingMode cfg) cv)

               out :: SV
               out = case outputs of
                       [o] -> o
                       _   -> bad [ "Unexpected non-singular output"
                                  , "   Saw: " ++ show outputs
                                  ]

               mkAsgn (sv, e) = (sv, converter e)
               converter = cvtExp solverCaps rm skolemMap tableMap funcMap
                 where solverCaps = capabilities (solver cfg)
                       rm         = roundingMode cfg
                       skolemMap  = M.empty
                       tableMap   = IM.empty
                       funcMap    = M.empty
