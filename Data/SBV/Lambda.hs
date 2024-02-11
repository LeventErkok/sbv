-----------------------------------------------------------------------------
-- |
-- Module    : Data.SBV.Lambda
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Generating lambda-expressions, constraints, and named functions, for (limited)
-- higher-order function support in SBV.
-----------------------------------------------------------------------------

{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NamedFieldPuns        #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE UndecidableInstances  #-}

{-# OPTIONS_GHC -Wall -Werror -fno-warn-orphans #-}

module Data.SBV.Lambda (
            lambda,      lambdaStr
          , namedLambda, namedLambdaStr
          , constraint,  constraintStr
        ) where

import Control.Monad       (join)
import Control.Monad.Trans (liftIO, MonadIO)

import Data.SBV.Core.Data
import Data.SBV.Core.Kind
import Data.SBV.SMT.SMTLib2
import Data.SBV.Utils.PrettyNum

import           Data.SBV.Core.Symbolic hiding   (mkNewState, fresh)
import qualified Data.SBV.Core.Symbolic as     S (mkNewState)

import Data.IORef (readIORef, modifyIORef')
import Data.List

import qualified Data.Foldable      as F
import qualified Data.Map.Strict    as M

import qualified Data.Generics.Uniplate.Data as G

data Defn = Defn [String]                        -- The uninterpreted names referred to in the body
                 (Maybe [(Quantifier, String)])  -- Param declaration groups, if any
                 (Int -> String)                 -- Body, given the tab amount.

-- | Maka a new substate from the incoming state, sharing parts as necessary
inSubState :: MonadIO m => State -> (State -> m b) -> m b
inSubState inState comp = do
        ll <- liftIO $ readIORef (rLambdaLevel inState)
        stEmpty <- S.mkNewState (stCfg inState) (LambdaGen (ll + 1))

        let share fld = fld inState   -- reuse the field from the parent-context
            fresh fld = fld stEmpty   -- create a new field here

        -- freshen certain fields, sharing some from the parent, and run the comp
        -- Here's the guidance:
        --
        --    * Anything that's "shared" updates the calling context. It better be the case
        --      that the caller can handle that info.
        --    * Anything that's "fresh" will be used in this substate, and will be forgotten.
        --      It better be the case that in "toLambda" below, you do something with it.
        --
        -- Note the above applies to all the IORefs, which is most of the state, though
        -- not all. For the time being, those are pathCond, stCfg, and startTime; which
        -- don't really impact anything.
        comp State {
                   -- These are not IORefs; so we share by copying  the value; changes won't be copied back
                     sbvContext          = share sbvContext
                   , pathCond            = share pathCond
                   , startTime           = share startTime

                   -- These are shared IORef's; and is shared, so they will be copied back to the parent state
                   , rProgInfo           = share rProgInfo
                   , rIncState           = share rIncState
                   , rCInfo              = share rCInfo
                   , rUsedKinds          = share rUsedKinds
                   , rUsedLbls           = share rUsedLbls
                   , rUIMap              = share rUIMap
                   , rUserFuncs          = share rUserFuncs
                   , rCgMap              = share rCgMap
                   , rDefns              = share rDefns
                   , rSMTOptions         = share rSMTOptions
                   , rOptGoals           = share rOptGoals
                   , rAsserts            = share rAsserts
                   , rOutstandingAsserts = share rOutstandingAsserts
                   , rPartitionVars      = share rPartitionVars

                   -- Everything else is fresh in the substate; i.e., will not copy back
                   , stCfg               = fresh stCfg
                   , runMode             = fresh runMode
                   , rctr                = fresh rctr
                   , rLambdaLevel        = fresh rLambdaLevel
                   , rtblMap             = fresh rtblMap
                   , rArrayMap           = fresh rArrayMap
                   , rAICache            = fresh rAICache
                   , rinps               = fresh rinps
                   , rlambdaInps         = fresh rlambdaInps
                   , rConstraints        = fresh rConstraints
                   , rObservables        = fresh rObservables
                   , routs               = fresh routs
                   , spgm                = fresh spgm
                   , rconstMap           = fresh rconstMap
                   , rexprMap            = fresh rexprMap
                   , rSVCache            = fresh rSVCache
                   , rQueryState         = fresh rQueryState

                   -- keep track of our parent
                   , parentState         = Just inState
                   }

-- In this case, we expect just one group of parameters, with universal quantification
extractAllUniversals :: [(Quantifier, String)] -> String
extractAllUniversals [(ALL, s)] = s
extractAllUniversals other      = error $ unlines [ ""
                                                  , "*** Data.SBV.Lambda: Impossible happened. Got existential quantifiers."
                                                  , "***"
                                                  , "***  Params: " ++ show other
                                                  , "***"
                                                  , "*** Please report this as a bug!"
                                                  ]


-- | Generic creator for anonymous lamdas.
lambdaGen :: (MonadIO m, Lambda (SymbolicT m) a) => (Defn -> b) -> State -> Kind -> a -> m b
lambdaGen trans inState fk f = inSubState inState $ \st -> trans <$> convert st fk (mkLambda st f)

-- | Create an SMTLib lambda, in the given state.
lambda :: (MonadIO m, Lambda (SymbolicT m) a) => State -> Kind -> a -> m SMTDef
lambda inState fk = lambdaGen mkLam inState fk
   where mkLam (Defn frees params body) = SMTLam fk frees (extractAllUniversals <$> params) body

-- | Create an anonymous lambda, rendered as n SMTLib string
lambdaStr :: (MonadIO m, Lambda (SymbolicT m) a) => State -> Kind -> a -> m String
lambdaStr = lambdaGen mkLam
   where mkLam (Defn _frees Nothing       body) = body 0
         mkLam (Defn _frees (Just params) body) = "(lambda " ++ extractAllUniversals params ++ "\n" ++ body 2 ++ ")"

-- | Generaic creator for named functions,
namedLambdaGen :: (MonadIO m, Lambda (SymbolicT m) a) => (Defn -> b) -> State -> Kind -> a -> m b
namedLambdaGen trans inState fk f = inSubState inState $ \st -> trans <$> convert st fk (mkLambda st f)

-- | Create a named SMTLib function, in the given state.
namedLambda :: (MonadIO m, Lambda (SymbolicT m) a) => State -> String -> Kind -> a -> m SMTDef
namedLambda inState nm fk = namedLambdaGen mkDef inState fk
   where mkDef (Defn frees params body) = SMTDef nm fk frees (extractAllUniversals <$> params) body

-- | Create a named SMTLib function, in the given state, string version
namedLambdaStr :: (MonadIO m, Lambda (SymbolicT m) a) => State -> String -> SBVType -> a -> m String
namedLambdaStr inState nm t = namedLambdaGen mkDef inState fk
   where mkDef (Defn frees params body) = concat $ declUserFuns [(SMTDef nm fk frees (extractAllUniversals <$> params) body, t)]
         fk = case t of
                SBVType [] -> error $ "namedLambdaStr: Invalid type for " ++ show nm ++ ", empty!"
                SBVType xs -> last xs

-- | Generic constraint generator.
constraintGen :: (MonadIO m, Constraint (SymbolicT m) a) => ([String] -> (Int -> String) -> b) -> State -> a -> m b
constraintGen trans inState@State{rProgInfo} f = do
   -- indicate we have quantifiers
   liftIO $ modifyIORef' rProgInfo (\u -> u{hasQuants = True})

   let mkDef (Defn deps Nothing       body) = trans deps body
       mkDef (Defn deps (Just params) body) = trans deps $ \i -> unwords (map mkGroup params) ++ "\n"
                                                              ++ body (i + 2)
                                                              ++ replicate (length params) ')'
       mkGroup (ALL, s) = "(forall " ++ s
       mkGroup (EX,  s) = "(exists " ++ s

   inSubState inState $ \st -> mkDef <$> convert st KBool (mkConstraint st f >>= output >> pure ())

-- | A constraint can be turned into a boolean
instance Constraint Symbolic a => QuantifiedBool a where
  quantifiedBool qb = SBV $ SVal KBool $ Right $ cache f
    where f st = liftIO $ constraint st qb

-- | Generate a constraint.
constraint :: (MonadIO m, Constraint (SymbolicT m) a) => State -> a -> m SV
constraint st = join . constraintGen mkSV st
   where mkSV _deps d = liftIO $ newExpr st KBool (SBVApp (QuantifiedBool (d 0)) [])

-- | Generate a constraint, string version
constraintStr :: (MonadIO m, Constraint (SymbolicT m) a) => State -> a -> m String
constraintStr = constraintGen toStr
   where toStr deps body = intercalate "\n" [ "; user defined axiom: " ++ depInfo deps
                                            , "(assert " ++ body 2 ++ ")"
                                            ]

         depInfo [] = ""
         depInfo ds = "[Refers to: " ++ intercalate ", " ds ++ "]"

-- | Convert to an appropriate SMTLib representation.
convert :: MonadIO m => State -> Kind -> SymbolicT m () -> m Defn
convert st expectedKind comp = do
   ((), res)   <- runSymbolicInState st comp
   curProgInfo <- liftIO $ readIORef (rProgInfo st)
   pure $ toLambda curProgInfo (stCfg st) expectedKind res

-- | Convert the result of a symbolic run to a more abstract representation
toLambda :: ProgInfo -> SMTConfig -> Kind -> Result -> Defn
toLambda curProgInfo cfg expectedKind result@Result{resAsgns = SBVPgm asgnsSeq} = sh result
 where tbd xs = error $ unlines $ "*** Data.SBV.lambda: Unsupported construct." : map ("*** " ++) ("" : xs ++ ["", report])
       bad xs = error $ unlines $ "*** Data.SBV.lambda: Impossible happened."   : map ("*** " ++) ("" : xs ++ ["", bugReport])
       report    = "Please request this as a feature at https://github.com/LeventErkok/sbv/issues"
       bugReport = "Please report this at https://github.com/LeventErkok/sbv/issues"

       sh (Result _hasQuants    -- Has quantified booleans? Does not apply

                  _ki           -- Kind info, we're assuming that all the kinds used are already available in the surrounding context.
                                -- There's no way to create a new kind in a lambda. If a new kind is used, it should be registered.

                  _qcInfo       -- Quickcheck info, does not apply, ignored

                  observables   -- Observables: There's no way to display these, so ignore

                  _codeSegs     -- UI code segments: Again, shouldn't happen; if present, error out

                  is            -- Inputs

                  ( _allConsts  -- Not needed, consts are sufficient for this translation
                  , consts      -- constants used
                  )

                  tbls          -- Tables

                  _arrs         -- Arrays                : nothing to do with them
                  _uis          -- Uninterpeted constants: nothing to do with them
                  _axs          -- Axioms definitions    : nothing to do with them

                  pgm           -- Assignments

                  cstrs         -- Additional constraints: Not currently supported inside lambda's
                  assertions    -- Assertions: Not currently supported inside lambda's

                  outputs       -- Outputs of the lambda (should be singular)
         )
         | not (null cstrs)
         = tbd [ "Constraints."
               , "  Saw: " ++ show (length cstrs) ++ " additional constraint(s)."
               ]
         | not (null assertions)
         = tbd [ "Assertions."
               , "  Saw: " ++ intercalate ", " [n | (n, _, _) <- assertions]
               ]
         | not (null observables)
         = tbd [ "Observables."
               , "  Saw: " ++ intercalate ", " [n | (n, _, _) <- observables]
               ]
         | kindOf out /= expectedKind
         = bad [ "Expected kind and final kind do not match"
               , "   Saw     : " ++ show (kindOf out)
               , "   Expected: " ++ show expectedKind
               ]
         | True
         = res
         where res = Defn (nub [nm | Uninterpreted nm <- G.universeBi asgnsSeq])
                          mbParam
                          (intercalate "\n" . body)

               params = case is of
                          ResultTopInps as -> bad [ "Top inputs"
                                                  , "   Saw: " ++ show as
                                                  ]
                          ResultLamInps xs -> map (\(q, v) -> (q, getSV v)) xs

               mbParam
                 | null params = Nothing
                 | True        = Just [(q, paramList (map snd l)) | l@((q, _) : _)  <- pGroups]
                 where pGroups = groupBy (\(q1, _) (q2, _) -> q1 == q2) params
                       paramList ps = '(' : unwords (map (\p -> '(' : show p ++ " " ++ smtType (kindOf p) ++ ")")  ps) ++ ")"

               body tabAmnt
                 | null constTables
                 , null nonConstTables
                 , Just e <- simpleBody (constBindings ++ svBindings) out
                 = [tab ++ e]
                 | True
                 = map (tab ++) $   [mkLet sv  | sv <- constBindings]
                                 ++ [mkTable t | t  <- constTables]
                                 ++ walk svBindings nonConstTables
                                 ++ [show out ++ replicate totalClose ')']

                 where tab          = replicate tabAmnt ' '
                       mkBind l r   = "(let ((" ++ l ++ " " ++ r ++ "))"
                       mkLet (s, v) = mkBind (show s) v

                       mkTable (((i, ak, rk), elts), _) = mkBind nm (lambdaTable (map (const ' ') nm) ak rk elts)
                          where nm = "table" ++ show i

                       totalClose = length constBindings
                                  + length svBindings
                                  + length constTables
                                  + length nonConstTables

                       walk []  []        = []
                       walk []  remaining = error $ "Data.SBV: Impossible: Ran out of bindings, but tables remain: " ++ show remaining
                       walk (cur@(SV _ nd, _) : rest)  remaining =  map (mkTable . snd) ready
                                                                 ++ [mkLet cur]
                                                                 ++ walk rest notReady
                          where (ready, notReady) = partition (\(need, _) -> need < getLLI nd) remaining

               getLLI :: NodeId -> (Int, Int)
               getLLI (NodeId (_, l, i)) = (l, i)

               -- if we have just one definition returning it, simplify
               simpleBody :: [(SV, String)] -> SV -> Maybe String
               simpleBody [(v, e)] o | v == o = Just e
               simpleBody _        _          = Nothing

               assignments = F.toList (pgmAssignments pgm)

               constants = filter ((`notElem` [falseSV, trueSV]) . fst) consts

               constBindings, svBindings :: [(SV, String)]
               constBindings = map mkConst constants
               svBindings    = map mkAsgn assignments

               mkConst :: (SV, CV) -> (SV, String)
               mkConst (sv, cv) = (sv, cvToSMTLib (roundingMode cfg) cv)

               out :: SV
               out = case outputs of
                       [o] -> o
                       _   -> bad [ "Unexpected non-singular output"
                                  , "   Saw: " ++ show outputs
                                  ]

               rm = roundingMode cfg

               -- NB. The following is dead-code, since we ensure tbls is empty
               -- We used to support this, but there are issues, so dropping support
               -- See, for instance, https://github.com/LeventErkok/sbv/issues/664
               (tableMap, constTables, nonConstTablesUnindexed) = constructTables rm consts tbls

               -- Index each non-const table with the largest index of SV it needs
               nonConstTables = [ (maximum ((0, 0) : [getLLI n | SV _ n <- elts]), nct)
                                | nct@((_, elts), _) <- nonConstTablesUnindexed]

               lambdaTable :: String -> Kind -> Kind -> [SV] -> String
               lambdaTable extraSpace ak rk elts = "(lambda ((" ++ lv ++ " " ++ smtType ak ++ "))" ++ space ++ chain 0 elts ++ ")"
                 where cnst k i = cvtCV rm (mkConstCV k (i::Integer))

                       lv = "idx"

                       -- If more than 5 elts, use new-lines
                       long = not (null (drop 5 elts))
                       space
                         | long
                         = "\n                  " ++ extraSpace
                         | True
                         = " "

                       chain _ []     = cnst rk 0
                       chain _ [x]    = show x
                       chain i (x:xs) = "(ite (= " ++ lv ++ " " ++ cnst ak i ++ ") "
                                           ++ show x ++ space
                                           ++ chain (i+1) xs
                                           ++ ")"

               mkAsgn (sv, e) = (sv, converter e)
               converter = cvtExp curProgInfo solverCaps rm tableMap funcMap
                 where solverCaps = capabilities (solver cfg)
                       funcMap    = M.empty

{- HLint ignore module "Use second" -}
