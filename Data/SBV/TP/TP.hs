-----------------------------------------------------------------------------
-- |
-- Module    : Data.SBV.TP.TP
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
-----------------------------------------------------------------------------

{-# LANGUAGE ConstraintKinds            #-}
{-# LANGUAGE DataKinds                  #-}
{-# LANGUAGE DerivingStrategies         #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE NamedFieldPuns             #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE TypeAbstractions           #-}
{-# LANGUAGE TypeApplications           #-}
{-# LANGUAGE TypeFamilyDependencies     #-}
{-# LANGUAGE TypeOperators              #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module Data.SBV.TP.TP (
         Proposition, Proof, proofOf, assumptionFromProof, Instantiatable(..), Inst(..), Measure(..)
       , rootOfTrust, RootOfTrust(..), ProofTree(..), showProofTree, showProofTreeHTML
       ,   axiom
       ,   lemma,   lemmaWith
       ,    calc,    calcWith
       ,  induct,  inductWith
       , sInduct, sInductWith
       , sorry
       , TP, runTP, runTPWith, tpQuiet, tpRibbon, tpStats, tpCache
       , (|-), (⊢), (=:), (≡), (??), (∵), split, split2, cases, (==>), (⟹), qed, trivial, contradiction
       , qc
       ) where

import Data.SBV
import Data.SBV.Core.Model (qSaturateSavingObservables)

import Data.SBV.Control hiding (getProof)

import Data.SBV.TP.Kernel
import Data.SBV.TP.Utils

import qualified Data.SBV.List as SL

import Control.Monad (when)
import Control.Monad.Trans (liftIO)

import Data.Char  (isSpace)
import Data.List  (intercalate, isPrefixOf, isSuffixOf)
import Data.Maybe (catMaybes, maybeToList)

import Data.Proxy
import Data.Kind    (Type)
import GHC.TypeLits (KnownSymbol, symbolVal, Symbol)

import Data.SBV.Utils.TDiff

import Data.Dynamic

import qualified Test.QuickCheck as QC
import Test.QuickCheck (quickCheckWithResult, stdArgs, maxSize, chatty)

-- | Captures the steps for a calculationa proof
data CalcStrategy = CalcStrategy { calcIntros     :: SBool
                                 , calcProofTree  :: TPProof
                                 , calcQCInstance :: [Int] -> QC.Args -> Query QC.Result
                                 }

-- | Saturatable things in steps
proofTreeSaturatables :: TPProof -> [SBool]
proofTreeSaturatables = go
  where go (ProofEnd    b           hs                ) = b : concatMap getH hs
        go (ProofStep   a           hs               r) = a : concatMap getH hs ++ go r
        go (ProofBranch (_ :: Bool) (_ :: [String]) ps) = concat [b : go p | (b, p) <- ps]

        getH (HelperProof  p) = [getObjProof p]
        getH (HelperAssum  b) = [b]
        getH HelperQC{}       = []
        getH HelperString{}   = []

-- | Things that are inside calc-strategy that we have to saturate
getCalcStrategySaturatables :: CalcStrategy -> [SBool]
getCalcStrategySaturatables (CalcStrategy calcIntros calcProofTree _calcQCInstance) = calcIntros : proofTreeSaturatables calcProofTree

-- | Propagate the settings for ribbon/timing from top to current. Because in any subsequent configuration
-- in a lemmaWith, inductWith etc., we just want to change the solver, not the actual settings for TP.
tpMergeCfg :: SMTConfig -> SMTConfig -> SMTConfig
tpMergeCfg cur top = cur{tpOptions = tpOptions top}

-- | Use an injective type family to allow for curried use of calc and strong induction steps.
type family StepArgs a t = result | result -> t where
  StepArgs                                                                             SBool  t =                                               (SBool, TPProofRaw t)
  StepArgs (Forall na a                                                             -> SBool) t = (SBV a                                     -> (SBool, TPProofRaw t))
  StepArgs (Forall na a -> Forall nb b                                              -> SBool) t = (SBV a -> SBV b                            -> (SBool, TPProofRaw t))
  StepArgs (Forall na a -> Forall nb b -> Forall nc c                               -> SBool) t = (SBV a -> SBV b -> SBV c                   -> (SBool, TPProofRaw t))
  StepArgs (Forall na a -> Forall nb b -> Forall nc c -> Forall nd d                -> SBool) t = (SBV a -> SBV b -> SBV c -> SBV d          -> (SBool, TPProofRaw t))
  StepArgs (Forall na a -> Forall nb b -> Forall nc c -> Forall nd d -> Forall ne e -> SBool) t = (SBV a -> SBV b -> SBV c -> SBV d -> SBV e -> (SBool, TPProofRaw t))

-- | Wrapper around measure values.
newtype Measure t = Measure t deriving newtype (EqSymbolic, OrdSymbolic, Mergeable)

-- | Use an injective type family to allow for curried use of measures in strong induction instances
type family MeasureArgs a t = result | result -> t where
  MeasureArgs                                                                             SBool  t = (                                             Measure t)
  MeasureArgs (Forall na a                                                             -> SBool) t = (SBV a                                     -> Measure t)
  MeasureArgs (Forall na a -> Forall nb b                                              -> SBool) t = (SBV a -> SBV b                            -> Measure t)
  MeasureArgs (Forall na a -> Forall nb b -> Forall nc c                               -> SBool) t = (SBV a -> SBV b -> SBV c                   -> Measure t)
  MeasureArgs (Forall na a -> Forall nb b -> Forall nc c -> Forall nd d                -> SBool) t = (SBV a -> SBV b -> SBV c -> SBV d          -> Measure t)
  MeasureArgs (Forall na a -> Forall nb b -> Forall nc c -> Forall nd d -> Forall ne e -> SBool) t = (SBV a -> SBV b -> SBV c -> SBV d -> SBV e -> Measure t)

-- | Use an injective type family to allow for curried use of regular induction steps. The first argument is the inductive arg that comes separately,
-- and hence is not used in the right-hand side of the equation.
type family IStepArgs a t = result | result -> t where
  IStepArgs ( Forall nx x                                                                                          -> SBool) t =                                               (SBool, TPProofRaw t)
  IStepArgs ( Forall nx x               -> Forall na a                                                             -> SBool) t = (SBV a ->                                     (SBool, TPProofRaw t))
  IStepArgs ( Forall nx x               -> Forall na a -> Forall nb b                                              -> SBool) t = (SBV a -> SBV b                            -> (SBool, TPProofRaw t))
  IStepArgs ( Forall nx x               -> Forall na a -> Forall nb b -> Forall nc c                               -> SBool) t = (SBV a -> SBV b -> SBV c                   -> (SBool, TPProofRaw t))
  IStepArgs ( Forall nx x               -> Forall na a -> Forall nb b -> Forall nc c -> Forall nd d                -> SBool) t = (SBV a -> SBV b -> SBV c -> SBV d          -> (SBool, TPProofRaw t))
  IStepArgs ( Forall nx x               -> Forall na a -> Forall nb b -> Forall nc c -> Forall nd d -> Forall ne e -> SBool) t = (SBV a -> SBV b -> SBV c -> SBV d -> SBV e -> (SBool, TPProofRaw t))
  IStepArgs ((Forall nx x, Forall ny y)                                                                            -> SBool) t =                                               (SBool, TPProofRaw t)
  IStepArgs ((Forall nx x, Forall ny y) -> Forall na a                                                             -> SBool) t = (SBV a ->                                     (SBool, TPProofRaw t))
  IStepArgs ((Forall nx x, Forall ny y) -> Forall na a -> Forall nb b                                              -> SBool) t = (SBV a -> SBV b                            -> (SBool, TPProofRaw t))
  IStepArgs ((Forall nx x, Forall ny y) -> Forall na a -> Forall nb b -> Forall nc c                               -> SBool) t = (SBV a -> SBV b -> SBV c                   -> (SBool, TPProofRaw t))
  IStepArgs ((Forall nx x, Forall ny y) -> Forall na a -> Forall nb b -> Forall nc c -> Forall nd d                -> SBool) t = (SBV a -> SBV b -> SBV c -> SBV d          -> (SBool, TPProofRaw t))
  IStepArgs ((Forall nx x, Forall ny y) -> Forall na a -> Forall nb b -> Forall nc c -> Forall nd d -> Forall ne e -> SBool) t = (SBV a -> SBV b -> SBV c -> SBV d -> SBV e -> (SBool, TPProofRaw t))

-- | A class for doing equational reasoning style calculational proofs. Use 'calc' to prove a given theorem
-- as a sequence of equalities, each step following from the previous.
class Calc a where
  -- | Prove a property via a series of equality steps, using the default solver.
  -- Let @H@ be a list of already established lemmas. Let @P@ be a property we wanted to prove, named @name@.
  -- Consider a call of the form @calc name P (cond, [A, B, C, D]) H@. Note that @H@ is
  -- a list of already proven facts, ensured by the type signature. We proceed as follows:
  --
  --    * Prove: @(H && cond)                                   -> (A == B)@
  --    * Prove: @(H && cond && A == B)                         -> (B == C)@
  --    * Prove: @(H && cond && A == B && B == C)               -> (C == D)@
  --    * Prove: @(H && (cond -> (A == B && B == C && C == D))) -> P@
  --    * If all of the above steps succeed, conclude @P@.
  --
  -- cond acts as the context. Typically, if you are trying to prove @Y -> Z@, then you want cond to be Y.
  -- (This is similar to @intros@ commands in theorem provers.)
  --
  -- So, calc-lemma is essentially modus-ponens, applied in a sequence of stepwise equality reasoning in the case of
  -- non-boolean steps.
  --
  -- If there are no helpers given (i.e., if @H@ is empty), then this call is equivalent to 'lemmaWith'.
  calc :: (Proposition a, EqSymbolic t) => String -> a -> StepArgs a t -> TP (Proof a)

  -- | Prove a property via a series of equality steps, using the given solver.
  calcWith :: (Proposition a, EqSymbolic t) => SMTConfig -> String -> a -> StepArgs a t -> TP (Proof a)

  -- | Internal, shouldn't be needed outside the library
  {-# MINIMAL calcSteps #-}
  calcSteps :: EqSymbolic t => a -> StepArgs a t -> Symbolic (SBool, CalcStrategy)

  calc         nm p steps = getTPConfig >>= \cfg  -> calcWith          cfg                   nm p steps
  calcWith cfg nm p steps = getTPConfig >>= \cfg' -> calcGeneric False (tpMergeCfg cfg cfg') nm p steps

  calcGeneric :: (EqSymbolic t, Proposition a) => Bool -> SMTConfig -> String -> a -> StepArgs a t -> TP (Proof a)
  calcGeneric tagTheorem cfg nm result steps = withProofCache nm $ do
      tpSt <- getTPState
      u    <- tpGetNextUnique

      liftIO $ runSMTWith cfg $ do

         qSaturateSavingObservables result -- make sure we saturate the result, i.e., get all it's UI's, types etc. pop out

         message cfg $ (if tagTheorem then "Theorem" else "Lemma") ++ ": " ++ nm ++ "\n"

         (calcGoal, strategy@CalcStrategy {calcIntros, calcProofTree, calcQCInstance}) <- calcSteps result steps

         -- Collect all subterms and saturate them
         mapM_ qSaturateSavingObservables $ getCalcStrategySaturatables strategy

         query $ proveProofTree cfg tpSt nm (result, calcGoal) calcIntros calcProofTree u calcQCInstance

-- | Prove the proof tree. The arguments are:
--
--      result           : The ultimate goal we want to prove. Note that this is a general proposition, and we don't actually prove it. See the next param.
--      resultBool       : The instance of result that, if we prove it, establishes the result itself
--      initialHypotheses: Hypotheses (conjuncted)
--      calcProofTree    : A tree of steps, which give rise to a bunch of equalities
--
-- Note that we do not check the resultBool is the result itself just "instantiated" appropriately. This is the contract with the caller who
-- has to establish that by whatever means it chooses to do so.
--
-- The final proof we have has the following form:
--
--     - For each "link" in the proofTree, prove that intros .=> link
--     - The above will give us a bunch of results, for each leaf node in the tree.
--     - Then prove: (intros .=> sAnd results) .=> resultBool
--     - Then conclude result, based on what assumption that proving resultBool establishes result
proveProofTree :: Proposition a
               => SMTConfig
               -> TPState
               -> String                                -- ^ the name of the top result
               -> (a, SBool)                            -- ^ goal: as a proposition and as a boolean
               -> SBool                                 -- ^ hypotheses
               -> TPProof                               -- ^ proof tree
               -> TPUnique                              -- ^ unique id
               -> ([Int] -> QC.Args -> Query QC.Result) -- ^ quick-checker
               -> Query (Proof a)
proveProofTree cfg tpSt nm (result, resultBool) initialHypotheses calcProofTree uniq quickCheckInstance = do

  let SMTConfig{tpOptions = TPOptions{printStats}} = cfg
  mbStartTime <- getTimeStampIf printStats

  let next :: [Int] -> [Int]
      next bs = case reverse bs of
                  i : rs -> reverse $ i + 1 : rs
                  []     -> [1]

      isEnd ProofEnd{}    = True
      isEnd ProofStep{}   = False
      isEnd ProofBranch{} = False

      -- trim the branch-name, if we're in a deeper level, and we're at the end
      trimBN level bn | level > 1, 1 : _ <- reverse bn = init bn
                      | True                           = bn

      -- If the next step is ending and we're the 1st step; our number can be skipped
      mkStepName level bn nextStep | isEnd nextStep = map show (trimBN level bn)
                                   | True           = map show bn

      walk :: SBool -> Int -> ([Int], TPProof) -> Query [SBool]

      -- End of proof, return what it established. If there's a hint associated here, it was probably by mistake; so tell it to the user.
      walk intros level (bn, ProofEnd calcResult hs)
         | not (null hs)
         = error $ unlines [ ""
                           , "*** Incorrect calc/induct lemma calculations."
                           , "***"
                           , "***    The last step in the proof has a helper, which isn't used."
                           , "***"
                           , "*** Perhaps the hint is off-by-one in its placement?"
                           ]
         | True
         =  do -- If we're not at the top-level and this is the only step, print it.
               -- Otherwise the noise isn't necessary.
               when (level > 1) $ case reverse bn of
                                    1 : _ -> liftIO $ do tab <- startTP cfg False "Step" level (TPProofStep False nm [] (map show (init bn)))
                                                         finishTP cfg "Q.E.D." (tab, Nothing) []
                                    _     -> pure ()

               pure [intros .=> calcResult]

      -- Do the branches separately and collect the results. If there's coverage needed, we do it too; which
      -- is essentially the assumption here.
      walk intros level (bnTop, ProofBranch checkCompleteness hintStrings ps) = do

        let bn = trimBN level bnTop

            addSuffix xs s = case reverse xs of
                                l : p -> reverse $ (l ++ s) : p
                                []    -> [s]

            full | checkCompleteness = ""
                 | True              = "full "

            stepName = map show bn

        _ <- io $ startTP cfg True "Step" level (TPProofStep False nm hintStrings (addSuffix stepName (" (" ++ show (length ps) ++ " way " ++ full ++ "case split)")))

        results <- concat <$> sequence [walk (intros .&& branchCond) (level + 1) (bn ++ [i, 1], p) | (i, (branchCond, p)) <- zip [1..] ps]

        when checkCompleteness $ smtProofStep cfg tpSt "Step" (level+1)
                                                       (TPProofStep False nm [] (stepName ++ ["Completeness"]))
                                                       (Just intros)
                                                       (sOr (map fst ps))
                                                       (\d -> finishTP cfg "Q.E.D." d [])
        pure results

      -- Do a proof step
      walk intros level (bn, ProofStep cur hs p) = do

           let finish et helpers d = finishTP cfg ("Q.E.D." ++ concludeModulo helpers) d et
               stepName            = mkStepName level bn p

           -- First prove the assumptions, if there are any. We stay quiet, unless timing is asked for
           let (quietCfg, finalizer)
                 | printStats = (cfg,                                              finish [] [])
                 | True       = (cfg{tpOptions = (tpOptions cfg) { quiet = True}}, const (pure ()))

               as = concatMap getHelperAssumes hs
               ss = getHelperText hs
           case as of
             [] -> pure ()
             _  -> smtProofStep quietCfg tpSt "Asms" level
                                         (TPProofStep True nm [] stepName)
                                         (Just intros)
                                         (sAnd as)
                                         finalizer

           -- Are we asked to do quick-check?
           let qcCount = case [i | HelperQC i <- hs] of
                           [] -> Nothing
                           is -> Just (maximum (0 : is))

           extras <- case qcCount of
                       Nothing  -> pure []

                       Just cnt -> do r <- quickCheckInstance bn stdArgs{maxSize = cnt, chatty = False}
                                      liftIO $ do
                                       let err = case r of
                                               QC.Success {}                -> Nothing
                                               QC.Failure {QC.output = out} -> Just out
                                               QC.GaveUp  {}                -> Just "QuickCheck reported \"GaveUp\""    -- can this happen?
                                               QC.NoExpectedFailure {}      -> Just "Expected failure but test passed." -- can't happen
                                       case err of
                                         Just e  -> do putStrLn $ "\n*** QuickCheck failed for " ++ intercalate "." (nm : stepName)
                                                       putStrLn e
                                                       error "Failed"

                                         Nothing -> -- prove by qc proof so it gets recorded
                                                    pure [quickCheckProof]
           -- Now prove the step
           let by = concatMap getHelperProofs hs ++ extras

           smtProofStep cfg tpSt "Step" level
                            (TPProofStep False nm ss stepName)
                            (Just (sAnd (intros : as ++ map getObjProof by)))
                            cur
                            (finish [] by)

           -- Move to next
           walk intros level (next bn, p)

  results <- walk initialHypotheses 1 ([1], calcProofTree)

  queryDebug [nm ++ ": Proof end: proving the result:"]

  smtProofStep cfg tpSt "Result" 1
               (TPProofStep False nm [] [""])
               (Just (initialHypotheses .=> sAnd results))
               resultBool $ \d ->
                 do mbElapsed <- getElapsedTime mbStartTime
                    let modulo = concludeModulo (concatMap getHelperProofs (getAllHelpers calcProofTree))
                    finishTP cfg ("Q.E.D." ++ modulo) d (catMaybes [mbElapsed])

                    pure $ Proof $ ProofObj { dependencies = getDependencies calcProofTree
                                            , isUserAxiom  = False
                                            , getObjProof  = label nm (quantifiedBool result)
                                            , getProp      = toDyn result
                                            , proofName    = nm
                                            , uniqId       = uniq
                                            , isCached     = False
                                            }

-- Helper data-type for calc-step below
data CalcContext a = CalcStart     [Helper] -- Haven't started yet
                   | CalcStep  a a [Helper] -- Intermediate step: first value, prev value

-- | Turn a sequence of steps into a chain of equalities
mkCalcSteps :: EqSymbolic a => (SBool, TPProofRaw a) -> ([Int] -> QC.Args -> Query QC.Result) -> CalcStrategy
mkCalcSteps (intros, tpp) qcInstance = CalcStrategy { calcIntros     = intros
                                                    , calcProofTree  = go (CalcStart []) tpp
                                                    , calcQCInstance = qcInstance
                                                    }
  where go :: EqSymbolic a => CalcContext a -> TPProofRaw a -> TPProof

        -- End of the proof; tie the begin and end
        go step (ProofEnd () hs) = case step of
                                     -- It's tempting to error out if we're at the start and already reached the end
                                     -- This means we're given a sequence of no-steps. While this is useless in the
                                     -- general case, it's quite valid in a case-split; where one of the case-splits
                                     -- might be easy enough for the solver to deduce so the user simply says "just derive it for me."
                                     CalcStart hs'          -> ProofEnd sTrue           (hs' ++ hs) -- Nothing proven!
                                     CalcStep begin end hs' -> ProofEnd (begin .== end) (hs' ++ hs)

        -- Branch: Just push it down. We use the hints from previous step, and pass the current ones down.
        go step (ProofBranch c hs ps) = ProofBranch c (getHelperText hs) [(branchCond, go step' p) | (branchCond, p) <- ps]
           where step' = case step of
                           CalcStart hs'     -> CalcStart (hs' ++ hs)
                           CalcStep  a b hs' -> CalcStep a b (hs' ++ hs)

        -- Step:
        go (CalcStart hs)           (ProofStep cur hs' p) =                               go (CalcStep cur   cur (hs' ++ hs)) p
        go (CalcStep first prev hs) (ProofStep cur hs' p) = ProofStep (prev  .== cur) hs (go (CalcStep first cur hs')         p)

-- | Quick-check wrapper. Internal use only.
class QCWrap a where
  quick :: a -> [Int] -> QC.Args -> Query QC.Result

-- | Given initial hypothesis, and a raw proof tree, build the quick-check walk over this tree
-- for the step that's marked as such.
qcWalk :: [Int] -> (SBool, TPProofRaw t) -> Query SBool
qcWalk step = error $ "I wish I knew how to implement qcWalk. I'm at: " ++ show step

-- Regular Calc instances
instance QCWrap (SBool, TPProofRaw t) where
  quick r step qcArgs = do t <- qcWalk step r
                           liftIO (quickCheckWithResult qcArgs t)

-- Inductive proofs over lists
instance SymVal x => QCWrap (Proof unused -> (SBV x, SList x) -> (SBool, TPProofRaw t)) where
  quick r step qcArgs = do let p = error "Unsupported: QuickCheck: Shouldn't be referring to the proof arg! (list case)"
                           x  <- freshVar_
                           xs <- freshVar_
                           t  <- qcWalk step (r p (x, xs))
                           liftIO (quickCheckWithResult qcArgs t)

-- Inductive proofs over two lists
instance (SymVal x, SymVal y) => QCWrap (Proof unused -> (SBV x, SList x, SBV y, SList y) -> (SBool, TPProofRaw t)) where
  quick r step qcArgs = do let p = error "Unsupported: QuickCheck: Shouldn't be referring to the proof arg! (list case)"
                           x  <- freshVar_
                           xs <- freshVar_
                           y  <- freshVar_
                           ys <- freshVar_
                           t  <- qcWalk step (r p (x, xs, y, ys))
                           liftIO (quickCheckWithResult qcArgs t)

-- Strong induction
instance QCWrap (Proof unused -> (SBool, TPProofRaw t)) where
  quick r step qcArgs = do let p = error "Unsupported: QuickCheck: Shouldn't be referring to the proof arg! (list case)"
                           t  <- qcWalk step (r p)
                           liftIO (quickCheckWithResult qcArgs t)

-- | Instances that extend quick-check to arbitrary number of elements
instance (SymVal a, QCWrap r) => QCWrap (SBV a -> r) where
  quick f step args = freshVar_ >>= \v -> quick (f v) step args

instance (SymVal x, SymVal a, QCWrap (Proof unused -> (SBV x, SList x) -> r)) => QCWrap (Proof unused -> (SBV x, SList x) -> SBV a -> r) where
  quick f step args = freshVar_ >>= \v -> quick (\p i -> (f p i v)) step args

instance (SymVal x, SymVal y, SymVal a, QCWrap (Proof unused -> (SBV x, SList x, SBV y, SList y) -> r)) => QCWrap (Proof unused -> (SBV x, SList x, SBV y, SList y) -> SBV a -> r) where
  quick f step args = freshVar_ >>= \v -> quick (\p i -> (f p i v)) step args

instance (SymVal a, QCWrap (Proof unused -> r)) => QCWrap (Proof unused -> SBV a -> r) where
  quick f step args = freshVar_ >>= \v -> quick (\p -> (f p v)) step args

-- | Chaining lemmas that depend on no extra variables
instance Calc SBool where
   calcSteps result steps = pure (result, mkCalcSteps steps (quick steps))

-- | Chaining lemmas that depend on a single extra variable.
instance (KnownSymbol na, SymVal a) => Calc (Forall na a -> SBool) where
   calcSteps result steps = do a <- free (symbolVal (Proxy @na))
                               pure (result (Forall a), mkCalcSteps (steps a) (quick steps))

-- | Chaining lemmas that depend on two extra variables.
instance (KnownSymbol na, SymVal a, KnownSymbol nb, SymVal b) => Calc (Forall na a -> Forall nb b -> SBool) where
   calcSteps result steps = do (a, b) <- (,) <$> free (symbolVal (Proxy @na)) <*> free (symbolVal (Proxy @nb))
                               pure (result (Forall a) (Forall b), mkCalcSteps (steps a b) (quick steps))

-- | Chaining lemmas that depend on three extra variables.
instance (KnownSymbol na, SymVal a, KnownSymbol nb, SymVal b, KnownSymbol nc, SymVal c) => Calc (Forall na a -> Forall nb b -> Forall nc c -> SBool) where
   calcSteps result steps = do (a, b, c) <- (,,) <$> free (symbolVal (Proxy @na)) <*> free (symbolVal (Proxy @nb)) <*> free (symbolVal (Proxy @nc))
                               pure (result (Forall a) (Forall b) (Forall c), mkCalcSteps (steps a b c) (quick steps))

-- | Chaining lemmas that depend on four extra variables.
instance (KnownSymbol na, SymVal a, KnownSymbol nb, SymVal b, KnownSymbol nc, SymVal c, KnownSymbol nd, SymVal d) => Calc (Forall na a -> Forall nb b -> Forall nc c -> Forall nd d -> SBool) where
   calcSteps result steps = do (a, b, c, d) <- (,,,) <$> free (symbolVal (Proxy @na)) <*> free (symbolVal (Proxy @nb)) <*> free (symbolVal (Proxy @nc)) <*> free (symbolVal (Proxy @nd))
                               pure (result (Forall a) (Forall b) (Forall c) (Forall d), mkCalcSteps (steps a b c d) (quick steps))

-- | Chaining lemmas that depend on five extra variables.
instance (KnownSymbol na, SymVal a, KnownSymbol nb, SymVal b, KnownSymbol nc, SymVal c, KnownSymbol nd, SymVal d, KnownSymbol ne, SymVal e)
      => Calc (Forall na a -> Forall nb b -> Forall nc c -> Forall nd d -> Forall ne e -> SBool) where
   calcSteps result steps = do (a, b, c, d, e) <- (,,,,) <$> free (symbolVal (Proxy @na)) <*> free (symbolVal (Proxy @nb)) <*> free (symbolVal (Proxy @nc)) <*> free (symbolVal (Proxy @nd)) <*> free (symbolVal (Proxy @ne))
                               pure (result (Forall a) (Forall b) (Forall c) (Forall d) (Forall e), mkCalcSteps (steps a b c d e) (quick steps))

-- | Captures the schema for an inductive proof. Base case might be nothing, to cover strong induction.
data InductionStrategy = InductionStrategy { inductionIntros     :: SBool
                                           , inductionMeasure    :: Maybe SBool
                                           , inductionBaseCase   :: Maybe SBool
                                           , inductionProofTree  :: TPProof
                                           , inductiveStep       :: SBool
                                           , inductiveQCInstance :: [Int] -> QC.Args -> Query QC.Result
                                           }

-- | Are we doing regular induction or measure based general induction?
data InductionStyle = RegularInduction | GeneralInduction

getInductionStrategySaturatables :: InductionStrategy -> [SBool]
getInductionStrategySaturatables (InductionStrategy inductionIntros
                                                    inductionMeasure
                                                    inductionBaseCase
                                                    inductionProofSteps
                                                    inductiveStep
                                                    _inductiveQCInstance)
  = inductionIntros : inductiveStep : proofTreeSaturatables inductionProofSteps ++ maybeToList inductionBaseCase ++ maybeToList inductionMeasure

-- | A class for doing regular inductive proofs.
class Inductive a where
   type IHType a :: Type
   type IHArg  a :: Type

   -- | Inductively prove a lemma, using the default config.
   -- Inductive proofs over lists only hold for finite lists. We also assume that all functions involved are terminating. SBV does not prove termination, so only
   -- partial correctness is guaranteed if non-terminating functions are involved.
   induct  :: (Proposition a, EqSymbolic t) => String -> a -> (Proof (IHType a) -> IHArg a -> IStepArgs a t) -> TP (Proof a)

   -- | Same as 'induct', but with the given solver configuration.
   -- Inductive proofs over lists only hold for finite lists. We also assume that all functions involved are terminating. SBV does not prove termination, so only
   -- partial correctness is guaranteed if non-terminating functions are involved.
   inductWith :: (Proposition a, EqSymbolic t) => SMTConfig -> String -> a -> (Proof (IHType a) -> IHArg a -> IStepArgs a t) -> TP (Proof a)

   induct         nm p steps = getTPConfig >>= \cfg  -> inductWith                             cfg                   nm p steps
   inductWith cfg nm p steps = getTPConfig >>= \cfg' -> inductionEngine RegularInduction False (tpMergeCfg cfg cfg') nm p (inductionStrategy p steps)

   -- | Internal, shouldn't be needed outside the library
   {-# MINIMAL inductionStrategy #-}
   inductionStrategy :: (Proposition a, EqSymbolic t) => a -> (Proof (IHType a) -> IHArg a -> IStepArgs a t) -> Symbolic InductionStrategy

-- | A class of values, capturing the zero of a measure value
class OrdSymbolic a => Zero a where
  zero :: Measure a

-- | An integer as a measure
instance Zero SInteger where
   zero = Measure 0

-- | A tuple of integers as a measure
instance Zero (SInteger, SInteger) where
  zero = Measure (0, 0)

-- | A triple of integers as a measure
instance Zero (SInteger, SInteger, SInteger) where
  zero = Measure (0, 0, 0)

-- | A quadruple of integers as a measure
instance Zero (SInteger, SInteger, SInteger, SInteger) where
  zero = Measure (0, 0, 0, 0)

instance Zero (SInteger, SInteger, SInteger, SInteger, SInteger) where
  zero = Measure (0, 0, 0, 0, 0)

-- | A class for doing generalized measure based strong inductive proofs.
class SInductive a where
   -- | Inductively prove a lemma, using measure based induction, using the default config.
   -- Inductive proofs over lists only hold for finite lists. We also assume that all functions involved are terminating. SBV does not prove termination, so only
   -- partial correctness is guaranteed if non-terminating functions are involved.
   sInduct :: (Proposition a, Zero m, EqSymbolic t) => String -> a -> MeasureArgs a m -> (Proof a -> StepArgs a t) -> TP (Proof a)

   -- | Same as 'sInduct', but with the given solver configuration.
   -- Inductive proofs over lists only hold for finite lists. We also assume that all functions involved are terminating. SBV does not prove termination, so only
   -- partial correctness is guaranteed if non-terminating functions are involved.
   sInductWith :: (Proposition a, Zero m, EqSymbolic t) => SMTConfig -> String -> a -> MeasureArgs a m -> (Proof a -> StepArgs a t) -> TP (Proof a)

   sInduct         nm p m steps = getTPConfig >>= \cfg  -> sInductWith                            cfg                   nm p m steps
   sInductWith cfg nm p m steps = getTPConfig >>= \cfg' -> inductionEngine GeneralInduction False (tpMergeCfg cfg cfg') nm p (sInductionStrategy p m steps)

   -- | Internal, shouldn't be needed outside the library
   {-# MINIMAL sInductionStrategy #-}
   sInductionStrategy :: (Proposition a, Zero m, EqSymbolic t) => a -> MeasureArgs a m -> (Proof a -> StepArgs a t) -> Symbolic InductionStrategy

-- | Do an inductive proof, based on the given strategy
inductionEngine :: Proposition a => InductionStyle -> Bool -> SMTConfig -> String -> a -> Symbolic InductionStrategy -> TP (Proof a)
inductionEngine style tagTheorem cfg nm result getStrategy = withProofCache nm $ do
   tpSt <- getTPState
   u    <- tpGetNextUnique

   liftIO $ runSMTWith cfg $ do

      qSaturateSavingObservables result -- make sure we saturate the result, i.e., get all it's UI's, types etc. pop out

      let qual = case style of
                   RegularInduction -> ""
                   GeneralInduction  -> " (strong)"

      message cfg $ "Inductive " ++ (if tagTheorem then "theorem" else "lemma") ++ qual ++ ": " ++ nm ++ "\n"

      strategy@InductionStrategy { inductionIntros
                                 , inductionMeasure
                                 , inductionBaseCase
                                 , inductionProofTree
                                 , inductiveStep
                                 , inductiveQCInstance
                                 } <- getStrategy

      mapM_ qSaturateSavingObservables $ getInductionStrategySaturatables strategy

      query $ do

       case inductionMeasure of
          Nothing -> queryDebug [nm ++ ": Induction" ++ qual ++ ", there is no custom measure to show non-negativeness."]
          Just ms -> do queryDebug [nm ++ ": Induction, proving measure is always non-negative:"]
                        smtProofStep cfg tpSt "Step" 1
                                              (TPProofStep False nm [] ["Measure is non-negative"])
                                              (Just inductionIntros)
                                              ms
                                              (\d -> finishTP cfg "Q.E.D." d [])
       case inductionBaseCase of
          Nothing -> queryDebug [nm ++ ": Induction" ++ qual ++ ", there is no base case to prove."]
          Just bc -> do queryDebug [nm ++ ": Induction, proving base case:"]
                        smtProofStep cfg tpSt "Step" 1
                                              (TPProofStep False nm [] ["Base"])
                                              (Just inductionIntros)
                                              bc
                                              (\d -> finishTP cfg "Q.E.D." d [])

       proveProofTree cfg tpSt nm (result, inductiveStep) inductionIntros inductionProofTree u inductiveQCInstance

-- Induction strategy helper
mkIndStrategy :: EqSymbolic a => Maybe SBool -> Maybe SBool -> (SBool, TPProofRaw a) -> SBool -> ([Int] -> QC.Args -> Query QC.Result) -> InductionStrategy
mkIndStrategy mbMeasure mbBaseCase indSteps step indQCInstance =
        let CalcStrategy { calcIntros, calcProofTree, calcQCInstance } = mkCalcSteps indSteps indQCInstance
        in InductionStrategy { inductionIntros     = calcIntros
                             , inductionMeasure    = mbMeasure
                             , inductionBaseCase   = mbBaseCase
                             , inductionProofTree  = calcProofTree
                             , inductiveStep       = step
                             , inductiveQCInstance = calcQCInstance
                             }

-- | Create a new variable with the given name, return both the variable and the name
mkVar :: (KnownSymbol n, SymVal a) => proxy n -> Symbolic (SBV a, String)
mkVar x = do let nn = symbolVal x
             n <- free nn
             pure (n, nn)

-- | Create a new variable with the given name, return both the variable and the name. List version.
mkLVar :: (KnownSymbol n, SymVal a) => proxy n -> Symbolic (SBV a, SList a, String)
mkLVar x = do let nxs = symbolVal x
                  nx  = singular nxs
              e  <- free nx
              es <- free nxs
              pure (e, es, nx ++ ":" ++ nxs)

-- | Helper for induction result
indResult :: [String] -> SBool -> SBool
indResult nms = observeIf not ("P(" ++ intercalate ", " nms ++ ")")

-- | Induction over 'SInteger'
instance KnownSymbol nn => Inductive (Forall nn Integer -> SBool) where
  type IHType (Forall nn Integer -> SBool) = SBool
  type IHArg  (Forall nn Integer -> SBool) = SInteger

  inductionStrategy result steps = do
       (n, nn) <- mkVar (Proxy @nn)
       pure $ mkIndStrategy Nothing
                            (Just (result (Forall 0)))
                            (steps (internalAxiom "IH" (Measure n .>= zero .=> result (Forall n))) n)
                            (indResult [nn ++ "+1"] (result (Forall (n+1))))
                            (quick steps)

-- | Induction over 'SInteger', taking an extra argument
instance (KnownSymbol nn, KnownSymbol na, SymVal a) => Inductive (Forall nn Integer -> Forall na a -> SBool) where
  type IHType (Forall nn Integer -> Forall na a -> SBool) = Forall na a -> SBool
  type IHArg  (Forall nn Integer -> Forall na a -> SBool) = SInteger

  inductionStrategy result steps = do
       (n, nn) <- mkVar (Proxy @nn)
       (a, na) <- mkVar (Proxy @na)
       pure $ mkIndStrategy Nothing
                            (Just (result (Forall 0) (Forall a)))
                            (steps (internalAxiom "IH" (\(Forall a' :: Forall na a) -> Measure n .>= zero .=> result (Forall n) (Forall a'))) n a)
                            (indResult [nn ++ "+1", na] (result (Forall (n+1)) (Forall a)))
                            (quick steps)

-- | Induction over 'SInteger', taking two extra arguments
instance (KnownSymbol nn, KnownSymbol na, SymVal a, KnownSymbol nb, SymVal b) => Inductive (Forall nn Integer -> Forall na a -> Forall nb b -> SBool) where
  type IHType (Forall nn Integer -> Forall na a -> Forall nb b -> SBool) = Forall na a -> Forall nb b -> SBool
  type IHArg  (Forall nn Integer -> Forall na a -> Forall nb b -> SBool) = SInteger

  inductionStrategy result steps = do
       (n, nn) <- mkVar (Proxy @nn)
       (a, na) <- mkVar (Proxy @na)
       (b, nb) <- mkVar (Proxy @nb)
       pure $ mkIndStrategy Nothing
                            (Just (result (Forall 0) (Forall a) (Forall b)))
                            (steps (internalAxiom "IH" (\(Forall a' :: Forall na a) (Forall b' :: Forall nb b) -> Measure n .>= zero .=> result (Forall n) (Forall a') (Forall b'))) n a b)
                            (indResult [nn ++ "+1", na, nb] (result (Forall (n+1)) (Forall a) (Forall b)))
                            (quick steps)

-- | Induction over 'SInteger', taking three extra arguments
instance (KnownSymbol nn, KnownSymbol na, SymVal a, KnownSymbol nb, SymVal b, KnownSymbol nc, SymVal c) => Inductive (Forall nn Integer -> Forall na a -> Forall nb b -> Forall nc c -> SBool) where
  type IHType (Forall nn Integer -> Forall na a -> Forall nb b -> Forall nc c -> SBool) = Forall na a -> Forall nb b -> Forall nc c -> SBool
  type IHArg  (Forall nn Integer -> Forall na a -> Forall nb b -> Forall nc c -> SBool) = SInteger

  inductionStrategy result steps = do
       (n, nn) <- mkVar (Proxy @nn)
       (a, na) <- mkVar (Proxy @na)
       (b, nb) <- mkVar (Proxy @nb)
       (c, nc) <- mkVar (Proxy @nc)
       pure $ mkIndStrategy Nothing
                            (Just (result (Forall 0) (Forall a) (Forall b) (Forall c)))
                            (steps (internalAxiom "IH" (\(Forall a' :: Forall na a) (Forall b' :: Forall nb b) (Forall c' :: Forall nc c) -> Measure n .>= zero .=> result (Forall n) (Forall a') (Forall b') (Forall c'))) n a b c)
                            (indResult [nn ++ "+1", na, nb, nc] (result (Forall (n+1)) (Forall a) (Forall b) (Forall c)))
                            (quick steps)

-- | Induction over 'SInteger', taking four extra arguments
instance (KnownSymbol nn, KnownSymbol na, SymVal a, KnownSymbol nb, SymVal b, KnownSymbol nc, SymVal c, KnownSymbol nd, SymVal d) => Inductive (Forall nn Integer -> Forall na a -> Forall nb b -> Forall nc c -> Forall nd d -> SBool) where
  type IHType (Forall nn Integer -> Forall na a -> Forall nb b -> Forall nc c -> Forall nd d -> SBool) = Forall na a -> Forall nb b -> Forall nc c -> Forall nd d -> SBool
  type IHArg  (Forall nn Integer -> Forall na a -> Forall nb b -> Forall nc c -> Forall nd d -> SBool) = SInteger

  inductionStrategy result steps = do
       (n, nn) <- mkVar (Proxy @nn)
       (a, na) <- mkVar (Proxy @na)
       (b, nb) <- mkVar (Proxy @nb)
       (c, nc) <- mkVar (Proxy @nc)
       (d, nd) <- mkVar (Proxy @nd)
       pure $ mkIndStrategy Nothing
                            (Just (result (Forall 0) (Forall a) (Forall b) (Forall c) (Forall d)))
                            (steps (internalAxiom "IH" (\(Forall a' :: Forall na a) (Forall b' :: Forall nb b) (Forall c' :: Forall nc c) (Forall d' :: Forall nd d) -> Measure n .>= zero .=> result (Forall n) (Forall a') (Forall b') (Forall c') (Forall d'))) n a b c d)
                            (indResult [nn ++ "+1", na, nb, nc, nd] (result (Forall (n+1)) (Forall a) (Forall b) (Forall c) (Forall d)))
                            (quick steps)

-- | Induction over 'SInteger', taking five extra arguments
instance (KnownSymbol nn, KnownSymbol na, SymVal a, KnownSymbol nb, SymVal b, KnownSymbol nc, SymVal c, KnownSymbol nd, SymVal d, KnownSymbol ne, SymVal e) => Inductive (Forall nn Integer -> Forall na a -> Forall nb b -> Forall nc c -> Forall nd d -> Forall ne e -> SBool) where
  type IHType (Forall nn Integer -> Forall na a -> Forall nb b -> Forall nc c -> Forall nd d -> Forall ne e -> SBool) = Forall na a -> Forall nb b -> Forall nc c -> Forall nd d -> Forall ne e -> SBool
  type IHArg  (Forall nn Integer -> Forall na a -> Forall nb b -> Forall nc c -> Forall nd d -> Forall ne e -> SBool) = SInteger

  inductionStrategy result steps = do
       (n, nn) <- mkVar (Proxy @nn)
       (a, na) <- mkVar (Proxy @na)
       (b, nb) <- mkVar (Proxy @nb)
       (c, nc) <- mkVar (Proxy @nc)
       (d, nd) <- mkVar (Proxy @nd)
       (e, ne) <- mkVar (Proxy @ne)
       pure $ mkIndStrategy Nothing
                            (Just (result (Forall 0) (Forall a) (Forall b) (Forall c) (Forall d) (Forall e)))
                            (steps (internalAxiom "IH" (\(Forall a' :: Forall na a) (Forall b' :: Forall nb b) (Forall c' :: Forall nc c) (Forall d' :: Forall nd d) (Forall e' :: Forall ne e) -> Measure n .>= zero .=> result (Forall n) (Forall a') (Forall b') (Forall c') (Forall d') (Forall e'))) n a b c d e)
                            (indResult [nn ++ "+1", na, nb, nc, nd, ne] (result (Forall (n+1)) (Forall a) (Forall b) (Forall c) (Forall d) (Forall e)))
                            (quick steps)

-- Given a user name for the list, get a name for the element, in the most suggestive way possible
--   xs  -> x
--   xss -> xs
--   foo -> fooElt
singular :: String -> String
singular n = case reverse n of
               's':_:_ -> init n
               _       -> n ++ "Elt"

-- | Induction over 'SList'
instance (KnownSymbol nxs, SymVal x) => Inductive (Forall nxs [x] -> SBool) where
  type IHType (Forall nxs [x] -> SBool) = SBool
  type IHArg  (Forall nxs [x] -> SBool) = (SBV x, SList x)

  inductionStrategy result steps = do
       (x, xs, nxxs) <- mkLVar (Proxy @nxs)
       pure $ mkIndStrategy Nothing
                            (Just (result (Forall SL.nil)))
                            (steps (internalAxiom "IH" (result (Forall xs))) (x, xs))
                            (indResult [nxxs] (result (Forall (x SL..: xs))))
                            (quick steps)

-- | Induction over 'SList', taking an extra argument
instance (KnownSymbol nxs, SymVal x, KnownSymbol na, SymVal a) => Inductive (Forall nxs [x] -> Forall na a -> SBool) where
  type IHType (Forall nxs [x] -> Forall na a -> SBool) = Forall na a -> SBool
  type IHArg  (Forall nxs [x] -> Forall na a -> SBool) = (SBV x, SList x)

  inductionStrategy result steps = do
       (x, xs, nxxs) <- mkLVar (Proxy @nxs)
       (a, na)       <- mkVar  (Proxy @na)
       pure $ mkIndStrategy Nothing
                            (Just (result (Forall SL.nil) (Forall a)))
                            (steps (internalAxiom "IH" (\(Forall a' :: Forall na a) -> result (Forall xs) (Forall a'))) (x, xs) a)
                            (indResult [nxxs, na] (result (Forall (x SL..: xs)) (Forall a)))
                            (quick steps)

-- | Induction over 'SList', taking two extra arguments
instance (KnownSymbol nxs, SymVal x, KnownSymbol na, SymVal a, KnownSymbol nb, SymVal b) => Inductive (Forall nxs [x] -> Forall na a -> Forall nb b -> SBool) where
  type IHType (Forall nxs [x] -> Forall na a -> Forall nb b -> SBool) = Forall na a -> Forall nb b -> SBool
  type IHArg  (Forall nxs [x] -> Forall na a -> Forall nb b -> SBool) = (SBV x, SList x)

  inductionStrategy result steps = do
       (x, xs, nxxs) <- mkLVar (Proxy @nxs)
       (a, na)       <- mkVar  (Proxy @na)
       (b, nb)       <- mkVar  (Proxy @nb)
       pure $ mkIndStrategy Nothing
                            (Just (result (Forall SL.nil) (Forall a) (Forall b)))
                            (steps (internalAxiom "IH" (\(Forall a' :: Forall na a) (Forall b' :: Forall nb b) -> result (Forall xs) (Forall a') (Forall b'))) (x, xs) a b)
                            (indResult [nxxs, na, nb] (result (Forall (x SL..: xs)) (Forall a) (Forall b)))
                            (quick steps)

-- | Induction over 'SList', taking three extra arguments
instance (KnownSymbol nxs, SymVal x, KnownSymbol na, SymVal a, KnownSymbol nb, SymVal b, KnownSymbol nc, SymVal c) => Inductive (Forall nxs [x] -> Forall na a -> Forall nb b -> Forall nc c -> SBool) where
  type IHType (Forall nxs [x] -> Forall na a -> Forall nb b -> Forall nc c -> SBool) = Forall na a -> Forall nb b -> Forall nc c -> SBool
  type IHArg  (Forall nxs [x] -> Forall na a -> Forall nb b -> Forall nc c -> SBool) = (SBV x, SList x)

  inductionStrategy result steps = do
       (x, xs, nxxs) <- mkLVar (Proxy @nxs)
       (a, na)       <- mkVar  (Proxy @na)
       (b, nb)       <- mkVar  (Proxy @nb)
       (c, nc)       <- mkVar  (Proxy @nc)
       pure $ mkIndStrategy Nothing
                            (Just (result (Forall SL.nil) (Forall a) (Forall b) (Forall c)))
                            (steps (internalAxiom "IH" (\(Forall a' :: Forall na a) (Forall b' :: Forall nb b) (Forall c' :: Forall nc c) -> result (Forall xs) (Forall a') (Forall b') (Forall c'))) (x, xs) a b c)
                            (indResult [nxxs, na, nb, nc] (result (Forall (x SL..: xs)) (Forall a) (Forall b) (Forall c)))
                            (quick steps)

-- | Induction over 'SList', taking four extra arguments
instance (KnownSymbol nxs, SymVal x, KnownSymbol na, SymVal a, KnownSymbol nb, SymVal b, KnownSymbol nc, SymVal c, KnownSymbol nd, SymVal d) => Inductive (Forall nxs [x] -> Forall na a -> Forall nb b -> Forall nc c -> Forall nd d -> SBool) where
  type IHType (Forall nxs [x] -> Forall na a -> Forall nb b -> Forall nc c -> Forall nd d -> SBool) = Forall na a -> Forall nb b -> Forall nc c -> Forall nd d -> SBool
  type IHArg  (Forall nxs [x] -> Forall na a -> Forall nb b -> Forall nc c -> Forall nd d -> SBool) = (SBV x, SList x)

  inductionStrategy result steps = do
       (x, xs, nxxs) <- mkLVar (Proxy @nxs)
       (a, na)       <- mkVar  (Proxy @na)
       (b, nb)       <- mkVar  (Proxy @nb)
       (c, nc)       <- mkVar  (Proxy @nc)
       (d, nd)       <- mkVar  (Proxy @nd)
       pure $ mkIndStrategy Nothing
                            (Just (result (Forall SL.nil) (Forall a) (Forall b) (Forall c) (Forall d)))
                            (steps (internalAxiom "IH" (\(Forall a' :: Forall na a) (Forall b' :: Forall nb b) (Forall c' :: Forall nc c) (Forall d' :: Forall nd d) -> result (Forall xs) (Forall a') (Forall b') (Forall c') (Forall d'))) (x, xs) a b c d)
                            (indResult [nxxs, na, nb, nc, nd] (result (Forall (x SL..: xs)) (Forall a) (Forall b) (Forall c) (Forall d)))
                            (quick steps)

-- | Induction over 'SList', taking five extra arguments
instance (KnownSymbol nxs, SymVal x, KnownSymbol na, SymVal a, KnownSymbol nb, SymVal b, KnownSymbol nc, SymVal c, KnownSymbol nd, SymVal d, KnownSymbol ne, SymVal e) => Inductive (Forall nxs [x] -> Forall na a -> Forall nb b -> Forall nc c -> Forall nd d -> Forall ne e -> SBool) where
  type IHType (Forall nxs [x] -> Forall na a -> Forall nb b -> Forall nc c -> Forall nd d -> Forall ne e -> SBool) = Forall na a -> Forall nb b -> Forall nc c -> Forall nd d -> Forall ne e -> SBool
  type IHArg  (Forall nxs [x] -> Forall na a -> Forall nb b -> Forall nc c -> Forall nd d -> Forall ne e -> SBool) = (SBV x, SList x)

  inductionStrategy result steps = do
       (x, xs, nxxs) <- mkLVar (Proxy @nxs)
       (a, na)       <- mkVar  (Proxy @na)
       (b, nb)       <- mkVar  (Proxy @nb)
       (c, nc)       <- mkVar  (Proxy @nc)
       (d, nd)       <- mkVar  (Proxy @nd)
       (e, ne)       <- mkVar  (Proxy @ne)
       pure $ mkIndStrategy Nothing
                            (Just (result (Forall SL.nil) (Forall a) (Forall b) (Forall c) (Forall d) (Forall e)))
                            (steps (internalAxiom "IH" (\(Forall a' :: Forall na a) (Forall b' :: Forall nb b) (Forall c' :: Forall nc c) (Forall d' :: Forall nd d) (Forall e' :: Forall ne e) -> result (Forall xs) (Forall a') (Forall b') (Forall c') (Forall d') (Forall e'))) (x, xs) a b c d e)
                            (indResult [nxxs, na, nb, nc, nd, ne] (result (Forall (x SL..: xs)) (Forall a) (Forall b) (Forall c) (Forall d) (Forall e)))
                            (quick steps)

-- | Induction over two 'SList', simultaneously
instance (KnownSymbol nxs, SymVal x, KnownSymbol nys, SymVal y) => Inductive ((Forall nxs [x], Forall nys [y]) -> SBool) where
  type IHType ((Forall nxs [x], Forall nys [y]) -> SBool) = SBool
  type IHArg  ((Forall nxs [x], Forall nys [y]) -> SBool) = (SBV x, SList x, SBV y, SList y)

  inductionStrategy result steps = do
       (x, xs, nxxs) <- mkLVar (Proxy @nxs)
       (y, ys, nyys) <- mkLVar (Proxy @nys)
       pure $ mkIndStrategy Nothing
                            (Just (result (Forall SL.nil, Forall SL.nil) .&& result (Forall SL.nil, Forall (y SL..: ys)) .&& result (Forall (x SL..: xs), Forall SL.nil)))
                            (steps (internalAxiom "IH" (result (Forall xs, Forall ys))) (x, xs, y, ys))
                            (indResult [nxxs, nyys] (result (Forall (x SL..: xs), Forall (y SL..: ys))))
                            (quick steps)

-- | Induction over two 'SList', simultaneously, taking an extra argument
instance (KnownSymbol nxs, SymVal x, KnownSymbol nys, SymVal y, KnownSymbol na, SymVal a) => Inductive ((Forall nxs [x], Forall nys [y]) -> Forall na a -> SBool) where
  type IHType ((Forall nxs [x], Forall nys [y]) -> Forall na a -> SBool) = Forall na a -> SBool
  type IHArg  ((Forall nxs [x], Forall nys [y]) -> Forall na a -> SBool) = (SBV x, SList x, SBV y, SList y)

  inductionStrategy result steps = do
       (x, xs, nxxs) <- mkLVar (Proxy @nxs)
       (y, ys, nyys) <- mkLVar (Proxy @nys)
       (a, na)       <- mkVar  (Proxy @na)
       pure $ mkIndStrategy Nothing
                            (Just (result (Forall SL.nil, Forall SL.nil) (Forall a) .&& result (Forall SL.nil, Forall (y SL..: ys)) (Forall a) .&& result (Forall (x SL..: xs), Forall SL.nil) (Forall a)))
                            (steps (internalAxiom "IH" (\(Forall a' :: Forall na a) -> result (Forall xs, Forall ys) (Forall a'))) (x, xs, y, ys) a)
                            (indResult [nxxs, nyys, na] (result (Forall (x SL..: xs), Forall (y SL..: ys)) (Forall a)))
                            (quick steps)

-- | Induction over two 'SList', simultaneously, taking two extra arguments
instance (KnownSymbol nxs, SymVal x, KnownSymbol nys, SymVal y, KnownSymbol na, SymVal a, KnownSymbol nb, SymVal b) => Inductive ((Forall nxs [x], Forall nys [y]) -> Forall na a -> Forall nb b -> SBool) where
  type IHType ((Forall nxs [x], Forall nys [y]) -> Forall na a -> Forall nb b -> SBool) = Forall na a -> Forall nb b -> SBool
  type IHArg  ((Forall nxs [x], Forall nys [y]) -> Forall na a -> Forall nb b -> SBool) = (SBV x, SList x, SBV y, SList y)

  inductionStrategy result steps = do
       (x, xs, nxxs) <- mkLVar (Proxy @nxs)
       (y, ys, nyys) <- mkLVar (Proxy @nys)
       (a, na)       <- mkVar  (Proxy @na)
       (b, nb)       <- mkVar  (Proxy @nb)
       pure $ mkIndStrategy Nothing
                            (Just (result (Forall SL.nil, Forall SL.nil) (Forall a) (Forall b) .&& result (Forall SL.nil, Forall (y SL..: ys)) (Forall a) (Forall b) .&& result (Forall (x SL..: xs), Forall SL.nil) (Forall a) (Forall b)))
                            (steps (internalAxiom "IH" (\(Forall a' :: Forall na a) (Forall b' :: Forall nb b) -> result (Forall xs, Forall ys) (Forall a') (Forall b'))) (x, xs, y, ys) a b)
                            (indResult [nxxs, nyys, na, nb] (result (Forall (x SL..: xs), Forall (y SL..: ys)) (Forall a) (Forall b)))
                            (quick steps)

-- | Induction over two 'SList', simultaneously, taking three extra arguments
instance (KnownSymbol nxs, SymVal x, KnownSymbol nys, SymVal y, KnownSymbol na, SymVal a, KnownSymbol nb, SymVal b, KnownSymbol nc, SymVal c) => Inductive ((Forall nxs [x], Forall nys [y]) -> Forall na a -> Forall nb b -> Forall nc c -> SBool) where
  type IHType ((Forall nxs [x], Forall nys [y]) -> Forall na a -> Forall nb b -> Forall nc c -> SBool) = Forall na a -> Forall nb b -> Forall nc c -> SBool
  type IHArg  ((Forall nxs [x], Forall nys [y]) -> Forall na a -> Forall nb b -> Forall nc c -> SBool) = (SBV x, SList x, SBV y, SList y)

  inductionStrategy result steps = do
       (x, xs, nxxs) <- mkLVar (Proxy @nxs)
       (y, ys, nyys) <- mkLVar (Proxy @nys)
       (a, na)       <- mkVar  (Proxy @na)
       (b, nb)       <- mkVar  (Proxy @nb)
       (c, nc)       <- mkVar  (Proxy @nc)
       pure $ mkIndStrategy Nothing
                            (Just (result (Forall SL.nil, Forall SL.nil) (Forall a) (Forall b) (Forall c) .&& result (Forall SL.nil, Forall (y SL..: ys)) (Forall a) (Forall b) (Forall c) .&& result (Forall (x SL..: xs), Forall SL.nil) (Forall a) (Forall b) (Forall c)))
                            (steps (internalAxiom "IH" (\(Forall a' :: Forall na a) (Forall b' :: Forall nb b) (Forall c' :: Forall nc c) -> result (Forall xs, Forall ys) (Forall a') (Forall b') (Forall c'))) (x, xs, y, ys) a b c)
                            (indResult [nxxs, nyys, na, nb, nc] (result (Forall (x SL..: xs), Forall (y SL..: ys)) (Forall a) (Forall b) (Forall c)))
                            (quick steps)

-- | Induction over two 'SList', simultaneously, taking four extra arguments
instance (KnownSymbol nxs, SymVal x, KnownSymbol nys, SymVal y, KnownSymbol na, SymVal a, KnownSymbol nb, SymVal b, KnownSymbol nc, SymVal c, KnownSymbol nd, SymVal d) => Inductive ((Forall nxs [x], Forall nys [y]) -> Forall na a -> Forall nb b -> Forall nc c -> Forall nd d -> SBool) where
  type IHType ((Forall nxs [x], Forall nys [y]) -> Forall na a -> Forall nb b -> Forall nc c -> Forall nd d -> SBool) = Forall na a -> Forall nb b -> Forall nc c -> Forall nd d -> SBool
  type IHArg  ((Forall nxs [x], Forall nys [y]) -> Forall na a -> Forall nb b -> Forall nc c -> Forall nd d -> SBool) = (SBV x, SList x, SBV y, SList y)

  inductionStrategy result steps = do
       (x, xs, nxxs) <- mkLVar (Proxy @nxs)
       (y, ys, nyys) <- mkLVar (Proxy @nys)
       (a, na)       <- mkVar  (Proxy @na)
       (b, nb)       <- mkVar  (Proxy @nb)
       (c, nc)       <- mkVar  (Proxy @nc)
       (d, nd)       <- mkVar  (Proxy @nd)
       pure $ mkIndStrategy Nothing
                            (Just (result (Forall SL.nil, Forall SL.nil) (Forall a) (Forall b) (Forall c) (Forall d) .&& result (Forall SL.nil, Forall (y SL..: ys)) (Forall a) (Forall b) (Forall c) (Forall d) .&& result (Forall (x SL..: xs), Forall SL.nil) (Forall a) (Forall b) (Forall c) (Forall d)))
                            (steps (internalAxiom "IH" (\(Forall a' :: Forall na a) (Forall b' :: Forall nb b) (Forall c' :: Forall nc c) (Forall d' :: Forall nd d) -> result (Forall xs, Forall ys) (Forall a') (Forall b') (Forall c') (Forall d'))) (x, xs, y, ys) a b c d)
                            (indResult [nxxs, nyys, na, nb, nc, nd] (result (Forall (x SL..: xs), Forall (y SL..: ys)) (Forall a) (Forall b) (Forall c) (Forall d)))
                            (quick steps)

-- | Induction over two 'SList', simultaneously, taking five extra arguments
instance (KnownSymbol nxs, SymVal x, KnownSymbol nys, SymVal y, KnownSymbol na, SymVal a, KnownSymbol nb, SymVal b, KnownSymbol nc, SymVal c, KnownSymbol nd, SymVal d, KnownSymbol ne, SymVal e) => Inductive ((Forall nxs [x], Forall nys [y]) -> Forall na a -> Forall nb b -> Forall nc c -> Forall nd d -> Forall ne e -> SBool) where
  type IHType ((Forall nxs [x], Forall nys [y]) -> Forall na a -> Forall nb b -> Forall nc c -> Forall nd d -> Forall ne e -> SBool) = Forall na a -> Forall nb b -> Forall nc c -> Forall nd d -> Forall ne e -> SBool
  type IHArg  ((Forall nxs [x], Forall nys [y]) -> Forall na a -> Forall nb b -> Forall nc c -> Forall nd d -> Forall ne e -> SBool) = (SBV x, SList x, SBV y, SList y)

  inductionStrategy result steps = do
       (x, xs, nxxs) <- mkLVar (Proxy @nxs)
       (y, ys, nyys) <- mkLVar (Proxy @nys)
       (a, na)       <- mkVar  (Proxy @na)
       (b, nb)       <- mkVar  (Proxy @nb)
       (c, nc)       <- mkVar  (Proxy @nc)
       (d, nd)       <- mkVar  (Proxy @nd)
       (e, ne)       <- mkVar  (Proxy @ne)
       pure $ mkIndStrategy Nothing
                            (Just (result (Forall SL.nil, Forall SL.nil) (Forall a) (Forall b) (Forall c) (Forall d) (Forall e) .&& result (Forall SL.nil, Forall (y SL..: ys)) (Forall a) (Forall b) (Forall c) (Forall d) (Forall e) .&& result (Forall (x SL..: xs), Forall SL.nil) (Forall a) (Forall b) (Forall c) (Forall d) (Forall e)))
                            (steps (internalAxiom "IH" (\(Forall a' :: Forall na a) (Forall b' :: Forall nb b) (Forall c' :: Forall nc c) (Forall d' :: Forall nd d) (Forall e' :: Forall ne e) -> result (Forall xs, Forall ys) (Forall a') (Forall b') (Forall c') (Forall d') (Forall e'))) (x, xs, y, ys) a b c d e)
                            (indResult [nxxs, nyys, na, nb, nc, nd, ne] (result (Forall (x SL..: xs), Forall (y SL..: ys)) (Forall a) (Forall b) (Forall c) (Forall d) (Forall e)))
                            (quick steps)


-- | Generalized induction with one parameter
instance (KnownSymbol na, SymVal a) => SInductive (Forall na a -> SBool) where
  sInductionStrategy result measure steps = do
      (a, na) <- mkVar (Proxy @na)
      pure $ mkIndStrategy (Just (measure a .>= zero))
                           Nothing
                           (steps (internalAxiom "IH" (\(Forall a' :: Forall na a) -> measure a' .< measure a .=> result (Forall a'))) a)
                           (indResult [na] (result (Forall a)))
                           (quick steps)

-- | Generalized induction with two parameters
instance (KnownSymbol na, SymVal a, KnownSymbol nb, SymVal b) => SInductive (Forall na a -> Forall nb b -> SBool) where
  sInductionStrategy result measure steps = do
      (a, na) <- mkVar (Proxy @na)
      (b, nb) <- mkVar (Proxy @nb)
      pure $ mkIndStrategy (Just (measure a b .>= zero))
                           Nothing
                           (steps (internalAxiom "IH" (\(Forall a' :: Forall na a) (Forall b' :: Forall nb b) -> measure a' b' .< measure a b .=> result (Forall a') (Forall b'))) a b)
                           (indResult [na, nb] (result (Forall a) (Forall b)))
                           (quick steps)

-- | Generalized induction with three parameters
instance (KnownSymbol na, SymVal a, KnownSymbol nb, SymVal b, KnownSymbol nc, SymVal c) => SInductive (Forall na a -> Forall nb b -> Forall nc c -> SBool) where
  sInductionStrategy result measure steps = do
      (a, na) <- mkVar (Proxy @na)
      (b, nb) <- mkVar (Proxy @nb)
      (c, nc) <- mkVar (Proxy @nc)
      pure $ mkIndStrategy (Just (measure a b c .>= zero))
                           Nothing
                           (steps (internalAxiom "IH" (\(Forall a' :: Forall na a) (Forall b' :: Forall nb b) (Forall c' :: Forall nc c) -> measure a' b' c' .< measure a b c .=> result (Forall a') (Forall b') (Forall c'))) a b c)
                           (indResult [na, nb, nc] (result (Forall a) (Forall b) (Forall c)))
                           (quick steps)

-- | Generalized induction with four parameters
instance (KnownSymbol na, SymVal a, KnownSymbol nb, SymVal b, KnownSymbol nc, SymVal c, KnownSymbol nd, SymVal d) => SInductive (Forall na a -> Forall nb b -> Forall nc c -> Forall nd d -> SBool) where
  sInductionStrategy result measure steps = do
      (a, na) <- mkVar (Proxy @na)
      (b, nb) <- mkVar (Proxy @nb)
      (c, nc) <- mkVar (Proxy @nc)
      (d, nd) <- mkVar (Proxy @nd)
      pure $ mkIndStrategy (Just (measure a b c d .>= zero))
                           Nothing
                           (steps (internalAxiom "IH" (\(Forall a' :: Forall na a) (Forall b' :: Forall nb b) (Forall c' :: Forall nc c) (Forall d' :: Forall nd d) -> measure a' b' c' d' .< measure a b c d .=> result (Forall a') (Forall b') (Forall c') (Forall d'))) a b c d)
                           (indResult [na, nb, nc, nd] (result (Forall a) (Forall b) (Forall c) (Forall d)))
                           (quick steps)

-- | Generalized induction with five parameters
instance (KnownSymbol na, SymVal a, KnownSymbol nb, SymVal b, KnownSymbol nc, SymVal c, KnownSymbol nd, SymVal d, KnownSymbol ne, SymVal e) => SInductive (Forall na a -> Forall nb b -> Forall nc c -> Forall nd d -> Forall ne e -> SBool) where
  sInductionStrategy result measure steps = do
      (a, na) <- mkVar (Proxy @na)
      (b, nb) <- mkVar (Proxy @nb)
      (c, nc) <- mkVar (Proxy @nc)
      (d, nd) <- mkVar (Proxy @nd)
      (e, ne) <- mkVar (Proxy @ne)
      pure $ mkIndStrategy (Just (measure a b c d e .>= zero))
                           Nothing
                           (steps (internalAxiom "IH" (\(Forall a' :: Forall na a) (Forall b' :: Forall nb b) (Forall c' :: Forall nc c) (Forall d' :: Forall nd d) (Forall e' :: Forall ne e) -> measure a' b' c' d' e' .< measure a b c d e .=> result (Forall a') (Forall b') (Forall c') (Forall d') (Forall e'))) a b c d e)
                           (indResult [na, nb, nc, nd, ne] (result (Forall a) (Forall b) (Forall c) (Forall d) (Forall e)))
                           (quick steps)

-- | Instantiation for a universally quantified variable
newtype Inst (nm :: Symbol) a = Inst (SBV a)

instance KnownSymbol nm => Show (Inst nm a) where
   show (Inst a) = symbolVal (Proxy @nm) ++ " |-> " ++ show a

-- | Instantiating a proof at a particular choice of arguments
class Instantiatable a where
  type IArgs a :: Type

  -- | Apply a universal proof to some arguments, creating a boolean expression guaranteed to be true
  at :: Proof a -> IArgs a -> Proof Bool

-- | Instantiation a single parameter proof
instance (KnownSymbol na, Typeable a) => Instantiatable (Forall na a -> SBool) where
  type IArgs (Forall na a -> SBool) = Inst na a

  at = instantiate $ \f (Inst a) -> f (Forall a :: Forall na a)

-- | Two parameters
instance ( KnownSymbol na, HasKind a, Typeable a
         , KnownSymbol nb, HasKind b, Typeable b
         ) => Instantiatable (Forall na a -> Forall nb b -> SBool) where
  type IArgs (Forall na a -> Forall nb b -> SBool) = (Inst na a, Inst nb b)

  at  = instantiate $ \f (Inst a, Inst b) -> f (Forall a :: Forall na a) (Forall b :: Forall nb b)

-- | Three parameters
instance ( KnownSymbol na, HasKind a, Typeable a
         , KnownSymbol nb, HasKind b, Typeable b
         , KnownSymbol nc, HasKind c, Typeable c
         ) => Instantiatable (Forall na a -> Forall nb b -> Forall nc c -> SBool) where
  type IArgs (Forall na a -> Forall nb b -> Forall nc c -> SBool) = (Inst na a, Inst nb b, Inst nc c)

  at  = instantiate $ \f (Inst a, Inst b, Inst c) -> f (Forall a :: Forall na a) (Forall b :: Forall nb b) (Forall c :: Forall nc c)

-- | Four parameters
instance ( KnownSymbol na, HasKind a, Typeable a
         , KnownSymbol nb, HasKind b, Typeable b
         , KnownSymbol nc, HasKind c, Typeable c
         , KnownSymbol nd, HasKind d, Typeable d
         ) => Instantiatable (Forall na a -> Forall nb b -> Forall nc c -> Forall nd d -> SBool) where
  type IArgs (Forall na a -> Forall nb b -> Forall nc c -> Forall nd d -> SBool) = (Inst na a, Inst nb b, Inst nc c, Inst nd d)

  at  = instantiate $ \f (Inst a, Inst b, Inst c, Inst d) -> f (Forall a :: Forall na a) (Forall b :: Forall nb b) (Forall c :: Forall nc c) (Forall d :: Forall nd d)

-- | Five parameters
instance ( KnownSymbol na, HasKind a, Typeable a
         , KnownSymbol nb, HasKind b, Typeable b
         , KnownSymbol nc, HasKind c, Typeable c
         , KnownSymbol nd, HasKind d, Typeable d
         , KnownSymbol ne, HasKind e, Typeable e
         ) => Instantiatable (Forall na a -> Forall nb b -> Forall nc c -> Forall nd d -> Forall ne e -> SBool) where
  type IArgs (Forall na a -> Forall nb b -> Forall nc c -> Forall nd d -> Forall ne e -> SBool) = (Inst na a, Inst nb b, Inst nc c, Inst nd d, Inst ne e)

  at  = instantiate $ \f (Inst a, Inst b, Inst c, Inst d, Inst e) -> f (Forall a :: Forall na a) (Forall b :: Forall nb b) (Forall c :: Forall nc c) (Forall d :: Forall nd d) (Forall e :: Forall ne e)

-- | Instantiate a proof over an arg. This uses dynamic typing, kind of hacky, but works sufficiently well.
instantiate :: (Typeable f, Show arg) => (f -> arg -> SBool) -> Proof a -> arg -> Proof Bool
instantiate ap (Proof p@ProofObj{getProp, proofName}) a = case fromDynamic getProp of
                                                            Nothing -> cantInstantiate
                                                            Just f  -> let result = f `ap` a
                                                                           nm     = proofName ++ " @ " ++ paren sha
                                                                       in Proof $ p { getObjProof = label nm result
                                                                                    , getProp     = toDyn result
                                                                                    , proofName   = nm
                                                                                    }
 where sha = show a
       cantInstantiate = error $ unlines [ "***"
                                         , "Data.SBV.TP: Impossible happened: Cannot instantiate proof:"
                                         , ""
                                         , "   Name: " ++ proofName
                                         , "   Type: " ++ trim (show getProp)
                                         , "   At  : " ++ sha
                                         , ""
                                         , "Please report this as a bug!"
                                         ]

       -- dynamic puts funky <</>> at the beginning and end; trim it:
       trim  ('<':'<':s) = reverse (trimE (reverse s))
       trim  s           = s
       trimE ('>':'>':s) = s
       trimE s           = s

       -- Add parens if necessary
       paren s | "(" `isPrefixOf` s && ")" `isSuffixOf` s = s
               | not (any isSpace s)                      = s
               | True                                     = '(' : s ++ ")"

-- | Helpers for a step
data Helper = HelperProof  ProofObj  -- A previously proven theorem
            | HelperAssum  SBool     -- A hypothesis
            | HelperQC     Int       -- Quickcheck with this many tests
            | HelperString String    -- Just a text, only used for diagnostics

-- | Get all helpers used in a proof
getAllHelpers :: TPProof -> [Helper]
getAllHelpers (ProofStep   _           hs               p)  = hs ++ getAllHelpers p
getAllHelpers (ProofBranch (_ :: Bool) (_ :: [String]) ps) = concatMap (getAllHelpers . snd) ps
getAllHelpers (ProofEnd    _           hs                ) = hs

-- | Get proofs from helpers
getHelperProofs :: Helper -> [ProofObj]
getHelperProofs (HelperProof p) = [p]
getHelperProofs HelperAssum {}  = []
getHelperProofs HelperQC    {}  = [quickCheckProof]
getHelperProofs HelperString{}  = []

-- | Get proofs from helpers
getHelperAssumes :: Helper -> [SBool]
getHelperAssumes HelperProof  {} = []
getHelperAssumes (HelperAssum b) = [b]
getHelperAssumes HelperQC     {} = []
getHelperAssumes HelperString {} = []

-- | Get hint strings from helpers. If there's an explicit comment given, just pass that. If not, collect all the names
getHelperText :: [Helper] -> [String]
getHelperText hs = case [s | HelperString s <- hs] of
                     [] -> concatMap collect hs
                     ss -> ss
  where collect :: Helper -> [String]
        collect (HelperProof  p) = [proofName p | isUserAxiom p]  -- Don't put out internals (inductive hypotheses)
        collect HelperAssum  {}  = []
        collect (HelperQC     i) = ["passed " ++ show i ++ " tests"]
        collect (HelperString s) = [s]

-- | A proof is a sequence of steps, supporting branching
data TPProofGen a bh b = ProofStep   a    [Helper] (TPProofGen a bh b)          -- ^ A single step
                       | ProofBranch Bool bh       [(SBool, TPProofGen a bh b)] -- ^ A branching step. Bool indicates if completeness check is needed
                       | ProofEnd    b    [Helper]                              -- ^ End of proof

-- | A proof, as written by the user. No produced result, but helpers on branches
type TPProofRaw a = TPProofGen a [Helper] ()

-- | A proof, as processed by TP. Producing a boolean result and each step is a boolean. Helpers on branches dispersed down, only strings are left for printing
type TPProof = TPProofGen SBool [String] SBool

-- | Collect dependencies for a TPProof
getDependencies :: TPProof -> [ProofObj]
getDependencies = collect
  where collect (ProofStep   _ hs next) = concatMap getHelperProofs hs ++ collect next
        collect (ProofBranch _ _  bs)   = concatMap (collect . snd) bs
        collect (ProofEnd    _    hs)   = concatMap getHelperProofs hs

-- | Class capturing giving a proof-step helper
type family Hinted a where
  Hinted (TPProofRaw a) = TPProofRaw a
  Hinted a              = TPProofRaw a

-- | Attaching a hint
(??) :: HintsTo a b => a -> b -> Hinted a
(??) = addHint
infixl 2 ??

-- | Alternative unicode for `??`.
(∵) :: HintsTo a b => a -> b -> Hinted a
(∵) = (??)
infixl 2 ∵

-- | Class capturing hints
class HintsTo a b where
  addHint :: a -> b -> Hinted a

-- | Giving just one proof as a helper.
instance Hinted a ~ TPProofRaw a => HintsTo a (Proof b) where
  a `addHint` p = ProofStep a [HelperProof (proofOf p)] qed

-- | Giving a bunch of proofs at the same type as a helper.
instance Hinted a ~ TPProofRaw a => HintsTo a [Proof b] where
  a `addHint` ps = ProofStep a (map (HelperProof . proofOf) ps) qed

-- | Giving just one proof-obj as a helper.
instance Hinted a ~ TPProofRaw a => HintsTo a ProofObj where
  a `addHint` p = ProofStep a [HelperProof p] qed

-- | Giving a bunch of proof-objs at the same type as a helper.
instance Hinted a ~ TPProofRaw a => HintsTo a [ProofObj] where
  a `addHint` ps = ProofStep a (map HelperProof ps) qed

-- | Giving just one boolean as a helper.
instance Hinted a ~ TPProofRaw a => HintsTo a SBool where
  a `addHint` p = ProofStep a [HelperAssum p] qed

-- | Giving a list of booleans as a helper.
instance Hinted a ~ TPProofRaw a => HintsTo a [SBool] where
  a `addHint` ps = ProofStep a (map HelperAssum ps) qed

-- | Giving just one helper
instance Hinted a ~ TPProofRaw a => HintsTo a Helper where
  a `addHint` h = ProofStep a [h] qed

-- | Giving a list of helper
instance Hinted a ~ TPProofRaw a => HintsTo a [Helper] where
  a `addHint` hs = ProofStep a hs qed

-- | Giving user a hint as a string. This doesn't actually do anything for the solver, it just helps with readability
instance Hinted a ~ TPProofRaw a => HintsTo a String where
  a `addHint` s = ProofStep a [HelperString s] qed

-- | Giving a bunch of strings
instance Hinted a ~ TPProofRaw a => HintsTo a [String] where
  a `addHint` ss = ProofStep a (map HelperString ss) qed

-- | Giving just one proof as a helper, starting from a proof
instance {-# OVERLAPPING #-} Hinted (TPProofRaw a) ~ TPProofRaw a => HintsTo (TPProofRaw a) (Proof b) where
  ProofStep   a hs ps `addHint` h = ProofStep   a (hs ++ [HelperProof (proofOf h)]) ps
  ProofBranch b hs bs `addHint` h = ProofBranch b (hs ++ [HelperProof (proofOf h)]) bs
  ProofEnd    b hs    `addHint` h = ProofEnd    b (hs ++ [HelperProof (proofOf h)])

-- | Giving just one proofobj as a helper, starting from a proof
instance {-# OVERLAPPING #-} Hinted (TPProofRaw a) ~ TPProofRaw a => HintsTo (TPProofRaw a) ProofObj where
  ProofStep   a hs ps `addHint` h = ProofStep   a (hs ++ [HelperProof h]) ps
  ProofBranch b hs bs `addHint` h = ProofBranch b (hs ++ [HelperProof h]) bs
  ProofEnd    b hs    `addHint` h = ProofEnd    b (hs ++ [HelperProof h])

-- | Giving a bunch of proofs at the same type as a helper, starting from a proof
instance {-# OVERLAPPING #-} Hinted (TPProofRaw a) ~ TPProofRaw a => HintsTo (TPProofRaw a) [Proof b] where
  ProofStep   a hs ps `addHint` hs' = ProofStep   a (hs ++ map (HelperProof . proofOf) hs') ps
  ProofBranch b hs bs `addHint` hs' = ProofBranch b (hs ++ map (HelperProof . proofOf) hs') bs
  ProofEnd    b hs    `addHint` hs' = ProofEnd    b (hs ++ map (HelperProof . proofOf) hs')

-- | Giving just one boolean as a helper.
instance {-# OVERLAPPING #-} Hinted (TPProofRaw a) ~ TPProofRaw a => HintsTo (TPProofRaw a) SBool where
  ProofStep   a hs ps `addHint` h = ProofStep   a (hs ++ [HelperAssum h]) ps
  ProofBranch b hs bs `addHint` h = ProofBranch b (hs ++ [HelperAssum h]) bs
  ProofEnd    b hs    `addHint` h = ProofEnd    b (hs ++ [HelperAssum h])

-- | Giving a bunch of booleans as a helper.
instance {-# OVERLAPPING #-} Hinted (TPProofRaw a) ~ TPProofRaw a => HintsTo (TPProofRaw a) [SBool] where
  ProofStep   a hs ps `addHint` hs' = ProofStep   a (hs ++ map HelperAssum hs') ps
  ProofBranch b hs bs `addHint` hs' = ProofBranch b (hs ++ map HelperAssum hs') bs
  ProofEnd    b hs    `addHint` hs' = ProofEnd    b (hs ++ map HelperAssum hs')

-- | Giving just one helper
instance {-# OVERLAPPING #-} Hinted (TPProofRaw a) ~ TPProofRaw a => HintsTo (TPProofRaw a) Helper where
  ProofStep   a hs ps `addHint` h = ProofStep   a (hs ++ [h]) ps
  ProofBranch b hs bs `addHint` h = ProofBranch b (hs ++ [h]) bs
  ProofEnd    b hs    `addHint` h = ProofEnd    b (hs ++ [h])

-- | Giving a set of helpers
instance {-# OVERLAPPING #-} Hinted (TPProofRaw a) ~ TPProofRaw a => HintsTo (TPProofRaw a) [Helper] where
  ProofStep   a hs ps `addHint` hs' = ProofStep   a (hs ++ hs') ps
  ProofBranch b hs bs `addHint` hs' = ProofBranch b (hs ++ hs') bs
  ProofEnd    b hs    `addHint` hs' = ProofEnd    b (hs ++ hs')

-- | Giving user a hint as a string. This doesn't actually do anything for the solver, it just helps with readability
instance {-# OVERLAPPING #-} Hinted (TPProofRaw a) ~ TPProofRaw a => HintsTo (TPProofRaw a) String where
  a `addHint` s = a `addHint` HelperString s

-- | Giving a bunch of strings as hints. This doesn't actually do anything for the solver, it just helps with readability
instance {-# OVERLAPPING #-} Hinted (TPProofRaw a) ~ TPProofRaw a => HintsTo (TPProofRaw a) [String] where
  a `addHint` ss = a `addHint` map HelperString ss

-- | Giving a set of proof objects as helpers. This is helpful since we occasionally put a bunch of proofs together.
instance {-# OVERLAPPING #-} Hinted (TPProofRaw a) ~ TPProofRaw a => HintsTo (TPProofRaw a) [ProofObj] where
  ProofStep   a hs ps `addHint` hs' = ProofStep   a (hs ++ map HelperProof hs') ps
  ProofBranch b hs bs `addHint` hs' = ProofBranch b (hs ++ map HelperProof hs') bs
  ProofEnd    b hs    `addHint` hs' = ProofEnd    b (hs ++ map HelperProof hs')

-- | Capture what a given step can chain-to. This is a closed-type family, i.e.,
-- we don't allow users to change this and write other chainable things. Probably it is not really necessary,
-- but we'll cross that bridge if someone actually asks for it.
type family ChainsTo a where
  ChainsTo (TPProofRaw a) = TPProofRaw a
  ChainsTo a              = TPProofRaw a

-- | Chain steps in a calculational proof.
(=:) :: ChainStep a (ChainsTo a) =>  a -> ChainsTo a -> ChainsTo a
(=:) = chain
infixr 1 =:

-- | Unicode alternative for `=:`.
(≡) :: ChainStep a (ChainsTo a) =>  a -> ChainsTo a -> ChainsTo a
(≡) = (=:)
infixr 1 ≡

-- | Chaining two steps together
class ChainStep a b where
  chain :: a -> b -> b

-- | Chaining from a value without any annotation
instance ChainStep a (TPProofRaw a) where
  chain x y = ProofStep x [] y

-- | Chaining from another proof step
instance ChainStep (TPProofRaw a) (TPProofRaw a) where
  chain (ProofStep   a  hs  p)  y = ProofStep   a hs (chain p y)
  chain (ProofBranch c  hs  ps) y = ProofBranch c hs [(branchCond, chain p y) | (branchCond, p) <- ps]
  chain (ProofEnd    () hs)     y = case y of
                                      ProofStep   a  hs' p  -> ProofStep   a  (hs' ++ hs) p
                                      ProofBranch b  hs' bs -> ProofBranch b  (hs' ++ hs) bs
                                      ProofEnd    () hs'    -> ProofEnd    () (hs' ++ hs)

-- | Mark the end of a calculational proof.
qed :: TPProofRaw a
qed = ProofEnd () []

-- | Mark a trivial proof. This is essentially the same as 'qed', but reads better in proof scripts.
class Trivial a where
  -- | Mark a proof as trivial, i.e., the solver should be able to deduce it without any help.
  trivial :: a

-- | Trivial proofs with no arguments
instance Trivial (TPProofRaw a) where
  trivial = qed

-- | Trivial proofs with many arguments arguments
instance Trivial a => Trivial (b -> a) where
  trivial = const trivial

-- | Mark a contradictory proof path. This is essentially the same as @sFalse := qed@, but reads better in proof scripts.
class Contradiction a where
  -- | Mark a proof as contradiction, i.e., the solver should be able to conclude it by reasoning that the current path is infeasible
  contradiction :: a

-- | Contradiction proofs with no arguments
instance Contradiction (TPProofRaw SBool) where
  contradiction = sFalse =: qed

-- | Contradiction proofs with many arguments
instance Contradiction a => Contradiction (b -> a) where
  contradiction = const contradiction


-- | Start a calculational proof, with the given hypothesis. Use @[]@ as the
-- first argument if the calculation holds unconditionally. The first argument is
-- typically used to introduce hypotheses in proofs of implications such as @A .=> B .=> C@, where
-- we would put @[A, B]@ as the starting assumption. You can name these and later use in the derivation steps.
(|-) :: [SBool] -> TPProofRaw a -> (SBool, TPProofRaw a)
bs |- p = (sAnd bs, p)
infixl 0 |-

-- | Alternative unicode for `|-`.
(⊢) :: [SBool] -> TPProofRaw a -> (SBool, TPProofRaw a)
(⊢) = (|-)
infixl 0 ⊢

-- | The boolean case-split
cases :: [(SBool, TPProofRaw a)] -> TPProofRaw a
cases = ProofBranch True []

-- | Case splitting over a list; empty and full cases
split :: SymVal a => SList a -> TPProofRaw r -> (SBV a -> SList a -> TPProofRaw r) -> TPProofRaw r
split xs empty cons = ProofBranch False [] [(cnil, empty), (ccons, cons h t)]
   where cnil   = SL.null   xs
         (h, t) = SL.uncons xs
         ccons  = sNot cnil .&& xs .== h SL..: t

-- | Case splitting over two lists; empty and full cases for each
split2 :: (SymVal a, SymVal b)
       => (SList a, SList b)
       -> TPProofRaw r
       -> ((SBV b, SList b)                     -> TPProofRaw r) -- empty first
       -> ((SBV a, SList a)                     -> TPProofRaw r) -- empty second
       -> ((SBV a, SList a) -> (SBV b, SList b) -> TPProofRaw r) -- neither empty
       -> TPProofRaw r
split2 (xs, ys) ee ec ce cc = ProofBranch False
                                          []
                                          [ (xnil  .&& ynil,  ee)
                                          , (xnil  .&& ycons, ec (hy, ty))
                                          , (xcons .&& ynil,  ce (hx, tx))
                                          , (xcons .&& ycons, cc (hx, tx) (hy, ty))
                                          ]
  where xnil     = SL.null   xs
        (hx, tx) = SL.uncons xs
        xcons    = sNot xnil .&& xs .== hx SL..: tx

        ynil     = SL.null   ys
        (hy, ty) = SL.uncons ys
        ycons    = sNot ynil .&& ys .== hy SL..: ty

-- | A quick-check step
qc :: Int -> Helper
qc = HelperQC

-- | Specifying a case-split, helps with the boolean case.
(==>) :: SBool -> TPProofRaw a -> (SBool, TPProofRaw a)
(==>) = (,)
infix 0 ==>

-- | Alternative unicode for `==>`
(⟹) :: SBool -> TPProofRaw a -> (SBool, TPProofRaw a)
(⟹) = (==>)
infix 0 ⟹

{- HLint ignore module "Eta reduce" -}
