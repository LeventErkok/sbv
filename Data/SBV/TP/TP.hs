-----------------------------------------------------------------------------
-- |
-- Module    : Data.SBV.TP.TP
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
-----------------------------------------------------------------------------

{-# LANGUAGE DataKinds              #-}
{-# LANGUAGE FlexibleContexts       #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE NamedFieldPuns         #-}
{-# LANGUAGE ScopedTypeVariables    #-}
{-# LANGUAGE TupleSections          #-}
{-# LANGUAGE TypeApplications       #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE TypeOperators          #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module Data.SBV.TP.TP (
         Proposition, Proof, proofOf, assumptionFromProof, Instantiatable(..), Inst(..)
       , rootOfTrust, RootOfTrust(..), ProofTree(..), showProofTree, showProofTreeHTML
       ,   axiom
       ,            lemma,          lemmaWith
       ,   inductiveLemma, inductiveLemmaWith
       ,             calc,           calcWith
       ,           induct,         inductWith
       ,          sInduct,        sInductWith
       , sorry
       , TP, runTP, runTPWith, tpQuiet, tpRibbon, tpStats, tpAsms, tpCache
       , (|-), (|->), (⊢), (=:), (≡), (??), (∵), split, split2, cases, (==>), (⟹), qed, trivial, contradiction
       , qc, qcWith
       , disp
       , recall
       ) where

import Data.SBV
import Data.SBV.Core.Model (qSaturateSavingObservables)
import Data.SBV.Core.Data  (SBV(..), SVal(..))
import qualified Data.SBV.Core.Symbolic as S (sObserve)

import Data.SBV.Core.Operations (svEqual)
import Data.SBV.Control hiding (getProof, (|->))

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
import Test.QuickCheck (quickCheckWithResult)

-- | Captures the steps for a calculationa proof
data CalcStrategy = CalcStrategy { calcIntros     :: SBool
                                 , calcProofTree  :: TPProof
                                 , calcQCInstance :: [Int] -> Symbolic SBool
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
        getH (HelperDisp _ v) = [SBV (v `svEqual` v)]

-- | Things that are inside calc-strategy that we have to saturate
getCalcStrategySaturatables :: CalcStrategy -> [SBool]
getCalcStrategySaturatables (CalcStrategy calcIntros calcProofTree _calcQCInstance) = calcIntros : proofTreeSaturatables calcProofTree

-- | Propagate the settings for ribbon/timing from top to current. Because in any subsequent configuration
-- in a lemmaWith, inductWith etc., we just want to change the solver, not the actual settings for TP.
tpMergeCfg :: SMTConfig -> SMTConfig -> SMTConfig
tpMergeCfg cur top = cur{tpOptions = tpOptions top}

-- | Use an injective type family to allow for curried use of calc and strong induction steps.
type family StepArgs a t = result | result -> t where
  StepArgs                                                                             SBool  t =                                               (SBool, TPProofRaw (SBV t))
  StepArgs (Forall na a                                                             -> SBool) t = (SBV a                                     -> (SBool, TPProofRaw (SBV t)))
  StepArgs (Forall na a -> Forall nb b                                              -> SBool) t = (SBV a -> SBV b                            -> (SBool, TPProofRaw (SBV t)))
  StepArgs (Forall na a -> Forall nb b -> Forall nc c                               -> SBool) t = (SBV a -> SBV b -> SBV c                   -> (SBool, TPProofRaw (SBV t)))
  StepArgs (Forall na a -> Forall nb b -> Forall nc c -> Forall nd d                -> SBool) t = (SBV a -> SBV b -> SBV c -> SBV d          -> (SBool, TPProofRaw (SBV t)))
  StepArgs (Forall na a -> Forall nb b -> Forall nc c -> Forall nd d -> Forall ne e -> SBool) t = (SBV a -> SBV b -> SBV c -> SBV d -> SBV e -> (SBool, TPProofRaw (SBV t)))

-- | Use an injective type family to allow for curried use of measures in strong induction instances
type family MeasureArgs a t = result | result -> t where
  MeasureArgs                                                                             SBool  t = (                                             SBV t)
  MeasureArgs (Forall na a                                                             -> SBool) t = (SBV a                                     -> SBV t)
  MeasureArgs (Forall na a -> Forall nb b                                              -> SBool) t = (SBV a -> SBV b                            -> SBV t)
  MeasureArgs (Forall na a -> Forall nb b -> Forall nc c                               -> SBool) t = (SBV a -> SBV b -> SBV c                   -> SBV t)
  MeasureArgs (Forall na a -> Forall nb b -> Forall nc c -> Forall nd d                -> SBool) t = (SBV a -> SBV b -> SBV c -> SBV d          -> SBV t)
  MeasureArgs (Forall na a -> Forall nb b -> Forall nc c -> Forall nd d -> Forall ne e -> SBool) t = (SBV a -> SBV b -> SBV c -> SBV d -> SBV e -> SBV t)

-- | Use an injective type family to allow for curried use of regular induction steps. The first argument is the inductive arg that comes separately,
-- and hence is not used in the right-hand side of the equation.
type family IStepArgs a t = result | result -> t where
  IStepArgs ( Forall nx x                                                                                          -> SBool) t =                                               (SBool, TPProofRaw (SBV t))
  IStepArgs ( Forall nx x               -> Forall na a                                                             -> SBool) t = (SBV a ->                                     (SBool, TPProofRaw (SBV t)))
  IStepArgs ( Forall nx x               -> Forall na a -> Forall nb b                                              -> SBool) t = (SBV a -> SBV b                            -> (SBool, TPProofRaw (SBV t)))
  IStepArgs ( Forall nx x               -> Forall na a -> Forall nb b -> Forall nc c                               -> SBool) t = (SBV a -> SBV b -> SBV c                   -> (SBool, TPProofRaw (SBV t)))
  IStepArgs ( Forall nx x               -> Forall na a -> Forall nb b -> Forall nc c -> Forall nd d                -> SBool) t = (SBV a -> SBV b -> SBV c -> SBV d          -> (SBool, TPProofRaw (SBV t)))
  IStepArgs ( Forall nx x               -> Forall na a -> Forall nb b -> Forall nc c -> Forall nd d -> Forall ne e -> SBool) t = (SBV a -> SBV b -> SBV c -> SBV d -> SBV e -> (SBool, TPProofRaw (SBV t)))
  IStepArgs ((Forall nx x, Forall ny y)                                                                            -> SBool) t =                                               (SBool, TPProofRaw (SBV t))
  IStepArgs ((Forall nx x, Forall ny y) -> Forall na a                                                             -> SBool) t = (SBV a ->                                     (SBool, TPProofRaw (SBV t)))
  IStepArgs ((Forall nx x, Forall ny y) -> Forall na a -> Forall nb b                                              -> SBool) t = (SBV a -> SBV b                            -> (SBool, TPProofRaw (SBV t)))
  IStepArgs ((Forall nx x, Forall ny y) -> Forall na a -> Forall nb b -> Forall nc c                               -> SBool) t = (SBV a -> SBV b -> SBV c                   -> (SBool, TPProofRaw (SBV t)))
  IStepArgs ((Forall nx x, Forall ny y) -> Forall na a -> Forall nb b -> Forall nc c -> Forall nd d                -> SBool) t = (SBV a -> SBV b -> SBV c -> SBV d          -> (SBool, TPProofRaw (SBV t)))
  IStepArgs ((Forall nx x, Forall ny y) -> Forall na a -> Forall nb b -> Forall nc c -> Forall nd d -> Forall ne e -> SBool) t = (SBV a -> SBV b -> SBV c -> SBV d -> SBV e -> (SBool, TPProofRaw (SBV t)))

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
  calc :: (Proposition a, SymVal t, EqSymbolic (SBV t)) => String -> a -> StepArgs a t -> TP (Proof a)

  -- | Prove a property via a series of equality steps, using the given solver.
  calcWith :: (Proposition a, SymVal t, EqSymbolic (SBV t)) => SMTConfig -> String -> a -> StepArgs a t -> TP (Proof a)

  -- | Internal, shouldn't be needed outside the library
  {-# MINIMAL calcSteps #-}
  calcSteps :: (SymVal t, EqSymbolic (SBV t)) => a -> StepArgs a t -> Symbolic (SBool, CalcStrategy)

  calc         nm p steps = getTPConfig >>= \cfg  -> calcWith          cfg                   nm p steps
  calcWith cfg nm p steps = getTPConfig >>= \cfg' -> calcGeneric False (tpMergeCfg cfg cfg') nm p steps

  calcGeneric :: (SymVal t, EqSymbolic (SBV t), Proposition a) => Bool -> SMTConfig -> String -> a -> StepArgs a t -> TP (Proof a)
  calcGeneric tagTheorem cfg nm result steps = withProofCache nm $ do
      tpSt <- getTPState
      u    <- tpGetNextUnique

      (_, CalcStrategy {calcQCInstance}) <- liftIO $ runSMTWith cfg (calcSteps result steps)

      liftIO $ runSMTWith cfg $ do

         qSaturateSavingObservables result -- make sure we saturate the result, i.e., get all it's UI's, types etc. pop out

         message cfg $ (if tagTheorem then "Theorem" else "Lemma") ++ ": " ++ nm ++ "\n"

         (calcGoal, strategy@CalcStrategy {calcIntros, calcProofTree}) <- calcSteps result steps

         -- Collect all subterms and saturate them
         mapM_ qSaturateSavingObservables $ getCalcStrategySaturatables strategy

         query $ proveProofTree cfg tpSt nm (result, calcGoal) calcIntros calcProofTree u calcQCInstance

-- | In the proof tree, what's the next node label?
nextProofStep :: [Int] -> [Int]
nextProofStep bs = case reverse bs of
                     i : rs -> reverse $ i + 1 : rs
                     []     -> [1]

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
--
-- NB. This function needs to be in "sync" with qcRun below for obvious reasons. So, any changes there
-- make it here too!
proveProofTree :: Proposition a
               => SMTConfig
               -> TPState
               -> String                    -- ^ the name of the top result
               -> (a, SBool)                -- ^ goal: as a proposition and as a boolean
               -> SBool                     -- ^ hypotheses
               -> TPProof                   -- ^ proof tree
               -> TPUnique                  -- ^ unique id
               -> ([Int] -> Symbolic SBool) -- ^ quick-checker
               -> Query (Proof a)
proveProofTree cfg tpSt nm (result, resultBool) initialHypotheses calcProofTree uniq quickCheckInstance = do
    results <- walk initialHypotheses 1 ([1], calcProofTree)

    queryDebug [nm ++ ": Proof end: proving the result:"]

    mbStartTime <- getTimeStampIf printStats
    smtProofStep cfg tpSt "Result" 1
                 (TPProofStep False nm [] [""])
                 (Just (initialHypotheses .=> sAnd results))
                 resultBool [] $ \d ->
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

  where SMTConfig{tpOptions = TPOptions{printStats, printAsms}} = cfg

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
                                                         []
                                                         (\d -> finishTP cfg "Q.E.D." d [])
          pure results

        -- Do a proof step
        walk intros level (bn, ProofStep cur hs p) = do

             let finish et helpers d = finishTP cfg ("Q.E.D." ++ concludeModulo helpers) d et
                 stepName            = mkStepName level bn p
                 disps               = [(n, v) | HelperDisp n v <- hs]

                 -- First prove the assumptions, if there are any. We stay quiet, unless timing is asked for
                 (quietCfg, finalizer)
                   | printStats || printAsms = (cfg,                                             finish [] [])
                   | True                    = (cfg{tpOptions = (tpOptions cfg) {quiet = True}}, const (pure ()))

                 as = concatMap getHelperAssumes hs
                 ss = getHelperText hs

             case as of
               [] -> pure ()
               _  -> smtProofStep quietCfg tpSt "Asms" level
                                           (TPProofStep True nm [] stepName)
                                           (Just intros)
                                           (sAnd as)
                                           disps
                                           finalizer

             -- Are we asked to do quick-check?
             case [qcArg | HelperQC qcArg <- hs] of
               [] -> do -- No quickcheck. Just prove the step
                        let by = concatMap getHelperProofs hs

                        smtProofStep cfg tpSt "Step" level
                                         (TPProofStep False nm ss stepName)
                                         (Just (sAnd (intros : as ++ map getObjProof by)))
                                         cur
                                         disps
                                         (finish [] by)

               xs -> do let qcArg = last xs -- take the last one if multiple exists. Why not?

                            hs' = concatMap xform hs ++ [HelperString ("qc: Running " ++ show (QC.maxSuccess qcArg) ++ " tests")]
                            xform HelperProof{}    = []
                            xform HelperAssum{}    = []
                            xform h@HelperQC{}     = [h]
                            xform h@HelperString{} = [h]
                            xform HelperDisp{}     = []

                        liftIO $ do

                           tab <- startTP cfg (verbose cfg) "Step" level (TPProofStep False nm (getHelperText hs') stepName)

                           (mbT, r) <- timeIf printStats $ quickCheckWithResult qcArg{QC.chatty = verbose cfg} $ quickCheckInstance bn

                           case mbT of
                             Nothing -> pure ()
                             Just t  -> updStats tpSt (\s -> s{qcElapsed = qcElapsed s + t})

                           let err = case r of
                                   QC.Success {}                -> Nothing
                                   QC.Failure {QC.output = out} -> Just out
                                   QC.GaveUp  {}                -> Just $ unlines [ "*** QuickCheck reported \"GaveUp\""
                                                                                  , "***"
                                                                                  , "*** This can happen if you have assumptions in the environment"
                                                                                  , "*** that makes it hard for quick-check to generate valid test values."
                                                                                  , "***"
                                                                                  , "*** See if you can reduce assumptions. If not, please get in touch,"
                                                                                  , "*** to see if we can handle the problem via custom Arbitrary instances."
                                                                                  ]
                                   QC.NoExpectedFailure {}      -> Just "Expected failure but test passed." -- can't happen

                           case err of
                             Just e  -> do putStrLn $ "\n*** QuickCheck failed for " ++ intercalate "." (nm : stepName)
                                           putStrLn e
                                           error "Failed"

                             Nothing -> let extra = [' ' | printStats]  -- aligns better when printing stats
                                        in finishTP cfg ("QC OK" ++ extra) (tab, mbT) []

             -- Move to next
             walk intros level (nextProofStep bn, p)

-- | Helper data-type for calc-step below
data CalcContext a = CalcStart     [Helper] -- Haven't started yet
                   | CalcStep  a a [Helper] -- Intermediate step: first value, prev value


-- | Turn a raw (i.e., as written by the user) proof tree to a tree where the successive equalities are made explicit.
mkProofTree :: SymVal a => (SBV a -> SBV a -> c, SBV a -> SBV a -> SBool) -> TPProofRaw (SBV a) -> TPProofGen c [String] SBool
mkProofTree (symTraceEq, symEq) = go (CalcStart [])
  where -- End of the proof; tie the begin and end
        go step (ProofEnd () hs) = case step of
                                     -- It's tempting to error out if we're at the start and already reached the end
                                     -- This means we're given a sequence of no-steps. While this is useless in the
                                     -- general case, it's quite valid in a case-split; where one of the case-splits
                                     -- might be easy enough for the solver to deduce so the user simply says "just derive it for me."
                                     CalcStart hs'           -> ProofEnd sTrue (hs' ++ hs) -- Nothing proven!
                                     CalcStep  begin end hs' -> ProofEnd (begin `symEq` end) (hs' ++ hs)

        -- Branch: Just push it down. We use the hints from previous step, and pass the current ones down.
        go step (ProofBranch c hs ps) = ProofBranch c (getHelperText hs) [(bc, go step' p) | (bc, p) <- ps]
           where step' = case step of
                           CalcStart hs'     -> CalcStart (hs' ++ hs)
                           CalcStep  a b hs' -> CalcStep a b (hs' ++ hs)

        -- Step:
        go (CalcStart hs)           (ProofStep cur hs' p) = go (CalcStep cur cur (hs' ++ hs)) p
        go (CalcStep first prev hs) (ProofStep cur hs' p) = ProofStep (prev `symTraceEq` cur) hs (go (CalcStep first cur hs') p)

-- | Turn a sequence of steps into a chain of equalities
mkCalcSteps :: SymVal a => (SBool, TPProofRaw (SBV a)) -> ([Int] -> Symbolic SBool) -> Symbolic CalcStrategy
mkCalcSteps (intros, tpp) qcInstance = do
        pure $ CalcStrategy { calcIntros     = intros
                            , calcProofTree  = mkProofTree ((.===), (.===)) tpp
                            , calcQCInstance = qcInstance
                            }

-- | Given initial hypothesis, and a raw proof tree, build the quick-check walk over this tree for the step that's marked as such.
qcRun :: SymVal a => [Int] -> (SBool, TPProofRaw (SBV a)) -> Symbolic SBool
qcRun checkedLabel (intros, tpp) = do
        results <- runTree sTrue 1 ([1], mkProofTree (\a b -> (a, b, a .=== b), (.==)) tpp)
        case [b | (l, b) <- results, l == checkedLabel] of
          [(caseCond, b)] -> do constrain $ intros .&& caseCond
                                pure b
          []              -> notFound
          _               -> die "Hit the label multiple times."

 where die why =  error $ unlines [ ""
                                  , "*** Data.SBV.patch: Impossible happened."
                                  , "***"
                                  , "*** " ++ why
                                  , "***"
                                  , "*** While trying to quickcheck at level " ++ show checkedLabel
                                  , "*** Please report this as a bug!"
                                  ]

       -- It is possible that we may not find the node. Why? Because it might be under a case-split (ite essentially)
       -- and the random choices we made before-hand may just not get us there. Sigh. So, the right thing to do is
       -- to just say "we're good." But this can also indicate a bug in our code. Oh well, we'll ignore it.
       notFound = pure sTrue

       -- "run" the tree, and if we hit the correct label return the result.
       -- This needs to be in "sync" with proveProofTree for obvious reasons. So, any changes there
       -- make it here too!
       runTree :: SymVal a => SBool -> Int -> ([Int], TPProofGen (SBV a, SBV a, SBool) [String] SBool) -> Symbolic [([Int], (SBool, SBool))]
       runTree _        _     (_,  ProofEnd{})         = pure []
       runTree caseCond level (bn, ProofBranch _ _ ps) = concat <$> sequence [runTree (caseCond .&& branchCond) (level + 1) (bn ++ [i, 1], p)
                                                                             | (i, (branchCond, p)) <- zip [1..] ps
                                                                             ]
       runTree caseCond level (bn, ProofStep (lhs, rhs, cur) hs p) = do rest <- runTree caseCond level (nextProofStep bn, p)
                                                                        when (bn == checkedLabel) $ do
                                                                                sObserve "lhs" lhs
                                                                                sObserve "rhs" rhs
                                                                                mapM_ (uncurry S.sObserve) [(n, v) | HelperDisp n v <- hs]
                                                                        pure $ (bn, (caseCond, cur)) : rest

-- | Chaining lemmas that depend on no extra variables
instance Calc SBool where
   calcSteps result steps = (result,) <$> mkCalcSteps steps (`qcRun` steps)

-- | Chaining lemmas that depend on a single extra variable.
instance (KnownSymbol na, SymVal a) => Calc (Forall na a -> SBool) where
   calcSteps result steps = do a  <- free (symbolVal (Proxy @na))
                               let q checkedLabel = do aa <- free (symbolVal (Proxy @na))
                                                       qcRun checkedLabel (steps aa)
                               (result (Forall a),) <$> mkCalcSteps (steps a) q

-- | Chaining lemmas that depend on two extra variables.
instance (KnownSymbol na, SymVal a, KnownSymbol nb, SymVal b) => Calc (Forall na a -> Forall nb b -> SBool) where
   calcSteps result steps = do (a, b) <- (,) <$> free (symbolVal (Proxy @na)) <*> free (symbolVal (Proxy @nb))
                               let q checkedLabel = do (aa, ab) <- (,) <$> free (symbolVal (Proxy @na)) <*> free (symbolVal (Proxy @nb))
                                                       qcRun checkedLabel (steps aa ab)
                               (result (Forall a) (Forall b),) <$> mkCalcSteps (steps a b) q

-- | Chaining lemmas that depend on three extra variables.
instance (KnownSymbol na, SymVal a, KnownSymbol nb, SymVal b, KnownSymbol nc, SymVal c) => Calc (Forall na a -> Forall nb b -> Forall nc c -> SBool) where
   calcSteps result steps = do (a, b, c) <- (,,) <$> free (symbolVal (Proxy @na)) <*> free (symbolVal (Proxy @nb)) <*> free (symbolVal (Proxy @nc))
                               let q checkedLabel = do (aa, ab, ac) <- (,,) <$> free (symbolVal (Proxy @na)) <*> free (symbolVal (Proxy @nb)) <*> free (symbolVal (Proxy @nc))
                                                       qcRun checkedLabel (steps aa ab ac)
                               (result (Forall a) (Forall b) (Forall c),) <$> mkCalcSteps (steps a b c) q

-- | Chaining lemmas that depend on four extra variables.
instance (KnownSymbol na, SymVal a, KnownSymbol nb, SymVal b, KnownSymbol nc, SymVal c, KnownSymbol nd, SymVal d) => Calc (Forall na a -> Forall nb b -> Forall nc c -> Forall nd d -> SBool) where
   calcSteps result steps = do (a, b, c, d) <- (,,,) <$> free (symbolVal (Proxy @na)) <*> free (symbolVal (Proxy @nb)) <*> free (symbolVal (Proxy @nc)) <*> free (symbolVal (Proxy @nd))
                               let q checkedLabel = do sb <- steps <$> free (symbolVal (Proxy @na)) <*> free (symbolVal (Proxy @nb)) <*> free (symbolVal (Proxy @nc)) <*> free (symbolVal (Proxy @nd))
                                                       qcRun checkedLabel sb
                               (result (Forall a) (Forall b) (Forall c) (Forall d),) <$> mkCalcSteps (steps a b c d) q

-- | Chaining lemmas that depend on five extra variables.
instance (KnownSymbol na, SymVal a, KnownSymbol nb, SymVal b, KnownSymbol nc, SymVal c, KnownSymbol nd, SymVal d, KnownSymbol ne, SymVal e)
      => Calc (Forall na a -> Forall nb b -> Forall nc c -> Forall nd d -> Forall ne e -> SBool) where
   calcSteps result steps = do (a, b, c, d, e) <- (,,,,) <$> free (symbolVal (Proxy @na)) <*> free (symbolVal (Proxy @nb)) <*> free (symbolVal (Proxy @nc)) <*> free (symbolVal (Proxy @nd)) <*> free (symbolVal (Proxy @ne))
                               let q checkedLabel = do sb <- steps <$> free (symbolVal (Proxy @na)) <*> free (symbolVal (Proxy @nb)) <*> free (symbolVal (Proxy @nc)) <*> free (symbolVal (Proxy @nd)) <*> free (symbolVal (Proxy @ne))
                                                       qcRun checkedLabel sb
                               (result (Forall a) (Forall b) (Forall c) (Forall d) (Forall e),) <$> mkCalcSteps (steps a b c d e) q

-- | Captures the schema for an inductive proof. Base case might be nothing, to cover strong induction.
data InductionStrategy = InductionStrategy { inductionIntros     :: SBool
                                           , inductionMeasure    :: Maybe (SBool, [ProofObj])
                                           , inductionBaseCase   :: Maybe SBool
                                           , inductionProofTree  :: TPProof
                                           , inductiveStep       :: SBool
                                           , inductiveQCInstance :: [Int] -> Symbolic SBool
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
  = inductionIntros
  : inductiveStep
  : proofTreeSaturatables inductionProofSteps
  ++ measureDs
  ++ maybeToList inductionBaseCase
  where objDeps p = getObjProof p : concatMap objDeps (dependencies p)
        measureDs = case inductionMeasure of
                      Nothing      -> []
                      Just (a, ps) -> a : concatMap objDeps ps

-- | A class for doing regular inductive proofs.
class Inductive a where
   type IHType a :: Type
   type IHArg  a :: Type

   -- | Inductively prove a lemma, using the default config.
   -- Inductive proofs over lists only hold for finite lists. We also assume that all functions involved are terminating. SBV does not prove termination, so only
   -- partial correctness is guaranteed if non-terminating functions are involved.
   induct  :: (Proposition a, SymVal t, EqSymbolic (SBV t)) => String -> a -> (Proof (IHType a) -> IHArg a -> IStepArgs a t) -> TP (Proof a)

   -- | Same as 'induct', but with the given solver configuration.
   -- Inductive proofs over lists only hold for finite lists. We also assume that all functions involved are terminating. SBV does not prove termination, so only
   -- partial correctness is guaranteed if non-terminating functions are involved.
   inductWith :: (Proposition a, SymVal t, EqSymbolic (SBV t)) => SMTConfig -> String -> a -> (Proof (IHType a) -> IHArg a -> IStepArgs a t) -> TP (Proof a)

   induct         nm p steps = getTPConfig >>= \cfg  -> inductWith                             cfg                   nm p steps
   inductWith cfg nm p steps = getTPConfig >>= \cfg' -> inductionEngine RegularInduction False (tpMergeCfg cfg cfg') nm p (inductionStrategy p steps)

   -- | Internal, shouldn't be needed outside the library
   {-# MINIMAL inductionStrategy #-}
   inductionStrategy :: (Proposition a, SymVal t, EqSymbolic (SBV t)) => a -> (Proof (IHType a) -> IHArg a -> IStepArgs a t) -> Symbolic InductionStrategy

-- | A class of values, capturing the zero of a measure value
class OrdSymbolic (SBV a) => Zero a where
  zero :: SBV a

-- | An integer as a measure
instance Zero Integer where
   zero = literal 0

-- | A tuple of integers as a measure
instance Zero (Integer, Integer) where
  zero = literal (0, 0)

-- | A triple of integers as a measure
instance Zero (Integer, Integer, Integer) where
  zero = literal (0, 0, 0)

-- | A quadruple of integers as a measure
instance Zero (Integer, Integer, Integer, Integer) where
  zero = literal (0, 0, 0, 0)

instance Zero (Integer, Integer, Integer, Integer, Integer) where
  zero = literal (0, 0, 0, 0, 0)

-- | A class for doing generalized measure based strong inductive proofs.
class SInductive a where
   -- | Inductively prove a lemma, using measure based induction, using the default config.
   -- Inductive proofs over lists only hold for finite lists. We also assume that all functions involved are terminating. SBV does not prove termination, so only
   -- partial correctness is guaranteed if non-terminating functions are involved.
   sInduct :: (Proposition a, Zero m, SymVal t, EqSymbolic (SBV t)) => String -> a -> (MeasureArgs a m, [ProofObj]) -> (Proof a -> StepArgs a t) -> TP (Proof a)

   -- | Same as 'sInduct', but with the given solver configuration.
   -- Inductive proofs over lists only hold for finite lists. We also assume that all functions involved are terminating. SBV does not prove termination, so only
   -- partial correctness is guaranteed if non-terminating functions are involved.
   sInductWith :: (Proposition a, Zero m, SymVal t, EqSymbolic (SBV t)) => SMTConfig -> String -> a -> (MeasureArgs a m, [ProofObj]) -> (Proof a -> StepArgs a t) -> TP (Proof a)

   sInduct         nm p mhs steps = getTPConfig >>= \cfg  -> sInductWith                            cfg                   nm p mhs steps
   sInductWith cfg nm p mhs steps = getTPConfig >>= \cfg' -> inductionEngine GeneralInduction False (tpMergeCfg cfg cfg') nm p (sInductionStrategy p mhs steps)

   -- | Internal, shouldn't be needed outside the library
   {-# MINIMAL sInductionStrategy #-}
   sInductionStrategy :: (Proposition a, Zero m, SymVal t, EqSymbolic (SBV t)) => a -> (MeasureArgs a m, [ProofObj]) -> (Proof a -> StepArgs a t) -> Symbolic InductionStrategy

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
          Nothing      -> queryDebug [nm ++ ": Induction" ++ qual ++ ", there is no custom measure to show non-negativeness."]
          Just (m, hs) -> do queryDebug [nm ++ ": Induction, proving measure is always non-negative:"]
                             smtProofStep cfg tpSt "Step" 1
                                                   (TPProofStep False nm [] ["Measure is non-negative"])
                                                   (Just (sAnd (inductionIntros : map getObjProof hs)))
                                                   m
                                                   []
                                                   (\d -> finishTP cfg "Q.E.D." d [])
       case inductionBaseCase of
          Nothing -> queryDebug [nm ++ ": Induction" ++ qual ++ ", there is no base case to prove."]
          Just bc -> do queryDebug [nm ++ ": Induction, proving base case:"]
                        smtProofStep cfg tpSt "Step" 1
                                              (TPProofStep False nm [] ["Base"])
                                              (Just inductionIntros)
                                              bc
                                              []
                                              (\d -> finishTP cfg "Q.E.D." d [])

       proveProofTree cfg tpSt nm (result, inductiveStep) inductionIntros inductionProofTree u inductiveQCInstance

-- Induction strategy helper
mkIndStrategy :: (SymVal a, EqSymbolic (SBV a)) => Maybe (SBool, [ProofObj]) -> Maybe SBool -> (SBool, TPProofRaw (SBV a)) -> SBool -> ([Int] -> Symbolic SBool) -> Symbolic InductionStrategy
mkIndStrategy mbMeasure mbBaseCase indSteps step indQCInstance = do
        CalcStrategy { calcIntros, calcProofTree, calcQCInstance } <- mkCalcSteps indSteps indQCInstance
        pure $ InductionStrategy { inductionIntros     = calcIntros
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
mkLVar :: (KnownSymbol n, SymVal a) => proxy n -> Symbolic (SBV a, SList a, String, String, String)
mkLVar x = do let nxs = symbolVal x
                  nx  = singular nxs
              e  <- free nx
              es <- free nxs
              pure (e, es, nx, nxs, nx ++ ":" ++ nxs)

-- | Helper for induction result
indResult :: [String] -> SBool -> SBool
indResult nms = observeIf not ("P(" ++ intercalate ", " nms ++ ")")

-- | Induction over 'SInteger'
instance KnownSymbol nn => Inductive (Forall nn Integer -> SBool) where
  type IHType (Forall nn Integer -> SBool) = SBool
  type IHArg  (Forall nn Integer -> SBool) = SInteger

  inductionStrategy result steps = do
       (n, nn) <- mkVar (Proxy @nn)

       let bc = result (Forall 0)
           ih = internalAxiom "IH" (n .>= zero .=> result (Forall n))

       mkIndStrategy Nothing
                     (Just bc)
                     (steps ih n)
                     (indResult [nn ++ "+1"] (result (Forall (n+1))))
                     (\checkedLabel -> free nn >>= qcRun checkedLabel . steps ih)

-- | Induction over 'SInteger', taking an extra argument
instance (KnownSymbol nn, KnownSymbol na, SymVal a) => Inductive (Forall nn Integer -> Forall na a -> SBool) where
  type IHType (Forall nn Integer -> Forall na a -> SBool) = Forall na a -> SBool
  type IHArg  (Forall nn Integer -> Forall na a -> SBool) = SInteger

  inductionStrategy result steps = do
       (n, nn) <- mkVar (Proxy @nn)
       (a, na) <- mkVar (Proxy @na)

       let bc = result (Forall 0) (Forall a)
           ih = internalAxiom "IH" (\(Forall a' :: Forall na a) -> n .>= zero .=> result (Forall n) (Forall a'))

       mkIndStrategy Nothing
                     (Just bc)
                     (steps ih n a)
                     (indResult [nn ++ "+1", na] (result (Forall (n+1)) (Forall a)))
                     (\checkedLabel -> steps ih <$> free nn <*> free na >>= qcRun checkedLabel)

-- | Induction over 'SInteger', taking two extra arguments
instance (KnownSymbol nn, KnownSymbol na, SymVal a, KnownSymbol nb, SymVal b) => Inductive (Forall nn Integer -> Forall na a -> Forall nb b -> SBool) where
  type IHType (Forall nn Integer -> Forall na a -> Forall nb b -> SBool) = Forall na a -> Forall nb b -> SBool
  type IHArg  (Forall nn Integer -> Forall na a -> Forall nb b -> SBool) = SInteger

  inductionStrategy result steps = do
       (n, nn) <- mkVar (Proxy @nn)
       (a, na) <- mkVar (Proxy @na)
       (b, nb) <- mkVar (Proxy @nb)

       let bc = result (Forall 0) (Forall a) (Forall b)
           ih = internalAxiom "IH" (\(Forall a' :: Forall na a) (Forall b' :: Forall nb b) -> n .>= zero .=> result (Forall n) (Forall a') (Forall b'))

       mkIndStrategy Nothing
                     (Just bc)
                     (steps ih n a b)
                     (indResult [nn ++ "+1", na, nb] (result (Forall (n+1)) (Forall a) (Forall b)))
                     (\checkedLabel -> steps ih <$> free nn <*> free na <*> free nb >>= qcRun checkedLabel)

-- | Induction over 'SInteger', taking three extra arguments
instance (KnownSymbol nn, KnownSymbol na, SymVal a, KnownSymbol nb, SymVal b, KnownSymbol nc, SymVal c) => Inductive (Forall nn Integer -> Forall na a -> Forall nb b -> Forall nc c -> SBool) where
  type IHType (Forall nn Integer -> Forall na a -> Forall nb b -> Forall nc c -> SBool) = Forall na a -> Forall nb b -> Forall nc c -> SBool
  type IHArg  (Forall nn Integer -> Forall na a -> Forall nb b -> Forall nc c -> SBool) = SInteger

  inductionStrategy result steps = do
       (n, nn) <- mkVar (Proxy @nn)
       (a, na) <- mkVar (Proxy @na)
       (b, nb) <- mkVar (Proxy @nb)
       (c, nc) <- mkVar (Proxy @nc)

       let bc = result (Forall 0) (Forall a) (Forall b) (Forall c)
           ih = internalAxiom "IH" (\(Forall a' :: Forall na a) (Forall b' :: Forall nb b) (Forall c' :: Forall nc c) -> n .>= zero .=> result (Forall n) (Forall a') (Forall b') (Forall c'))

       mkIndStrategy Nothing
                     (Just bc)
                     (steps ih n a b c)
                     (indResult [nn ++ "+1", na, nb, nc] (result (Forall (n+1)) (Forall a) (Forall b) (Forall c)))
                     (\checkedLabel -> steps ih <$> free nn <*> free na <*> free nb <*> free nc >>= qcRun checkedLabel)

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

       let bc = result (Forall 0) (Forall a) (Forall b) (Forall c) (Forall d)
           ih = internalAxiom "IH" (\(Forall a' :: Forall na a) (Forall b' :: Forall nb b) (Forall c' :: Forall nc c) (Forall d' :: Forall nd d) -> n .>= zero .=> result (Forall n) (Forall a') (Forall b') (Forall c') (Forall d'))

       mkIndStrategy Nothing
                     (Just bc)
                     (steps ih n a b c d)
                     (indResult [nn ++ "+1", na, nb, nc, nd] (result (Forall (n+1)) (Forall a) (Forall b) (Forall c) (Forall d)))
                     (\checkedLabel -> steps ih <$> free nn <*> free na <*> free nb <*> free nc <*> free nd >>= qcRun checkedLabel)

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

       let bc = result (Forall 0) (Forall a) (Forall b) (Forall c) (Forall d) (Forall e)
           ih = internalAxiom "IH" (\(Forall a' :: Forall na a) (Forall b' :: Forall nb b) (Forall c' :: Forall nc c) (Forall d' :: Forall nd d) (Forall e' :: Forall ne e) -> n .>= zero .=> result (Forall n) (Forall a') (Forall b') (Forall c') (Forall d') (Forall e'))

       mkIndStrategy Nothing
                     (Just bc)
                     (steps ih n a b c d e)
                     (indResult [nn ++ "+1", na, nb, nc, nd, ne] (result (Forall (n+1)) (Forall a) (Forall b) (Forall c) (Forall d) (Forall e)))
                     (\checkedLabel -> steps ih <$> free nn <*> free na <*> free nb <*> free nc <*> free nd <*> free ne >>= qcRun checkedLabel)

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
       (x, xs, nx, nxs, nxxs) <- mkLVar (Proxy @nxs)

       let bc = result (Forall SL.nil)
           ih = internalAxiom "IH" (result (Forall xs))

       mkIndStrategy Nothing
                     (Just bc)
                     (steps ih (x, xs))
                     (indResult [nxxs] (result (Forall (x SL..: xs))))
                     (\checkedLabel ->  ((,) <$> free nx <*> free nxs) >>= qcRun checkedLabel . steps ih)

-- | Induction over 'SList', taking an extra argument
instance (KnownSymbol nxs, SymVal x, KnownSymbol na, SymVal a) => Inductive (Forall nxs [x] -> Forall na a -> SBool) where
  type IHType (Forall nxs [x] -> Forall na a -> SBool) = Forall na a -> SBool
  type IHArg  (Forall nxs [x] -> Forall na a -> SBool) = (SBV x, SList x)

  inductionStrategy result steps = do
       (x, xs, nx, nxs, nxxs) <- mkLVar (Proxy @nxs)
       (a, na)                <- mkVar  (Proxy @na)

       let bc = result (Forall SL.nil) (Forall a)
           ih = internalAxiom "IH" (\(Forall a' :: Forall na a) -> result (Forall xs) (Forall a'))

       mkIndStrategy Nothing
                     (Just bc)
                     (steps ih (x, xs) a)
                     (indResult [nxxs, na] (result (Forall (x SL..: xs)) (Forall a)))
                     (\checkedLabel -> steps ih <$> ((,) <$> free nx <*> free nxs) <*> free na >>= qcRun checkedLabel)

-- | Induction over 'SList', taking two extra arguments
instance (KnownSymbol nxs, SymVal x, KnownSymbol na, SymVal a, KnownSymbol nb, SymVal b) => Inductive (Forall nxs [x] -> Forall na a -> Forall nb b -> SBool) where
  type IHType (Forall nxs [x] -> Forall na a -> Forall nb b -> SBool) = Forall na a -> Forall nb b -> SBool
  type IHArg  (Forall nxs [x] -> Forall na a -> Forall nb b -> SBool) = (SBV x, SList x)

  inductionStrategy result steps = do
       (x, xs, nx, nxs, nxxs) <- mkLVar (Proxy @nxs)
       (a, na)                <- mkVar  (Proxy @na)
       (b, nb)                <- mkVar  (Proxy @nb)

       let bc = result (Forall SL.nil) (Forall a) (Forall b)
           ih = internalAxiom "IH" (\(Forall a' :: Forall na a) (Forall b' :: Forall nb b) -> result (Forall xs) (Forall a') (Forall b'))

       mkIndStrategy Nothing
                     (Just bc)
                     (steps ih (x, xs) a b)
                     (indResult [nxxs, na, nb] (result (Forall (x SL..: xs)) (Forall a) (Forall b)))
                     (\checkedLabel -> steps ih <$> ((,) <$> free nx <*> free nxs) <*> free na <*> free nb >>= qcRun checkedLabel)

-- | Induction over 'SList', taking three extra arguments
instance (KnownSymbol nxs, SymVal x, KnownSymbol na, SymVal a, KnownSymbol nb, SymVal b, KnownSymbol nc, SymVal c) => Inductive (Forall nxs [x] -> Forall na a -> Forall nb b -> Forall nc c -> SBool) where
  type IHType (Forall nxs [x] -> Forall na a -> Forall nb b -> Forall nc c -> SBool) = Forall na a -> Forall nb b -> Forall nc c -> SBool
  type IHArg  (Forall nxs [x] -> Forall na a -> Forall nb b -> Forall nc c -> SBool) = (SBV x, SList x)

  inductionStrategy result steps = do
       (x, xs, nx, nxs, nxxs) <- mkLVar (Proxy @nxs)
       (a, na)                <- mkVar  (Proxy @na)
       (b, nb)                <- mkVar  (Proxy @nb)
       (c, nc)                <- mkVar  (Proxy @nc)

       let bc = result (Forall SL.nil) (Forall a) (Forall b) (Forall c)
           ih = internalAxiom "IH" (\(Forall a' :: Forall na a) (Forall b' :: Forall nb b) (Forall c' :: Forall nc c) -> result (Forall xs) (Forall a') (Forall b') (Forall c'))

       mkIndStrategy Nothing
                     (Just bc)
                     (steps ih (x, xs) a b c)
                     (indResult [nxxs, na, nb, nc] (result (Forall (x SL..: xs)) (Forall a) (Forall b) (Forall c)))
                     (\checkedLabel -> steps ih <$> ((,) <$> free nx <*> free nxs) <*> free na <*> free nb <*> free nc >>= qcRun checkedLabel)

-- | Induction over 'SList', taking four extra arguments
instance (KnownSymbol nxs, SymVal x, KnownSymbol na, SymVal a, KnownSymbol nb, SymVal b, KnownSymbol nc, SymVal c, KnownSymbol nd, SymVal d) => Inductive (Forall nxs [x] -> Forall na a -> Forall nb b -> Forall nc c -> Forall nd d -> SBool) where
  type IHType (Forall nxs [x] -> Forall na a -> Forall nb b -> Forall nc c -> Forall nd d -> SBool) = Forall na a -> Forall nb b -> Forall nc c -> Forall nd d -> SBool
  type IHArg  (Forall nxs [x] -> Forall na a -> Forall nb b -> Forall nc c -> Forall nd d -> SBool) = (SBV x, SList x)

  inductionStrategy result steps = do
       (x, xs, nx, nxs, nxxs) <- mkLVar (Proxy @nxs)
       (a, na)                <- mkVar  (Proxy @na)
       (b, nb)                <- mkVar  (Proxy @nb)
       (c, nc)                <- mkVar  (Proxy @nc)
       (d, nd)                <- mkVar  (Proxy @nd)

       let bc = result (Forall SL.nil) (Forall a) (Forall b) (Forall c) (Forall d)
           ih = internalAxiom "IH" (\(Forall a' :: Forall na a) (Forall b' :: Forall nb b) (Forall c' :: Forall nc c) (Forall d' :: Forall nd d) -> result (Forall xs) (Forall a') (Forall b') (Forall c') (Forall d'))

       mkIndStrategy Nothing
                     (Just bc)
                     (steps ih (x, xs) a b c d)
                     (indResult [nxxs, na, nb, nc, nd] (result (Forall (x SL..: xs)) (Forall a) (Forall b) (Forall c) (Forall d)))
                     (\checkedLabel -> steps ih <$> ((,) <$> free nx <*> free nxs) <*> free na <*> free nb <*> free nc <*> free nd >>= qcRun checkedLabel)

-- | Induction over 'SList', taking five extra arguments
instance (KnownSymbol nxs, SymVal x, KnownSymbol na, SymVal a, KnownSymbol nb, SymVal b, KnownSymbol nc, SymVal c, KnownSymbol nd, SymVal d, KnownSymbol ne, SymVal e) => Inductive (Forall nxs [x] -> Forall na a -> Forall nb b -> Forall nc c -> Forall nd d -> Forall ne e -> SBool) where
  type IHType (Forall nxs [x] -> Forall na a -> Forall nb b -> Forall nc c -> Forall nd d -> Forall ne e -> SBool) = Forall na a -> Forall nb b -> Forall nc c -> Forall nd d -> Forall ne e -> SBool
  type IHArg  (Forall nxs [x] -> Forall na a -> Forall nb b -> Forall nc c -> Forall nd d -> Forall ne e -> SBool) = (SBV x, SList x)

  inductionStrategy result steps = do
       (x, xs, nx, nxs, nxxs) <- mkLVar (Proxy @nxs)
       (a, na)                <- mkVar  (Proxy @na)
       (b, nb)                <- mkVar  (Proxy @nb)
       (c, nc)                <- mkVar  (Proxy @nc)
       (d, nd)                <- mkVar  (Proxy @nd)
       (e, ne)                <- mkVar  (Proxy @ne)

       let bc = result (Forall SL.nil) (Forall a) (Forall b) (Forall c) (Forall d) (Forall e)
           ih = internalAxiom "IH" (\(Forall a' :: Forall na a) (Forall b' :: Forall nb b) (Forall c' :: Forall nc c) (Forall d' :: Forall nd d) (Forall e' :: Forall ne e) -> result (Forall xs) (Forall a') (Forall b') (Forall c') (Forall d') (Forall e'))

       mkIndStrategy Nothing
                     (Just bc)
                     (steps ih (x, xs) a b c d e)
                     (indResult [nxxs, na, nb, nc, nd, ne] (result (Forall (x SL..: xs)) (Forall a) (Forall b) (Forall c) (Forall d) (Forall e)))
                     (\checkedLabel -> steps ih <$> ((,) <$> free nx <*> free nxs) <*> free na <*> free nb <*> free nc <*> free nd <*> free ne >>= qcRun checkedLabel)

-- | Induction over two 'SList', simultaneously
instance (KnownSymbol nxs, SymVal x, KnownSymbol nys, SymVal y) => Inductive ((Forall nxs [x], Forall nys [y]) -> SBool) where
  type IHType ((Forall nxs [x], Forall nys [y]) -> SBool) = SBool
  type IHArg  ((Forall nxs [x], Forall nys [y]) -> SBool) = (SBV x, SList x, SBV y, SList y)

  inductionStrategy result steps = do
       (x, xs, nx, nxs, nxxs) <- mkLVar (Proxy @nxs)
       (y, ys, ny, nys, nyys) <- mkLVar (Proxy @nys)

       let bc = result (Forall SL.nil, Forall SL.nil) .&& result (Forall SL.nil, Forall (y SL..: ys)) .&& result (Forall (x SL..: xs), Forall SL.nil)
           ih = internalAxiom "IH" (result (Forall xs, Forall ys))

       mkIndStrategy Nothing
                     (Just bc)
                     (steps ih (x, xs, y, ys))
                     (indResult [nxxs, nyys] (result (Forall (x SL..: xs), Forall (y SL..: ys))))
                     (\checkedLabel -> ((,,,) <$> free nx <*> free nxs <*> free ny <*> free nys) >>= qcRun checkedLabel . steps ih)

-- | Induction over two 'SList', simultaneously, taking an extra argument
instance (KnownSymbol nxs, SymVal x, KnownSymbol nys, SymVal y, KnownSymbol na, SymVal a) => Inductive ((Forall nxs [x], Forall nys [y]) -> Forall na a -> SBool) where
  type IHType ((Forall nxs [x], Forall nys [y]) -> Forall na a -> SBool) = Forall na a -> SBool
  type IHArg  ((Forall nxs [x], Forall nys [y]) -> Forall na a -> SBool) = (SBV x, SList x, SBV y, SList y)

  inductionStrategy result steps = do
       (x, xs, nx, nxs, nxxs) <- mkLVar (Proxy @nxs)
       (y, ys, ny, nys, nyys) <- mkLVar (Proxy @nys)
       (a, na)                <- mkVar  (Proxy @na)

       let bc = result (Forall SL.nil, Forall SL.nil) (Forall a) .&& result (Forall SL.nil, Forall (y SL..: ys)) (Forall a) .&& result (Forall (x SL..: xs), Forall SL.nil) (Forall a)
           ih = internalAxiom "IH" (\(Forall a' :: Forall na a) -> result (Forall xs, Forall ys) (Forall a'))

       mkIndStrategy Nothing
                     (Just bc)
                     (steps ih (x, xs, y, ys) a)
                     (indResult [nxxs, nyys, na] (result (Forall (x SL..: xs), Forall (y SL..: ys)) (Forall a)))
                     (\checkedLabel -> steps ih <$> ((,,,) <$> free nx <*> free nxs <*> free ny <*> free nys) <*> free na >>= qcRun checkedLabel)

-- | Induction over two 'SList', simultaneously, taking two extra arguments
instance (KnownSymbol nxs, SymVal x, KnownSymbol nys, SymVal y, KnownSymbol na, SymVal a, KnownSymbol nb, SymVal b) => Inductive ((Forall nxs [x], Forall nys [y]) -> Forall na a -> Forall nb b -> SBool) where
  type IHType ((Forall nxs [x], Forall nys [y]) -> Forall na a -> Forall nb b -> SBool) = Forall na a -> Forall nb b -> SBool
  type IHArg  ((Forall nxs [x], Forall nys [y]) -> Forall na a -> Forall nb b -> SBool) = (SBV x, SList x, SBV y, SList y)

  inductionStrategy result steps = do
       (x, xs, nx, nxs, nxxs) <- mkLVar (Proxy @nxs)
       (y, ys, ny, nys, nyys) <- mkLVar (Proxy @nys)
       (a, na)                <- mkVar  (Proxy @na)
       (b, nb)                <- mkVar  (Proxy @nb)

       let bc = result (Forall SL.nil, Forall SL.nil) (Forall a) (Forall b) .&& result (Forall SL.nil, Forall (y SL..: ys)) (Forall a) (Forall b) .&& result (Forall (x SL..: xs), Forall SL.nil) (Forall a) (Forall b)
           ih = internalAxiom "IH" (\(Forall a' :: Forall na a) (Forall b' :: Forall nb b) -> result (Forall xs, Forall ys) (Forall a') (Forall b'))

       mkIndStrategy Nothing
                     (Just bc)
                     (steps ih (x, xs, y, ys) a b)
                     (indResult [nxxs, nyys, na, nb] (result (Forall (x SL..: xs), Forall (y SL..: ys)) (Forall a) (Forall b)))
                     (\checkedLabel -> steps ih <$> ((,,,) <$> free nx <*> free nxs <*> free ny <*> free nys) <*> free na <*> free nb >>= qcRun checkedLabel)

-- | Induction over two 'SList', simultaneously, taking three extra arguments
instance (KnownSymbol nxs, SymVal x, KnownSymbol nys, SymVal y, KnownSymbol na, SymVal a, KnownSymbol nb, SymVal b, KnownSymbol nc, SymVal c) => Inductive ((Forall nxs [x], Forall nys [y]) -> Forall na a -> Forall nb b -> Forall nc c -> SBool) where
  type IHType ((Forall nxs [x], Forall nys [y]) -> Forall na a -> Forall nb b -> Forall nc c -> SBool) = Forall na a -> Forall nb b -> Forall nc c -> SBool
  type IHArg  ((Forall nxs [x], Forall nys [y]) -> Forall na a -> Forall nb b -> Forall nc c -> SBool) = (SBV x, SList x, SBV y, SList y)

  inductionStrategy result steps = do
       (x, xs, nx, nxs, nxxs) <- mkLVar (Proxy @nxs)
       (y, ys, ny, nys, nyys) <- mkLVar (Proxy @nys)
       (a, na)                <- mkVar  (Proxy @na)
       (b, nb)                <- mkVar  (Proxy @nb)
       (c, nc)                <- mkVar  (Proxy @nc)

       let bc = result (Forall SL.nil, Forall SL.nil) (Forall a) (Forall b) (Forall c) .&& result (Forall SL.nil, Forall (y SL..: ys)) (Forall a) (Forall b) (Forall c) .&& result (Forall (x SL..: xs), Forall SL.nil) (Forall a) (Forall b) (Forall c)
           ih = internalAxiom "IH" (\(Forall a' :: Forall na a) (Forall b' :: Forall nb b) (Forall c' :: Forall nc c) -> result (Forall xs, Forall ys) (Forall a') (Forall b') (Forall c'))

       mkIndStrategy Nothing
                     (Just bc)
                     (steps ih (x, xs, y, ys) a b c)
                     (indResult [nxxs, nyys, na, nb, nc] (result (Forall (x SL..: xs), Forall (y SL..: ys)) (Forall a) (Forall b) (Forall c)))
                     (\checkedLabel -> steps ih <$> ((,,,) <$> free nx <*> free nxs <*> free ny <*> free nys) <*> free na <*> free nb <*> free nc >>= qcRun checkedLabel)

-- | Induction over two 'SList', simultaneously, taking four extra arguments
instance (KnownSymbol nxs, SymVal x, KnownSymbol nys, SymVal y, KnownSymbol na, SymVal a, KnownSymbol nb, SymVal b, KnownSymbol nc, SymVal c, KnownSymbol nd, SymVal d) => Inductive ((Forall nxs [x], Forall nys [y]) -> Forall na a -> Forall nb b -> Forall nc c -> Forall nd d -> SBool) where
  type IHType ((Forall nxs [x], Forall nys [y]) -> Forall na a -> Forall nb b -> Forall nc c -> Forall nd d -> SBool) = Forall na a -> Forall nb b -> Forall nc c -> Forall nd d -> SBool
  type IHArg  ((Forall nxs [x], Forall nys [y]) -> Forall na a -> Forall nb b -> Forall nc c -> Forall nd d -> SBool) = (SBV x, SList x, SBV y, SList y)

  inductionStrategy result steps = do
       (x, xs, nx, nxs, nxxs) <- mkLVar (Proxy @nxs)
       (y, ys, ny, nys, nyys) <- mkLVar (Proxy @nys)
       (a, na)                <- mkVar  (Proxy @na)
       (b, nb)                <- mkVar  (Proxy @nb)
       (c, nc)                <- mkVar  (Proxy @nc)
       (d, nd)                <- mkVar  (Proxy @nd)

       let bc = result (Forall SL.nil, Forall SL.nil) (Forall a) (Forall b) (Forall c) (Forall d) .&& result (Forall SL.nil, Forall (y SL..: ys)) (Forall a) (Forall b) (Forall c) (Forall d) .&& result (Forall (x SL..: xs), Forall SL.nil) (Forall a) (Forall b) (Forall c) (Forall d)
           ih = internalAxiom "IH" (\(Forall a' :: Forall na a) (Forall b' :: Forall nb b) (Forall c' :: Forall nc c) (Forall d' :: Forall nd d) -> result (Forall xs, Forall ys) (Forall a') (Forall b') (Forall c') (Forall d'))

       mkIndStrategy Nothing
                     (Just bc)
                     (steps ih (x, xs, y, ys) a b c d)
                     (indResult [nxxs, nyys, na, nb, nc, nd] (result (Forall (x SL..: xs), Forall (y SL..: ys)) (Forall a) (Forall b) (Forall c) (Forall d)))
                     (\checkedLabel -> steps ih <$> ((,,,) <$> free nx <*> free nxs <*> free ny <*> free nys) <*> free na <*> free nb <*> free nc <*> free nd >>= qcRun checkedLabel)

-- | Induction over two 'SList', simultaneously, taking five extra arguments
instance (KnownSymbol nxs, SymVal x, KnownSymbol nys, SymVal y, KnownSymbol na, SymVal a, KnownSymbol nb, SymVal b, KnownSymbol nc, SymVal c, KnownSymbol nd, SymVal d, KnownSymbol ne, SymVal e) => Inductive ((Forall nxs [x], Forall nys [y]) -> Forall na a -> Forall nb b -> Forall nc c -> Forall nd d -> Forall ne e -> SBool) where
  type IHType ((Forall nxs [x], Forall nys [y]) -> Forall na a -> Forall nb b -> Forall nc c -> Forall nd d -> Forall ne e -> SBool) = Forall na a -> Forall nb b -> Forall nc c -> Forall nd d -> Forall ne e -> SBool
  type IHArg  ((Forall nxs [x], Forall nys [y]) -> Forall na a -> Forall nb b -> Forall nc c -> Forall nd d -> Forall ne e -> SBool) = (SBV x, SList x, SBV y, SList y)

  inductionStrategy result steps = do
       (x, xs, nx, nxs, nxxs) <- mkLVar (Proxy @nxs)
       (y, ys, ny, nys, nyys) <- mkLVar (Proxy @nys)
       (a, na)                <- mkVar  (Proxy @na)
       (b, nb)                <- mkVar  (Proxy @nb)
       (c, nc)                <- mkVar  (Proxy @nc)
       (d, nd)                <- mkVar  (Proxy @nd)
       (e, ne)                <- mkVar  (Proxy @ne)

       let bc = result (Forall SL.nil, Forall SL.nil) (Forall a) (Forall b) (Forall c) (Forall d) (Forall e) .&& result (Forall SL.nil, Forall (y SL..: ys)) (Forall a) (Forall b) (Forall c) (Forall d) (Forall e) .&& result (Forall (x SL..: xs), Forall SL.nil) (Forall a) (Forall b) (Forall c) (Forall d) (Forall e)
           ih = internalAxiom "IH" (\(Forall a' :: Forall na a) (Forall b' :: Forall nb b) (Forall c' :: Forall nc c) (Forall d' :: Forall nd d) (Forall e' :: Forall ne e) -> result (Forall xs, Forall ys) (Forall a') (Forall b') (Forall c') (Forall d') (Forall e'))

       mkIndStrategy Nothing
                     (Just bc)
                     (steps ih (x, xs, y, ys) a b c d e)
                     (indResult [nxxs, nyys, na, nb, nc, nd, ne] (result (Forall (x SL..: xs), Forall (y SL..: ys)) (Forall a) (Forall b) (Forall c) (Forall d) (Forall e)))
                     (\checkedLabel -> steps ih <$> ((,,,) <$> free nx <*> free nxs <*> free ny <*> free nys) <*> free na <*> free nb <*> free nc <*> free nd <*> free ne >>= qcRun checkedLabel)

-- | Generalized induction with one parameter
instance (KnownSymbol na, SymVal a) => SInductive (Forall na a -> SBool) where
  sInductionStrategy result (measure, helpers) steps = do
      (a, na) <- mkVar (Proxy @na)

      let ih   = internalAxiom "IH" (\(Forall a' :: Forall na a) -> measure a' .< measure a .=> result (Forall a'))
          conc = result (Forall a)

      mkIndStrategy (Just (measure a .>= zero, helpers))
                    Nothing
                    (steps ih a)
                    (indResult [na] conc)
                    (\checkedLabel -> free na >>= qcRun checkedLabel . steps ih)

-- | Generalized induction with two parameters
instance (KnownSymbol na, SymVal a, KnownSymbol nb, SymVal b) => SInductive (Forall na a -> Forall nb b -> SBool) where
  sInductionStrategy result (measure, helpers) steps = do
      (a, na) <- mkVar (Proxy @na)
      (b, nb) <- mkVar (Proxy @nb)

      let ih   = internalAxiom "IH" (\(Forall a' :: Forall na a) (Forall b' :: Forall nb b) -> measure a' b' .< measure a b .=> result (Forall a') (Forall b'))
          conc = result (Forall a) (Forall b)

      mkIndStrategy (Just (measure a b .>= zero, helpers))
                    Nothing
                    (steps ih a b)
                    (indResult [na, nb] conc)
                    (\checkedLabel -> steps ih <$> free na <*> free nb >>= qcRun checkedLabel)

-- | Generalized induction with three parameters
instance (KnownSymbol na, SymVal a, KnownSymbol nb, SymVal b, KnownSymbol nc, SymVal c) => SInductive (Forall na a -> Forall nb b -> Forall nc c -> SBool) where
  sInductionStrategy result (measure, helpers) steps = do
      (a, na) <- mkVar (Proxy @na)
      (b, nb) <- mkVar (Proxy @nb)
      (c, nc) <- mkVar (Proxy @nc)

      let ih   = internalAxiom "IH" (\(Forall a' :: Forall na a) (Forall b' :: Forall nb b) (Forall c' :: Forall nc c) -> measure a' b' c' .< measure a b c .=> result (Forall a') (Forall b') (Forall c'))
          conc = result (Forall a) (Forall b) (Forall c)

      mkIndStrategy (Just (measure a b c .>= zero, helpers))
                    Nothing
                    (steps ih a b c)
                    (indResult [na, nb, nc] conc)
                    (\checkedLabel -> steps ih <$> free na <*> free nb <*> free nc >>= qcRun checkedLabel)

-- | Generalized induction with four parameters
instance (KnownSymbol na, SymVal a, KnownSymbol nb, SymVal b, KnownSymbol nc, SymVal c, KnownSymbol nd, SymVal d) => SInductive (Forall na a -> Forall nb b -> Forall nc c -> Forall nd d -> SBool) where
  sInductionStrategy result (measure, helpers) steps = do
      (a, na) <- mkVar (Proxy @na)
      (b, nb) <- mkVar (Proxy @nb)
      (c, nc) <- mkVar (Proxy @nc)
      (d, nd) <- mkVar (Proxy @nd)

      let ih   = internalAxiom "IH" (\(Forall a' :: Forall na a) (Forall b' :: Forall nb b) (Forall c' :: Forall nc c) (Forall d' :: Forall nd d) -> measure a' b' c' d' .< measure a b c d .=> result (Forall a') (Forall b') (Forall c') (Forall d'))
          conc = result (Forall a) (Forall b) (Forall c) (Forall d)

      mkIndStrategy (Just (measure a b c d .>= zero, helpers))
                    Nothing
                    (steps ih a b c d)
                    (indResult [na, nb, nc, nd] conc)
                    (\checkedLabel -> steps ih <$> free na <*> free nb <*> free nc <*> free nd >>= qcRun checkedLabel)

-- | Generalized induction with five parameters
instance (KnownSymbol na, SymVal a, KnownSymbol nb, SymVal b, KnownSymbol nc, SymVal c, KnownSymbol nd, SymVal d, KnownSymbol ne, SymVal e) => SInductive (Forall na a -> Forall nb b -> Forall nc c -> Forall nd d -> Forall ne e -> SBool) where
  sInductionStrategy result (measure, helpers) steps = do
      (a, na) <- mkVar (Proxy @na)
      (b, nb) <- mkVar (Proxy @nb)
      (c, nc) <- mkVar (Proxy @nc)
      (d, nd) <- mkVar (Proxy @nd)
      (e, ne) <- mkVar (Proxy @ne)

      let ih   = internalAxiom "IH" (\(Forall a' :: Forall na a) (Forall b' :: Forall nb b) (Forall c' :: Forall nc c) (Forall d' :: Forall nd d) (Forall e' :: Forall ne e) -> measure a' b' c' d' e' .< measure a b c d e .=> result (Forall a') (Forall b') (Forall c') (Forall d') (Forall e'))
          conc = result (Forall a) (Forall b) (Forall c) (Forall d) (Forall e)

      mkIndStrategy (Just (measure a b c d e .>= zero, helpers))
                    Nothing
                    (steps ih a b c d e)
                    (indResult [na, nb, nc, nd, ne] conc)
                    (\checkedLabel -> steps ih <$> free na <*> free nb <*> free nc <*> free nd <*> free ne >>= qcRun checkedLabel)

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
data Helper = HelperProof  ProofObj     -- A previously proven theorem
            | HelperAssum  SBool        -- A hypothesis
            | HelperQC     QC.Args      -- Quickcheck with these args
            | HelperString String       -- Just a text, only used for diagnostics
            | HelperDisp   String SVal  -- Show the value of this expression in case of failure

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
getHelperProofs HelperDisp{}    = []

-- | Get proofs from helpers
getHelperAssumes :: Helper -> [SBool]
getHelperAssumes HelperProof  {} = []
getHelperAssumes (HelperAssum b) = [b]
getHelperAssumes HelperQC     {} = []
getHelperAssumes HelperString {} = []
getHelperAssumes HelperDisp{}    = []

-- | Get hint strings from helpers. If there's an explicit comment given, just pass that. If not, collect all the names
getHelperText :: [Helper] -> [String]
getHelperText hs = case [s | HelperString s <- hs] of
                     [] -> concatMap collect hs
                     ss -> ss
  where collect :: Helper -> [String]
        collect (HelperProof  p) = [proofName p | isUserAxiom p]  -- Don't put out internals (inductive hypotheses)
        collect HelperAssum  {}  = []
        collect (HelperQC     i) = ["qc: Running " ++ show (QC.maxSuccess i) ++ " tests"]
        collect (HelperString s) = [s]
        collect HelperDisp{}     = []

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

-- | Start an implicational  proof, with the given hypothesis. Use @[]@ as the
-- first argument if the calculation holds unconditionally. Each step will be a cascading
-- chain of conjunctions of the previous, starting from @sTrue@.
(|->) :: [SBool] -> TPProofRaw SBool -> (SBool, TPProofRaw SBool)
bs |-> p = (sAnd bs, xform sTrue p)
  where xform :: SBool -> TPProofGen SBool [Helper] () -> TPProofGen SBool [Helper] ()
        xform conj (ProofStep   a hs r)  = let ca = conj .&& a in ProofStep ca hs (xform ca r)
        xform conj (ProofBranch b bh ss) = ProofBranch b bh [(bc, xform conj r) | (bc, r) <- ss]
        xform _    (ProofEnd    b hs )   = ProofEnd b hs
infixl 0 |->

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
         ccons  = sNot cnil .&& xs .=== h SL..: t

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
        xcons    = sNot xnil .&& xs .=== hx SL..: tx

        ynil     = SL.null   ys
        (hy, ty) = SL.uncons ys
        ycons    = sNot ynil .&& ys .=== hy SL..: ty

-- | A quick-check step, taking number of tests.
qc :: Int -> Helper
qc cnt = HelperQC QC.stdArgs{QC.maxSuccess = cnt}

-- | A quick-check step, with specific quick-check args.
qcWith :: QC.Args -> Helper
qcWith = HelperQC

-- | Observing values in case of failure.
disp :: String -> SBV a -> Helper
disp n v = HelperDisp n (unSBV v)

-- | Specifying a case-split, helps with the boolean case.
(==>) :: SBool -> TPProofRaw a -> (SBool, TPProofRaw a)
(==>) = (,)
infix 0 ==>

-- | Alternative unicode for `==>`
(⟹) :: SBool -> TPProofRaw a -> (SBool, TPProofRaw a)
(⟹) = (==>)
infix 0 ⟹

-- | Recalling a proof. This essentially sets the verbose output off during this proof. Note that
-- if we're doing stats, we ignore this as the whole point of doing stats is to see steps in detail.
recall :: String -> TP (Proof a) -> TP (Proof a)
recall nm prf = do
  cfg <- getTPConfig
  if printStats (tpOptions cfg)
     then prf
     else do tab <- liftIO $ startTP cfg (verbose cfg) "Lemma" 0 (TPProofOneShot nm [])
             setTPConfig cfg{tpOptions = (tpOptions cfg) {quiet = True}}
             r@Proof{proofOf = ProofObj{dependencies}} <- prf
             setTPConfig cfg
             liftIO $ finishTP cfg ("Q.E.D." ++ concludeModulo dependencies) (tab, Nothing) []
             pure r

{- HLint ignore module "Eta reduce"         -}
{- HLint ignore module "Reduce duplication" -}
