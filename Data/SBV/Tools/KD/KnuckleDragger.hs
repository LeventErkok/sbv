-----------------------------------------------------------------------------
-- |
-- Module    : Data.SBV.Tools.KD.KnuckleDragger
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- A lightweight theorem proving like interface, built on top of SBV.
-- Inspired by and modeled after Philip Zucker's tool with the same
-- name, see <http://github.com/philzook58/knuckledragger>.
--
-- See the directory Documentation.SBV.Examples.KnuckleDragger for various examples.
-----------------------------------------------------------------------------

{-# LANGUAGE ConstraintKinds       #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE DerivingStrategies    #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NamedFieldPuns        #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TypeAbstractions      #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeOperators         #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module Data.SBV.Tools.KD.KnuckleDragger (
         Proposition, Proof, Instantiatable(..), Inst(..)
       , axiom
       , lemma,   lemmaWith
       , theorem, theoremWith
       ,    calc,    calcWith,    calcThm,    calcThmWith
       ,  induct,  inductWith,  inductThm,  inductThmWith
       , sInduct, sInductWith, sInductThm, sInductThmWith
       , sorry
       , KD, runKD, runKDWith, use
       , (|-), (⊢), (=:), (≡), (??), (⁇), split, split2, cases, (==>), (⟹), hyp, hprf, qed, trivial
       ) where

import Data.SBV
import Data.SBV.Core.Model (qSaturateSavingObservables)

import Data.SBV.Control hiding (getProof)

import Data.SBV.Tools.KD.Kernel
import Data.SBV.Tools.KD.Utils

import qualified Data.SBV.List as SL

import Control.Monad (when)
import Control.Monad.Trans (liftIO)

import Data.Char (isSpace)
import Data.List (isPrefixOf, isSuffixOf, intercalate)
import Data.Maybe (catMaybes, maybeToList)

import Data.Proxy
import GHC.TypeLits (KnownSymbol, symbolVal, Symbol)

import Data.SBV.Utils.TDiff

import Data.Dynamic

-- | Bring an IO proof into current proof context.
use :: IO Proof -> KD Proof
use = liftIO

-- | Captures the steps for a calculationa proof
data CalcStrategy = CalcStrategy { calcIntros    :: SBool
                                 , calcProofTree :: KDProof
                                 }

-- | Saturatable things in steps
proofTreeSaturatables :: KDProof -> [SBool]
proofTreeSaturatables = go
  where go (ProofEnd    b            hs)    = b : concatMap getH hs
        go (ProofStep   a            hs r)  = a : concatMap getH hs ++ go r
        go (ProofBranch  (_ :: Bool) () ps) = concat [b : go p | (b, p) <- ps]

        getH (HelperProof  p) = [getProof p]
        getH (HelperAssum  b) = [b]

-- | Things that are inside calc-strategy that we have to saturate
getCalcStrategySaturatables :: CalcStrategy -> [SBool]
getCalcStrategySaturatables (CalcStrategy calcIntros calcProofTree) = calcIntros : proofTreeSaturatables calcProofTree

-- | Propagate the settings for ribbon/timing from top to current. Because in any subsequent configuration
-- in a lemmaWith, inductWith etc., we just want to change the solver, not the actual settings for KD.
kdMergeCfg :: SMTConfig -> SMTConfig -> SMTConfig
kdMergeCfg cur top = cur{kdOptions = kdOptions top}

-- | A class for doing equational reasoning style calculational proofs. Use 'calc' to prove a given theorem
-- as a sequence of equalities, each step following from the previous.
class CalcLemma a steps where

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
  -- If @H@ is a singleton, then we bail out. A single step in @H@ indicates a usage mistake, since there's
  -- no sequence of steps to reason about.
  calc :: Proposition a => String -> a -> steps -> KD Proof

  -- | Same as calc, except tagged as Theorem
  calcThm :: Proposition a => String -> a -> steps -> KD Proof

  -- | Prove a property via a series of equality steps, using the given solver.
  calcWith :: Proposition a => SMTConfig -> String -> a -> steps -> KD Proof

  -- | Same as calcWith, except tagged as Theorem
  calcThmWith :: Proposition a => SMTConfig -> String -> a -> steps -> KD Proof

  -- | Internal, shouldn't be needed outside the library
  {-# MINIMAL calcSteps #-}
  calcSteps :: a -> steps -> Symbolic (SBool, CalcStrategy)

  calc            nm p steps = getKDConfig >>= \cfg  -> calcWith          cfg                   nm p steps
  calcThm         nm p steps = getKDConfig >>= \cfg  -> calcThmWith       cfg                   nm p steps
  calcWith    cfg nm p steps = getKDConfig >>= \cfg' -> calcGeneric False (kdMergeCfg cfg cfg') nm p steps
  calcThmWith cfg nm p steps = getKDConfig >>= \cfg' -> calcGeneric True  (kdMergeCfg cfg cfg') nm p steps

  calcGeneric :: Proposition a => Bool -> SMTConfig -> String -> a -> steps -> KD Proof
  calcGeneric tagTheorem cfg nm result steps = do
     kdSt <- getKDState

     liftIO $ runSMTWith cfg $ do

        qSaturateSavingObservables result -- make sure we saturate the result, i.e., get all it's UI's, types etc. pop out

        message cfg $ (if tagTheorem then "Theorem" else "Lemma") ++ ": " ++ nm ++ "\n"

        (calcGoal, strategy@CalcStrategy {calcIntros, calcProofTree}) <- calcSteps result steps

        -- Collect all subterms and saturate them
        mapM_ qSaturateSavingObservables $ getCalcStrategySaturatables strategy

        query $ proveProofTree cfg kdSt nm (result, calcGoal) calcIntros calcProofTree

-- | Prove the proof tree. The players here are:
--
--      result    : The ultimate goal we want to prove. Note that this is a general proposition, and we don't actually prove it. See the next param.
--      resultBool: The instance of result that, if we prove it, establishes the result itself
--      intros    : Hypotheses (conjuncted)
--      proofTree : A tree of steps, which give rise to a bunch of equalities
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
               -> KDState
               -> String        -- ^ the name of the top result
               -> (a, SBool)    -- ^ goal: as a proposition and as a boolean
               -> SBool         -- ^ hypotheses
               -> KDProof       -- ^ proof tree
               -> Query Proof
proveProofTree cfg kdSt nm (result, resultBool) initialHypotheses calcProofTree = do

  let SMTConfig{kdOptions = KDOptions{measureTime}} = cfg
  mbStartTime <- getTimeStampIf measureTime

  let next :: [Int] -> [Int]
      next bs = case reverse bs of
                  i : rs -> reverse $ i + 1 : rs
                  []     -> [1]

      walk :: SBool -> Int -> ([Int], KDProof) -> Query [SBool]

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
         =  do -- If this is the only step, then mark it as such. At the top-level, the noise isn't necessary.
               case reverse bn of
                 1 : _ -> liftIO $ do tab <- startKD cfg False "Step" level (KDProofStep False nm (map show bn))
                                      finishKD cfg "Q.E.D." (tab, Nothing) []
                 _     -> pure ()

               pure [initialHypotheses .&& intros .=> calcResult]

      -- Do the branches separately and collect the results. If there's coverage needed, we do it too; which
      -- is essentially the assumption here.
      walk intros level (bn, ProofBranch checkCompleteness () ps) = do

        let addSuffix xs s = case reverse xs of
                                l : p -> reverse $ (l ++ s) : p
                                []    -> [s]

        _ <- io $ startKD cfg True "Step" level (KDProofStep False nm (addSuffix (map show bn) (" (" ++ show (length ps) ++ " way case split)")))

        let deepen cur i p
              | isMultiStep p = cur ++ [i, 1]
              | True          = cur ++ [i]

            isMultiStep (ProofStep _ _ (ProofStep{})) = True
            isMultiStep _                             = False

        results <- concat <$> sequence [walk (intros .&& branchCond) (level + 1) (deepen bn i p, p) | (i, (branchCond, p)) <- zip [1..] ps]

        when checkCompleteness $ smtProofStep cfg kdSt "Step" (level+1)
                                                       (KDProofStep False nm (map show bn ++ ["Completeness"]))
                                                       (Just (initialHypotheses .&& intros))
                                                       (sOr (map fst ps))
                                                       (\d -> finishKD cfg "Q.E.D." d [])
        pure results

      -- Do a proof step
      walk intros level (bn, ProofStep cur hs p) = do

           let finish et helpers d = finishKD cfg ("Q.E.D." ++ modulo) d et
                  where (_, modulo) = calculateRootOfTrust nm helpers

               stepName = map show bn

           -- First prove the assumptions, if there are any. We stay quiet, unless timing is asked for
           let (quietCfg, finalizer)
                 | measureTime = (cfg,                                              finish [] [])
                 | True        = (cfg{kdOptions = (kdOptions cfg) { quiet = True}}, const (pure ()))

               as = concatMap getHelperAssumes hs
           case as of
             [] -> pure ()
             _  -> smtProofStep quietCfg kdSt "Asms" level
                                         (KDProofStep True nm stepName)
                                         (Just (initialHypotheses .&& intros))
                                         (sAnd as)
                                         finalizer

           -- Now prove the step
           let by = concatMap getHelperProofs hs
           smtProofStep cfg kdSt "Step" level
                                 (KDProofStep False nm stepName)
                                 (Just (sAnd (intros : as ++ map getProof by)))
                                 cur
                                 (finish [] by)

           -- Move to next
           walk intros level (next bn, p)

  results <- walk sTrue 1 ([1], calcProofTree)

  queryDebug [nm ++ ": Proof end: proving the result:"]

  smtProofStep cfg kdSt "Result" 1
               (KDProofStep False nm [""])
               (Just (initialHypotheses .=> sAnd results))
               resultBool $ \d ->
                 do mbElapsed <- getElapsedTime mbStartTime
                    let (ros, modulo) = calculateRootOfTrust nm (concatMap getHelperProofs (getAllHelpers calcProofTree))
                    finishKD cfg ("Q.E.D." ++ modulo) d (catMaybes [mbElapsed])

                    pure Proof { rootOfTrust = ros
                               , isUserAxiom = False
                               , getProof    = label nm (quantifiedBool result)
                               , getProp     = toDyn result
                               , proofName   = nm
                               }

-- Helper data-type for calc-step below
data CalcContext a = CalcStart     [Helper] -- Haven't started yet
                   | CalcStep  a a [Helper] -- Intermediate step: first value, prev value

-- | Turn a sequence of steps into a chain of equalities
mkCalcSteps :: EqSymbolic a => (SBool, KDProofRaw a) -> CalcStrategy
mkCalcSteps (intros, kdp) = CalcStrategy { calcIntros    = intros
                                         , calcProofTree = go (CalcStart []) kdp
                                         }
  where go :: EqSymbolic a => CalcContext a -> KDProofRaw a -> KDProof

        -- End of the proof; tie the begin and end
        go step (ProofEnd () hs) = case step of
                                     -- It's tempting to error out if we're at the start and already reached the end
                                     -- This means we're given a sequence of no-steps. While this is useless in the
                                     -- general case, it's quite valid in a case-split; where one of the case-splits
                                     -- might be easy enough for the solver to deduce so the user simply says "just derive it for me."
                                     CalcStart hs'          -> ProofEnd sTrue           (hs' ++ hs) -- Nothing proven!
                                     CalcStep begin end hs' -> ProofEnd (begin .== end) (hs' ++ hs)

        -- Branch: Just push it down. We use the hints from previous step, and pass the current ones down.
        go step (ProofBranch c hs ps) = ProofBranch c () [(branchCond, go step' p) | (branchCond, p) <- ps]
           where step' = case step of
                           CalcStart hs'     -> CalcStart (hs' ++ hs)
                           CalcStep  a b hs' -> CalcStep a b (hs' ++ hs)

        -- Step:
        go (CalcStart hs)           (ProofStep cur hs' p) =                               go (CalcStep cur   cur (hs' ++ hs)) p
        go (CalcStep first prev hs) (ProofStep cur hs' p) = ProofStep (prev  .== cur) hs (go (CalcStep first cur hs')         p)

-- | Chaining lemmas that depend on no extra variables
instance EqSymbolic z => CalcLemma SBool (SBool, KDProofRaw z) where
   calcSteps result steps = pure (result, mkCalcSteps steps)

-- | Chaining lemmas that depend on a single extra variable.
instance (KnownSymbol na, SymVal a, EqSymbolic z) => CalcLemma (Forall na a -> SBool) (SBV a -> (SBool, KDProofRaw z)) where
   calcSteps result steps = do a <- free (symbolVal (Proxy @na))
                               pure (result (Forall a), mkCalcSteps (steps a))

-- | Chaining lemmas that depend on two extra variables.
instance (KnownSymbol na, SymVal a, KnownSymbol nb, SymVal b, EqSymbolic z)
      => CalcLemma (Forall na a -> Forall nb b -> SBool)
                   (SBV a -> SBV b -> (SBool, KDProofRaw z)) where
   calcSteps result steps = do (a, b) <- (,) <$> free (symbolVal (Proxy @na)) <*> free (symbolVal (Proxy @nb))
                               pure (result (Forall a) (Forall b), mkCalcSteps (steps a b))

-- | Chaining lemmas that depend on three extra variables.
instance (KnownSymbol na, SymVal a, KnownSymbol nb, SymVal b, KnownSymbol nc, SymVal c, EqSymbolic z)
      => CalcLemma (Forall na a -> Forall nb b -> Forall nc c -> SBool)
                   (SBV a -> SBV b -> SBV c -> (SBool, KDProofRaw z)) where
   calcSteps result steps = do (a, b, c) <- (,,) <$> free (symbolVal (Proxy @na)) <*> free (symbolVal (Proxy @nb)) <*> free (symbolVal (Proxy @nc))
                               pure (result (Forall a) (Forall b) (Forall c), mkCalcSteps (steps a b c))

-- | Chaining lemmas that depend on four extra variables.
instance (KnownSymbol na, SymVal a, KnownSymbol nb, SymVal b, KnownSymbol nc, SymVal c, KnownSymbol nd, SymVal d, EqSymbolic z)
      => CalcLemma (Forall na a -> Forall nb b -> Forall nc c -> Forall nd d -> SBool)
                   (SBV a -> SBV b -> SBV c -> SBV d -> (SBool, KDProofRaw z)) where
   calcSteps result steps = do (a, b, c, d) <- (,,,) <$> free (symbolVal (Proxy @na)) <*> free (symbolVal (Proxy @nb)) <*> free (symbolVal (Proxy @nc)) <*> free (symbolVal (Proxy @nd))
                               pure (result (Forall a) (Forall b) (Forall c) (Forall d), mkCalcSteps (steps a b c d))

-- | Chaining lemmas that depend on five extra variables.
instance (KnownSymbol na, SymVal a, KnownSymbol nb, SymVal b, KnownSymbol nc, SymVal c, KnownSymbol nd, SymVal d, KnownSymbol ne, SymVal e, EqSymbolic z)
      => CalcLemma (Forall na a -> Forall nb b -> Forall nc c -> Forall nd d -> Forall ne e -> SBool)
                   (SBV a -> SBV b -> SBV c -> SBV d -> SBV e -> (SBool, KDProofRaw z)) where
   calcSteps result steps = do (a, b, c, d, e) <- (,,,,) <$> free (symbolVal (Proxy @na)) <*> free (symbolVal (Proxy @nb)) <*> free (symbolVal (Proxy @nc)) <*> free (symbolVal (Proxy @nd)) <*> free (symbolVal (Proxy @ne))
                               pure (result (Forall a) (Forall b) (Forall c) (Forall d) (Forall e), mkCalcSteps (steps a b c d e))

-- | Captures the schema for an inductive proof. Base case might be nothing, to cover strong induction.
data InductionStrategy = InductionStrategy { inductionIntros    :: SBool
                                           , inductionBaseCase  :: Maybe SBool
                                           , inductionProofTree :: KDProof
                                           , inductiveStep      :: SBool
                                           }

-- | Are we doing strong induction or regular induction?
data InductionStyle = RegularInduction | StrongInduction

getInductionStrategySaturatables :: InductionStrategy -> [SBool]
getInductionStrategySaturatables (InductionStrategy inductionIntros
                                                    inductionBaseCase
                                                    inductionProofSteps
                                                    inductiveStep)
  = inductionIntros : inductiveStep : proofTreeSaturatables inductionProofSteps ++ maybeToList inductionBaseCase

-- | A class for doing regular inductive proofs.
class Inductive a steps where
   -- | Inductively prove a lemma, using the default config.
   -- Inductive proofs over lists only hold for finite lists. We also assume that all functions involved are terminating. SBV does not prove termination, so only
   -- partial correctness is guaranteed if non-terminating functions are involved.
   induct  :: Proposition a => String -> a -> (Proof -> steps) -> KD Proof

   -- | Inductively prove a theorem. Same as 'induct', but tagged as a theorem, using the default config.
   -- Inductive proofs over lists only hold for finite lists. We also assume that all functions involved are terminating. SBV does not prove termination, so only
   -- partial correctness is guaranteed if non-terminating functions are involved.
   inductThm :: Proposition a => String -> a -> (Proof -> steps) -> KD Proof

   -- | Same as 'induct', but with the given solver configuration.
   -- Inductive proofs over lists only hold for finite lists. We also assume that all functions involved are terminating. SBV does not prove termination, so only
   -- partial correctness is guaranteed if non-terminating functions are involved.
   inductWith :: Proposition a => SMTConfig -> String -> a -> (Proof -> steps) -> KD Proof

   -- | Same as 'inductThm', but with the given solver configuration.
   -- Inductive proofs over lists only hold for finite lists. We also assume that all functions involved are terminating. SBV does not prove termination, so only
   -- partial correctness is guaranteed if non-terminating functions are involved.
   inductThmWith :: Proposition a => SMTConfig -> String -> a -> (Proof -> steps) -> KD Proof

   induct            nm p steps = getKDConfig >>= \cfg  -> inductWith                             cfg                   nm p steps
   inductThm         nm p steps = getKDConfig >>= \cfg  -> inductThmWith                          cfg                   nm p steps
   inductWith    cfg nm p steps = getKDConfig >>= \cfg' -> inductionEngine RegularInduction False (kdMergeCfg cfg cfg') nm p (inductionStrategy p steps)
   inductThmWith cfg nm p steps = getKDConfig >>= \cfg' -> inductionEngine RegularInduction True  (kdMergeCfg cfg cfg') nm p (inductionStrategy p steps)

   -- | Internal, shouldn't be needed outside the library
   {-# MINIMAL inductionStrategy #-}
   inductionStrategy :: Proposition a => a -> (Proof -> steps) -> Symbolic InductionStrategy

-- | A class for doing strong inductive proofs.
class SInductive a steps where
   -- | Inductively prove a lemma, using strong induction, using the default config.
   -- Inductive proofs over lists only hold for finite lists. We also assume that all functions involved are terminating. SBV does not prove termination, so only
   -- partial correctness is guaranteed if non-terminating functions are involved.
   sInduct :: Proposition a => String -> a -> (Proof -> steps) -> KD Proof

   -- | Inductively prove a theorem, using strong induction. Same as 'sInduct', but tagged as a theorem, using the default config.
   -- Inductive proofs over lists only hold for finite lists. We also assume that all functions involved are terminating. SBV does not prove termination, so only
   -- partial correctness is guaranteed if non-terminating functions are involved.
   sInductThm :: Proposition a => String -> a -> (Proof -> steps) -> KD Proof

   -- | Same as 'sInduct', but with the given solver configuration.
   -- Inductive proofs over lists only hold for finite lists. We also assume that all functions involved are terminating. SBV does not prove termination, so only
   -- partial correctness is guaranteed if non-terminating functions are involved.
   sInductWith :: Proposition a => SMTConfig -> String -> a -> (Proof -> steps) -> KD Proof

   -- | Same as 'sInductThm', but with the given solver configuration.
   -- Inductive proofs over lists only hold for finite lists. We also assume that all functions involved are terminating. SBV does not prove termination, so only
   -- partial correctness is guaranteed if non-terminating functions are involved.
   sInductThmWith :: Proposition a => SMTConfig -> String -> a -> (Proof -> steps) -> KD Proof

   sInduct            nm p steps = getKDConfig >>= \cfg  -> sInductWith                          cfg                   nm p steps
   sInductThm         nm p steps = getKDConfig >>= \cfg  -> sInductThmWith                       cfg                   nm p steps
   sInductWith    cfg nm p steps = getKDConfig >>= \cfg' -> inductionEngine StrongInduction False (kdMergeCfg cfg cfg') nm p (sInductionStrategy p steps)
   sInductThmWith cfg nm p steps = getKDConfig >>= \cfg' -> inductionEngine StrongInduction True  (kdMergeCfg cfg cfg') nm p (sInductionStrategy p steps)

   -- | Internal, shouldn't be needed outside the library
   {-# MINIMAL sInductionStrategy #-}
   sInductionStrategy :: Proposition a => a -> (Proof -> steps) -> Symbolic InductionStrategy

-- | Do an inductive proof, based on the given strategy
inductionEngine :: Proposition a => InductionStyle -> Bool -> SMTConfig -> String -> a -> Symbolic InductionStrategy -> KD Proof
inductionEngine style tagTheorem cfg nm result getStrategy = do
   kdSt <- getKDState

   liftIO $ runSMTWith cfg $ do

      qSaturateSavingObservables result -- make sure we saturate the result, i.e., get all it's UI's, types etc. pop out

      let strong = case style of
                     RegularInduction -> ""
                     StrongInduction  -> " (strong)"

      message cfg $ "Inductive " ++ (if tagTheorem then "theorem" else "lemma") ++ strong ++ ": " ++ nm ++ "\n"

      strategy@InductionStrategy { inductionIntros
                                 , inductionBaseCase
                                 , inductionProofTree
                                 , inductiveStep
                                 } <- getStrategy

      mapM_ qSaturateSavingObservables $ getInductionStrategySaturatables strategy

      query $ do

       case inductionBaseCase of
          Nothing -> queryDebug [nm ++ ": Induction" ++ strong ++ ", there is no proving base case:"]
          Just bc -> do queryDebug [nm ++ ": Induction, proving base case:"]
                        smtProofStep cfg kdSt "Step" 1
                                              (KDProofStep False nm ["Base"])
                                              (Just inductionIntros)
                                              bc
                                              (\d -> finishKD cfg "Q.E.D." d [])

       proveProofTree cfg kdSt nm (result, inductiveStep) inductionIntros inductionProofTree

-- Induction strategy helper
mkIndStrategy :: EqSymbolic a => Maybe SBool -> Maybe SBool -> (SBool, KDProofRaw a) -> SBool -> InductionStrategy
mkIndStrategy mbExtraConstraint mbBaseCase indSteps step =
        let CalcStrategy { calcIntros, calcProofTree } = mkCalcSteps indSteps
        in InductionStrategy { inductionIntros    = maybe id (.&&) mbExtraConstraint calcIntros
                             , inductionBaseCase  = mbBaseCase
                             , inductionProofTree = calcProofTree
                             , inductiveStep      = step
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
instance (KnownSymbol nn, EqSymbolic z) => Inductive (Forall nn Integer -> SBool) (SInteger -> (SBool, KDProofRaw z)) where
  inductionStrategy result steps = do
       (n, nn) <- mkVar (Proxy @nn)
       pure $ mkIndStrategy (Just (n .>= 0)) (Just (result (Forall 0)))
                            (steps (internalAxiom "IH" (result (Forall n))) n)
                            (indResult [nn ++ "+1"] (result (Forall (n+1))))

-- | Strong induction over 'SInteger'
instance (KnownSymbol nn, EqSymbolic z) => SInductive (Forall nn Integer -> SBool) (SInteger -> (SBool, KDProofRaw z)) where
  sInductionStrategy result steps = do
       (n, nn) <- mkVar (Proxy @nn)
       pure $ mkIndStrategy (Just (n .>= 0)) Nothing
                            (steps (internalAxiom "IH" (\(Forall n' :: Forall nn Integer) -> 0 .<= n' .&& n' .< n .=> result (Forall n'))) n)
                            (indResult [nn] (result (Forall n)))

-- | Induction over 'SInteger', taking an extra argument
instance (KnownSymbol nn, KnownSymbol na, SymVal a, EqSymbolic z) => Inductive (Forall nn Integer -> Forall na a -> SBool) (SInteger -> SBV a -> (SBool, KDProofRaw z)) where
  inductionStrategy result steps = do
       (n, nn) <- mkVar (Proxy @nn)
       (a, na) <- mkVar (Proxy @na)
       pure $ mkIndStrategy (Just (n .>= 0)) (Just (result (Forall 0) (Forall a)))
                            (steps (internalAxiom "IH" (\(Forall a' :: Forall na a) -> result (Forall n) (Forall a'))) n a)
                            (indResult [nn ++ "+1", na] (result (Forall (n+1)) (Forall a)))

-- | Strong induction over 'SInteger', taking an extra argument
instance (KnownSymbol nn, KnownSymbol na, SymVal a, EqSymbolic z) => SInductive (Forall nn Integer -> Forall na a -> SBool) (SInteger -> SBV a -> (SBool, KDProofRaw z)) where
  sInductionStrategy result steps = do
       (n, nn) <- mkVar (Proxy @nn)
       (a, na) <- mkVar (Proxy @na)
       pure $ mkIndStrategy (Just (n .>= 0)) Nothing
                            (steps (internalAxiom "IH" (\(Forall n' :: Forall nn Integer) (Forall a' :: Forall na a) -> 0 .<= n' .&& n' .< n .=> result (Forall n') (Forall a'))) n a)
                            (indResult [nn, na] (result (Forall n) (Forall a)))

-- | Induction over 'SInteger', taking two extra arguments
instance (KnownSymbol nn, KnownSymbol na, SymVal a, KnownSymbol nb, SymVal b, EqSymbolic z) => Inductive (Forall nn Integer -> Forall na a -> Forall nb b -> SBool) (SInteger -> SBV a -> SBV b -> (SBool, KDProofRaw z)) where
  inductionStrategy result steps = do
       (n, nn) <- mkVar (Proxy @nn)
       (a, na) <- mkVar (Proxy @na)
       (b, nb) <- mkVar (Proxy @nb)
       pure $ mkIndStrategy (Just (n .>= 0)) (Just (result (Forall 0) (Forall a) (Forall b)))
                            (steps (internalAxiom "IH" (\(Forall a' :: Forall na a) (Forall b' :: Forall nb b) -> result (Forall n) (Forall a') (Forall b'))) n a b)
                            (indResult [nn ++ "+1", na, nb] (result (Forall (n+1)) (Forall a) (Forall b)))

-- | Strong induction over 'SInteger', taking two extra arguments
instance (KnownSymbol nn, KnownSymbol na, SymVal a, KnownSymbol nb, SymVal b, EqSymbolic z) => SInductive (Forall nn Integer -> Forall na a -> Forall nb b -> SBool) (SInteger -> SBV a -> SBV b -> (SBool, KDProofRaw z)) where
  sInductionStrategy result steps = do
       (n, nn) <- mkVar (Proxy @nn)
       (a, na) <- mkVar (Proxy @na)
       (b, nb) <- mkVar (Proxy @nb)
       pure $ mkIndStrategy (Just (n .>= 0)) Nothing
                            (steps (internalAxiom "IH" (\(Forall n' :: Forall nn Integer) (Forall a' :: Forall na a) (Forall b' :: Forall nb b) -> 0 .<= n' .&& n' .< n .=> result (Forall n') (Forall a') (Forall b'))) n a b)
                            (indResult [nn, na, nb] (result (Forall n) (Forall a) (Forall b)))

-- | Induction over 'SInteger', taking three extra arguments
instance (KnownSymbol nn, KnownSymbol na, SymVal a, KnownSymbol nb, SymVal b, KnownSymbol nc, SymVal c, EqSymbolic z) => Inductive (Forall nn Integer -> Forall na a -> Forall nb b -> Forall nc c -> SBool) (SInteger -> SBV a -> SBV b -> SBV c -> (SBool, KDProofRaw z)) where
  inductionStrategy result steps = do
       (n, nn) <- mkVar (Proxy @nn)
       (a, na) <- mkVar (Proxy @na)
       (b, nb) <- mkVar (Proxy @nb)
       (c, nc) <- mkVar (Proxy @nc)
       pure $ mkIndStrategy (Just (n .>= 0)) (Just (result (Forall 0) (Forall a) (Forall b) (Forall c)))
                            (steps (internalAxiom "IH" (\(Forall a' :: Forall na a) (Forall b' :: Forall nb b) (Forall c' :: Forall nc c) -> result (Forall n) (Forall a') (Forall b') (Forall c'))) n a b c)
                            (indResult [nn ++ "+1", na, nb, nc] (result (Forall (n+1)) (Forall a) (Forall b) (Forall c)))

-- | Strong induction over 'SInteger', taking three extra arguments
instance (KnownSymbol nn, KnownSymbol na, SymVal a, KnownSymbol nb, SymVal b, KnownSymbol nc, SymVal c, EqSymbolic z) => SInductive (Forall nn Integer -> Forall na a -> Forall nb b -> Forall nc c -> SBool) (SInteger -> SBV a -> SBV b -> SBV c -> (SBool, KDProofRaw z)) where
  sInductionStrategy result steps = do
       (n, nn) <- mkVar (Proxy @nn)
       (a, na) <- mkVar (Proxy @na)
       (b, nb) <- mkVar (Proxy @nb)
       (c, nc) <- mkVar (Proxy @nc)
       pure $ mkIndStrategy (Just (n .>= 0)) Nothing
                            (steps (internalAxiom "IH" (\(Forall n' :: Forall nn Integer) (Forall a' :: Forall na a) (Forall b' :: Forall nb b) (Forall c' :: Forall nc c) -> 0 .<= n' .&& n' .< n .=> result (Forall n') (Forall a') (Forall b') (Forall c'))) n a b c)
                            (indResult [nn, na, nb, nc] (result (Forall n) (Forall a) (Forall b) (Forall c)))

-- | Induction over 'SInteger', taking four extra arguments
instance (KnownSymbol nn, KnownSymbol na, SymVal a, KnownSymbol nb, SymVal b, KnownSymbol nc, SymVal c, KnownSymbol nd, SymVal d, EqSymbolic z) => Inductive (Forall nn Integer -> Forall na a -> Forall nb b -> Forall nc c -> Forall nd d -> SBool) (SInteger -> SBV a -> SBV b -> SBV c -> SBV d -> (SBool, KDProofRaw z)) where
  inductionStrategy result steps = do
       (n, nn) <- mkVar (Proxy @nn)
       (a, na) <- mkVar (Proxy @na)
       (b, nb) <- mkVar (Proxy @nb)
       (c, nc) <- mkVar (Proxy @nc)
       (d, nd) <- mkVar (Proxy @nd)
       pure $ mkIndStrategy (Just (n .>= 0)) (Just (result (Forall 0) (Forall a) (Forall b) (Forall c) (Forall d)))
                            (steps (internalAxiom "IH" (\(Forall a' :: Forall na a) (Forall b' :: Forall nb b) (Forall c' :: Forall nc c) (Forall d' :: Forall nd d) -> result (Forall n) (Forall a') (Forall b') (Forall c') (Forall d'))) n a b c d)
                            (indResult [nn ++ "+1", na, nb, nc, nd] (result (Forall (n+1)) (Forall a) (Forall b) (Forall c) (Forall d)))

-- | Strong induction over 'SInteger', taking four extra arguments
instance (KnownSymbol nn, KnownSymbol na, SymVal a, KnownSymbol nb, SymVal b, KnownSymbol nc, SymVal c, KnownSymbol nd, SymVal d, EqSymbolic z) => SInductive (Forall nn Integer -> Forall na a -> Forall nb b -> Forall nc c -> Forall nd d -> SBool) (SInteger -> SBV a -> SBV b -> SBV c -> SBV d -> (SBool, KDProofRaw z)) where
  sInductionStrategy result steps = do
       (n, nn) <- mkVar (Proxy @nn)
       (a, na) <- mkVar (Proxy @na)
       (b, nb) <- mkVar (Proxy @nb)
       (c, nc) <- mkVar (Proxy @nc)
       (d, nd) <- mkVar (Proxy @nd)
       pure $ mkIndStrategy (Just (n .>= 0)) Nothing
                            (steps (internalAxiom "IH" (\(Forall n' :: Forall nn Integer) (Forall a' :: Forall na a) (Forall b' :: Forall nb b) (Forall c' :: Forall nc c) (Forall d' :: Forall nd d) -> 0 .<= n' .&& n' .< n .=> result (Forall n') (Forall a') (Forall b') (Forall c') (Forall d'))) n a b c d)
                            (indResult [nn, na, nb, nc, nd] (result (Forall n) (Forall a) (Forall b) (Forall c) (Forall d)))

-- | Induction over 'SInteger', taking five extra arguments
instance (KnownSymbol nn, KnownSymbol na, SymVal a, KnownSymbol nb, SymVal b, KnownSymbol nc, SymVal c, KnownSymbol nd, SymVal d, KnownSymbol ne, SymVal e, EqSymbolic z) => Inductive (Forall nn Integer -> Forall na a -> Forall nb b -> Forall nc c -> Forall nd d -> Forall ne e -> SBool) (SInteger -> SBV a -> SBV b -> SBV c -> SBV d -> SBV e -> (SBool, KDProofRaw z)) where
  inductionStrategy result steps = do
       (n, nn) <- mkVar (Proxy @nn)
       (a, na) <- mkVar (Proxy @na)
       (b, nb) <- mkVar (Proxy @nb)
       (c, nc) <- mkVar (Proxy @nc)
       (d, nd) <- mkVar (Proxy @nd)
       (e, ne) <- mkVar (Proxy @ne)
       pure $ mkIndStrategy (Just (n .>= 0)) (Just (result (Forall 0) (Forall a) (Forall b) (Forall c) (Forall d) (Forall e)))
                            (steps (internalAxiom "IH" (\(Forall a' :: Forall na a) (Forall b' :: Forall nb b) (Forall c' :: Forall nc c) (Forall d' :: Forall nd d) (Forall e' :: Forall ne e) -> result (Forall n) (Forall a') (Forall b') (Forall c') (Forall d') (Forall e'))) n a b c d e)
                            (indResult [nn ++ "+1", na, nb, nc, nd, ne] (result (Forall (n+1)) (Forall a) (Forall b) (Forall c) (Forall d) (Forall e)))

-- | Strong induction over 'SInteger', taking five extra arguments
instance (KnownSymbol nn, KnownSymbol na, SymVal a, KnownSymbol nb, SymVal b, KnownSymbol nc, SymVal c, KnownSymbol nd, SymVal d, KnownSymbol ne, SymVal e, EqSymbolic z) => SInductive (Forall nn Integer -> Forall na a -> Forall nb b -> Forall nc c -> Forall nd d -> Forall ne e -> SBool) (SInteger -> SBV a -> SBV b -> SBV c -> SBV d -> SBV e -> (SBool, KDProofRaw z)) where
  sInductionStrategy result steps = do
       (n, nn) <- mkVar (Proxy @nn)
       (a, na) <- mkVar (Proxy @na)
       (b, nb) <- mkVar (Proxy @nb)
       (c, nc) <- mkVar (Proxy @nc)
       (d, nd) <- mkVar (Proxy @nd)
       (e, ne) <- mkVar (Proxy @ne)
       pure $ mkIndStrategy (Just (n .>= 0)) Nothing
                            (steps (internalAxiom "IH" (\(Forall n' :: Forall nn Integer) (Forall a' :: Forall na a) (Forall b' :: Forall nb b) (Forall c' :: Forall nc c) (Forall d' :: Forall nd d) (Forall e' :: Forall ne e) -> 0 .<= n' .&& n' .< n .=> result (Forall n') (Forall a') (Forall b') (Forall c') (Forall d') (Forall e'))) n a b c d e)
                            (indResult [nn, na, nb, nc, nd, ne] (result (Forall n) (Forall a) (Forall b) (Forall c) (Forall d) (Forall e)))

-- Given a user name for the list, get a name for the element, in the most suggestive way possible
--   xs  -> x
--   xss -> xs
--   foo -> fooElt
singular :: String -> String
singular n = case reverse n of
               's':_:_ -> init n
               _       -> n ++ "Elt"

-- | Metric for induction over lists. Currently we simply require the list we're assuming correctness for is shorter in length, which
-- is a measure that is guarenteed >= 0. Later on, we might want to generalize this to a user given measure.
lexLeq :: SymVal a => SList a -> SList a -> SBool
lexLeq xs ys = SL.length xs .< SL.length ys

-- | Induction over 'SList'
instance (KnownSymbol nxs, SymVal x, EqSymbolic z) => Inductive (Forall nxs [x] -> SBool) (SBV x -> SList x -> (SBool, KDProofRaw z)) where
  inductionStrategy result steps = do
       (x, xs, nxxs) <- mkLVar (Proxy @nxs)
       pure $ mkIndStrategy Nothing (Just (result (Forall SL.nil)))
                            (steps (internalAxiom "IH" (result (Forall xs))) x xs)
                            (indResult [nxxs] (result (Forall (x SL..: xs))))

-- | Strong induction over 'SList'
instance (KnownSymbol nxs, SymVal x, EqSymbolic z) => SInductive (Forall nxs [x] -> SBool) (SList x -> (SBool, KDProofRaw z)) where
  sInductionStrategy result steps = do
       (xs, nxs) <- mkVar (Proxy @nxs)
       pure $ mkIndStrategy Nothing Nothing
                            (steps (internalAxiom "IH" (\(Forall xs' :: Forall nxs [x]) -> xs' `lexLeq` xs .=> result (Forall xs'))) xs)
                            (indResult [nxs] (result (Forall xs)))

-- | Induction over 'SList', taking an extra argument
instance (KnownSymbol nxs, SymVal x, KnownSymbol na, SymVal a, EqSymbolic z) => Inductive (Forall nxs [x] -> Forall na a -> SBool) (SBV x -> SList x -> SBV a -> (SBool, KDProofRaw z)) where
  inductionStrategy result steps = do
       (x, xs, nxxs) <- mkLVar (Proxy @nxs)
       (a, na)       <- mkVar  (Proxy @na)
       pure $ mkIndStrategy Nothing (Just (result (Forall SL.nil) (Forall a)))
                            (steps (internalAxiom "IH" (\(Forall a' :: Forall na a) -> result (Forall xs) (Forall a'))) x xs a)
                            (indResult [nxxs, na] (result (Forall (x SL..: xs)) (Forall a)))

-- | Strong induction over 'SList', taking an extra argument
instance (KnownSymbol nxs, SymVal x, KnownSymbol na, SymVal a, EqSymbolic z) => SInductive (Forall nxs [x] -> Forall na a -> SBool) (SList x -> SBV a -> (SBool, KDProofRaw z)) where
  sInductionStrategy result steps = do
       (xs, nxs) <- mkVar (Proxy @nxs)
       (a,  na)  <- mkVar (Proxy @na)
       pure $ mkIndStrategy Nothing Nothing
                            (steps (internalAxiom "IH" (\(Forall xs' :: Forall nxs [x]) (Forall a' :: Forall na a) -> xs' `lexLeq` xs .=> result (Forall xs') (Forall a'))) xs a)
                            (indResult [nxs, na] (result (Forall xs) (Forall a)))

-- | Induction over 'SList', taking two extra arguments
instance (KnownSymbol nxs, SymVal x, KnownSymbol na, SymVal a, KnownSymbol nb, SymVal b, EqSymbolic z) => Inductive (Forall nxs [x] -> Forall na a -> Forall nb b -> SBool) (SBV x -> SList x -> SBV a -> SBV b -> (SBool, KDProofRaw z)) where
  inductionStrategy result steps = do
       (x, xs, nxxs) <- mkLVar (Proxy @nxs)
       (a, na)       <- mkVar  (Proxy @na)
       (b, nb)       <- mkVar  (Proxy @nb)
       pure $ mkIndStrategy Nothing (Just (result (Forall SL.nil) (Forall a) (Forall b)))
                            (steps (internalAxiom "IH" (\(Forall a' :: Forall na a) (Forall b' :: Forall nb b) -> result (Forall xs) (Forall a') (Forall b'))) x xs a b)
                            (indResult [nxxs, na, nb] (result (Forall (x SL..: xs)) (Forall a) (Forall b)))

-- | Strong induction over 'SList', taking two extra arguments
instance (KnownSymbol nxs, SymVal x, KnownSymbol na, SymVal a, KnownSymbol nb, SymVal b, EqSymbolic z) => SInductive (Forall nxs [x] -> Forall na a -> Forall nb b -> SBool) (SList x -> SBV a -> SBV b -> (SBool, KDProofRaw z)) where
  sInductionStrategy result steps = do
       (xs, nxs) <- mkVar (Proxy @nxs)
       (a, na)   <- mkVar (Proxy @na)
       (b, nb)   <- mkVar (Proxy @nb)
       pure $ mkIndStrategy Nothing Nothing
                            (steps (internalAxiom "IH" (\(Forall xs' :: Forall nxs [x]) (Forall a' :: Forall na a) (Forall b' :: Forall nb b) -> xs' `lexLeq` xs .=> result (Forall xs') (Forall a') (Forall b'))) xs a b)
                            (indResult [nxs, na, nb] (result (Forall xs) (Forall a) (Forall b)))

-- | Induction over 'SList', taking three extra arguments
instance (KnownSymbol nxs, SymVal x, KnownSymbol na, SymVal a, KnownSymbol nb, SymVal b, KnownSymbol nc, SymVal c, EqSymbolic z) => Inductive (Forall nxs [x] -> Forall na a -> Forall nb b -> Forall nc c -> SBool) (SBV x -> SList x -> SBV a -> SBV b -> SBV c -> (SBool, KDProofRaw z)) where
  inductionStrategy result steps = do
       (x, xs, nxxs) <- mkLVar (Proxy @nxs)
       (a, na)       <- mkVar  (Proxy @na)
       (b, nb)       <- mkVar  (Proxy @nb)
       (c, nc)       <- mkVar  (Proxy @nc)
       pure $ mkIndStrategy Nothing (Just (result (Forall SL.nil) (Forall a) (Forall b) (Forall c)))
                            (steps (internalAxiom "IH" (\(Forall a' :: Forall na a) (Forall b' :: Forall nb b) (Forall c' :: Forall nc c) -> result (Forall xs) (Forall a') (Forall b') (Forall c'))) x xs a b c)
                            (indResult [nxxs, na, nb, nc] (result (Forall (x SL..: xs)) (Forall a) (Forall b) (Forall c)))

-- | Strong induction over 'SList', taking three extra arguments
instance (KnownSymbol nxs, SymVal x, KnownSymbol na, SymVal a, KnownSymbol nb, SymVal b, KnownSymbol nc, SymVal c, EqSymbolic z) => SInductive (Forall nxs [x] -> Forall na a -> Forall nb b -> Forall nc c -> SBool) (SList x -> SBV a -> SBV b -> SBV c -> (SBool, KDProofRaw z)) where
  sInductionStrategy result steps = do
       (xs, nxs) <- mkVar (Proxy @nxs)
       (a, na)   <- mkVar (Proxy @na)
       (b, nb)   <- mkVar (Proxy @nb)
       (c, nc)   <- mkVar (Proxy @nc)
       pure $ mkIndStrategy Nothing Nothing
                            (steps (internalAxiom "IH" (\(Forall xs' :: Forall nxs [x]) (Forall a' :: Forall na a) (Forall b' :: Forall nb b) (Forall c' :: Forall nc c) -> xs' `lexLeq` xs .=> result (Forall xs') (Forall a') (Forall b') (Forall c'))) xs a b c)
                            (indResult [nxs, na, nb, nc] (result (Forall xs) (Forall a) (Forall b) (Forall c)))

-- | Induction over 'SList', taking four extra arguments
instance (KnownSymbol nxs, SymVal x, KnownSymbol na, SymVal a, KnownSymbol nb, SymVal b, KnownSymbol nc, SymVal c, KnownSymbol nd, SymVal d, EqSymbolic z) => Inductive (Forall nxs [x] -> Forall na a -> Forall nb b -> Forall nc c -> Forall nd d -> SBool) (SBV x -> SList x -> SBV a -> SBV b -> SBV c -> SBV d -> (SBool, KDProofRaw z)) where
  inductionStrategy result steps = do
       (x, xs, nxxs) <- mkLVar (Proxy @nxs)
       (a, na)       <- mkVar  (Proxy @na)
       (b, nb)       <- mkVar  (Proxy @nb)
       (c, nc)       <- mkVar  (Proxy @nc)
       (d, nd)       <- mkVar  (Proxy @nd)
       pure $ mkIndStrategy Nothing (Just (result (Forall SL.nil) (Forall a) (Forall b) (Forall c) (Forall d)))
                            (steps (internalAxiom "IH" (\(Forall a' :: Forall na a) (Forall b' :: Forall nb b) (Forall c' :: Forall nc c) (Forall d' :: Forall nd d) -> result (Forall xs) (Forall a') (Forall b') (Forall c') (Forall d'))) x xs a b c d)
                            (indResult [nxxs, na, nb, nc, nd] (result (Forall (x SL..: xs)) (Forall a) (Forall b) (Forall c) (Forall d)))

-- | Strong induction over 'SList', taking four extra arguments
instance (KnownSymbol nxs, SymVal x, KnownSymbol na, SymVal a, KnownSymbol nb, SymVal b, KnownSymbol nc, SymVal c, KnownSymbol nd, SymVal d, EqSymbolic z) => SInductive (Forall nxs [x] -> Forall na a -> Forall nb b -> Forall nc c -> Forall nd d -> SBool) (SList x -> SBV a -> SBV b -> SBV c -> SBV d -> (SBool, KDProofRaw z)) where
  sInductionStrategy result steps = do
       (xs, nxs) <- mkVar (Proxy @nxs)
       (a, na)   <- mkVar (Proxy @na)
       (b, nb)   <- mkVar (Proxy @nb)
       (c, nc)   <- mkVar (Proxy @nc)
       (d, nd)   <- mkVar  (Proxy @nd)
       pure $ mkIndStrategy Nothing Nothing
                            (steps (internalAxiom "IH" (\(Forall xs' :: Forall nxs [x]) (Forall a' :: Forall na a) (Forall b' :: Forall nb b) (Forall c' :: Forall nc c) (Forall d' :: Forall nd d) -> xs' `lexLeq` xs .=> result (Forall xs') (Forall a') (Forall b') (Forall c') (Forall d'))) xs a b c d)
                            (indResult [nxs, na, nb, nc, nd] (result (Forall xs) (Forall a) (Forall b) (Forall c) (Forall d)))

-- | Induction over 'SList', taking five extra arguments
instance (KnownSymbol nxs, SymVal x, KnownSymbol na, SymVal a, KnownSymbol nb, SymVal b, KnownSymbol nc, SymVal c, KnownSymbol nd, SymVal d, KnownSymbol ne, SymVal e, EqSymbolic z) => Inductive (Forall nxs [x] -> Forall na a -> Forall nb b -> Forall nc c -> Forall nd d -> Forall ne e -> SBool) (SBV x -> SList x -> SBV a -> SBV b -> SBV c -> SBV d -> SBV e -> (SBool, KDProofRaw z)) where
  inductionStrategy result steps = do
       (x, xs, nxxs) <- mkLVar (Proxy @nxs)
       (a, na)       <- mkVar  (Proxy @na)
       (b, nb)       <- mkVar  (Proxy @nb)
       (c, nc)       <- mkVar  (Proxy @nc)
       (d, nd)       <- mkVar  (Proxy @nd)
       (e, ne)       <- mkVar  (Proxy @ne)
       pure $ mkIndStrategy Nothing (Just (result (Forall SL.nil) (Forall a) (Forall b) (Forall c) (Forall d) (Forall e)))
                            (steps (internalAxiom "IH" (\(Forall a' :: Forall na a) (Forall b' :: Forall nb b) (Forall c' :: Forall nc c) (Forall d' :: Forall nd d) (Forall e' :: Forall ne e) -> result (Forall xs) (Forall a') (Forall b') (Forall c') (Forall d') (Forall e'))) x xs a b c d e)
                            (indResult [nxxs, na, nb, nc, nd, ne] (result (Forall (x SL..: xs)) (Forall a) (Forall b) (Forall c) (Forall d) (Forall e)))

-- | Strong induction over 'SList', taking five extra arguments
instance (KnownSymbol nxs, SymVal x, KnownSymbol na, SymVal a, KnownSymbol nb, SymVal b, KnownSymbol nc, SymVal c, KnownSymbol nd, SymVal d, KnownSymbol ne, SymVal e, EqSymbolic z) => SInductive (Forall nxs [x] -> Forall na a -> Forall nb b -> Forall nc c -> Forall nd d -> Forall ne e -> SBool) (SList x -> SBV a -> SBV b -> SBV c -> SBV d -> SBV e -> (SBool, KDProofRaw z)) where
  sInductionStrategy result steps = do
       (xs, nxs) <- mkVar (Proxy @nxs)
       (a, na)   <- mkVar (Proxy @na)
       (b, nb)   <- mkVar (Proxy @nb)
       (c, nc)   <- mkVar (Proxy @nc)
       (d, nd)   <- mkVar (Proxy @nd)
       (e, ne)   <- mkVar (Proxy @ne)
       pure $ mkIndStrategy Nothing Nothing
                            (steps (internalAxiom "IH" (\(Forall xs' :: Forall nxs [x]) (Forall a' :: Forall na a) (Forall b' :: Forall nb b) (Forall c' :: Forall nc c) (Forall d' :: Forall nd d) (Forall e' :: Forall ne e) -> xs' `lexLeq` xs .=> result (Forall xs') (Forall a') (Forall b') (Forall c') (Forall d') (Forall e'))) xs a b c d e)
                            (indResult [nxs, na, nb, nc, nd, ne] (result (Forall xs) (Forall a) (Forall b) (Forall c) (Forall d) (Forall e)))

-- | Metric for induction over two lists. We use lexicographic ordering. 
lexLeq2 :: (SymVal a, SymVal b) => (SList a, SList b) -> (SList a, SList b) -> SBool
lexLeq2 (xs', ys') (xs, ys) =   lxs' .<  lxs        -- First one got smaller
                            .|| (    lxs' .== lxs   -- OR, the first one did not grow
                                 .&& lys' .<  lys   -- and the second went down
                                )
 where lxs' = SL.length xs'
       lys' = SL.length ys'
       lxs  = SL.length xs
       lys  = SL.length ys

-- | Induction over two 'SList', simultaneously
instance (KnownSymbol nxs, SymVal x, KnownSymbol nys, SymVal y, EqSymbolic z) => Inductive ((Forall nxs [x], Forall nys [y]) -> SBool) ((SBV x, SList x, SBV y, SList y) -> (SBool, KDProofRaw z)) where
  inductionStrategy result steps = do
       (x, xs, nxxs) <- mkLVar (Proxy @nxs)
       (y, ys, nyys) <- mkLVar (Proxy @nys)
       pure $ mkIndStrategy Nothing (Just (result (Forall SL.nil, Forall SL.nil) .&& result (Forall SL.nil, Forall (y SL..: ys)) .&& result (Forall (x SL..: xs), Forall SL.nil)))
                            (steps (internalAxiom "IH" (result (Forall xs, Forall ys))) (x, xs, y, ys))
                            (indResult [nxxs, nyys] (result (Forall (x SL..: xs), Forall (y SL..: ys))))

-- | Strong induction over two 'SList', simultaneously
instance (KnownSymbol nxs, SymVal x, KnownSymbol nys, SymVal y, EqSymbolic z) => SInductive ((Forall nxs [x], Forall nys [y]) -> SBool) ((SList x, SList y) -> (SBool, KDProofRaw z)) where
  sInductionStrategy result steps = do
       (xs, nxs) <- mkVar (Proxy @nxs)
       (ys, nys) <- mkVar (Proxy @nys)
       pure $ mkIndStrategy Nothing Nothing
                            (steps (internalAxiom "IH" (\(Forall xs' :: Forall nxs [x], Forall ys' :: Forall nys [y]) -> (xs', ys') `lexLeq2` (xs, ys) .=> result (Forall xs', Forall ys'))) (xs, ys))
                            (indResult [nxs, nys] (result (Forall xs, Forall ys)))

-- | Induction over two 'SList', simultaneously, taking an extra argument
instance (KnownSymbol nxs, SymVal x, KnownSymbol nys, SymVal y, KnownSymbol na, SymVal a, EqSymbolic z) => Inductive ((Forall nxs [x], Forall nys [y]) -> Forall na a -> SBool) ((SBV x, SList x, SBV y, SList y) -> SBV a -> (SBool, KDProofRaw z)) where
  inductionStrategy result steps = do
       (x, xs, nxxs) <- mkLVar (Proxy @nxs)
       (y, ys, nyys) <- mkLVar (Proxy @nys)
       (a, na)       <- mkVar  (Proxy @na)
       pure $ mkIndStrategy Nothing (Just (result (Forall SL.nil, Forall SL.nil) (Forall a) .&& result (Forall SL.nil, Forall (y SL..: ys)) (Forall a) .&& result (Forall (x SL..: xs), Forall SL.nil) (Forall a)))
                            (steps (internalAxiom "IH" (\(Forall a' :: Forall na a) -> result (Forall xs, Forall ys) (Forall a'))) (x, xs, y, ys) a)
                            (indResult [nxxs, nyys, na] (result (Forall (x SL..: xs), Forall (y SL..: ys)) (Forall a)))

-- | Strong induction over two 'SList', simultaneously, taking an extra argument
instance (KnownSymbol nxs, SymVal x, KnownSymbol nys, SymVal y, KnownSymbol na, SymVal a, EqSymbolic z) => SInductive ((Forall nxs [x], Forall nys [y]) -> Forall na a -> SBool) ((SList x, SList y) -> SBV a -> (SBool, KDProofRaw z)) where
  sInductionStrategy result steps = do
       (xs, nxs) <- mkVar (Proxy @nxs)
       (ys, nys) <- mkVar (Proxy @nys)
       (a, na)   <- mkVar  (Proxy @na)
       pure $ mkIndStrategy Nothing Nothing
                            (steps (internalAxiom "IH" (\(Forall xs' :: Forall nxs [x], Forall ys' :: Forall nys [y]) (Forall a' :: Forall na a) -> (xs', ys') `lexLeq2` (xs, ys) .=> result (Forall xs', Forall ys') (Forall a'))) (xs, ys) a)
                            (indResult [nxs, nys, na] (result (Forall xs, Forall ys) (Forall a)))

-- | Induction over two 'SList', simultaneously, taking two extra arguments
instance (KnownSymbol nxs, SymVal x, KnownSymbol nys, SymVal y, KnownSymbol na, SymVal a, KnownSymbol nb, SymVal b, EqSymbolic z) => Inductive ((Forall nxs [x], Forall nys [y]) -> Forall na a -> Forall nb b -> SBool) ((SBV x, SList x, SBV y, SList y) -> SBV a -> SBV b -> (SBool, KDProofRaw z)) where
  inductionStrategy result steps = do
       (x, xs, nxxs) <- mkLVar (Proxy @nxs)
       (y, ys, nyys) <- mkLVar (Proxy @nys)
       (a, na)       <- mkVar  (Proxy @na)
       (b, nb)       <- mkVar  (Proxy @nb)
       pure $ mkIndStrategy Nothing (Just (result (Forall SL.nil, Forall SL.nil) (Forall a) (Forall b) .&& result (Forall SL.nil, Forall (y SL..: ys)) (Forall a) (Forall b) .&& result (Forall (x SL..: xs), Forall SL.nil) (Forall a) (Forall b)))
                            (steps (internalAxiom "IH" (\(Forall a' :: Forall na a) (Forall b' :: Forall nb b) -> result (Forall xs, Forall ys) (Forall a') (Forall b'))) (x, xs, y, ys) a b)
                            (indResult [nxxs, nyys, na, nb] (result (Forall (x SL..: xs), Forall (y SL..: ys)) (Forall a) (Forall b)))

-- | Strong induction over two 'SList', simultaneously, taking two extra arguments
instance (KnownSymbol nxs, SymVal x, KnownSymbol nys, SymVal y, KnownSymbol na, SymVal a, KnownSymbol nb, SymVal b, EqSymbolic z) => SInductive ((Forall nxs [x], Forall nys [y]) -> Forall na a -> Forall nb b -> SBool) ((SList x, SList y) -> SBV a -> SBV b -> (SBool, KDProofRaw z)) where
  sInductionStrategy result steps = do
       (xs, nxs) <- mkVar (Proxy @nxs)
       (ys, nys) <- mkVar (Proxy @nys)
       (a, na)   <- mkVar  (Proxy @na)
       (b, nb)   <- mkVar  (Proxy @nb)
       pure $ mkIndStrategy Nothing Nothing
                            (steps (internalAxiom "IH" (\(Forall xs' :: Forall nxs [x], Forall ys' :: Forall nys [y]) (Forall a' :: Forall na a) (Forall b' :: Forall nb b) -> (xs', ys') `lexLeq2` (xs, ys) .=> result (Forall xs', Forall ys') (Forall a') (Forall b'))) (xs, ys) a b)
                            (indResult [nxs, nys, na, nb] (result (Forall xs, Forall ys) (Forall a) (Forall b)))

-- | Induction over two 'SList', simultaneously, taking three extra arguments
instance (KnownSymbol nxs, SymVal x, KnownSymbol nys, SymVal y, KnownSymbol na, SymVal a, KnownSymbol nb, SymVal b, KnownSymbol nc, SymVal c, EqSymbolic z) => Inductive ((Forall nxs [x], Forall nys [y]) -> Forall na a -> Forall nb b -> Forall nc c -> SBool) ((SBV x, SList x, SBV y, SList y) -> SBV a -> SBV b -> SBV c -> (SBool, KDProofRaw z)) where
  inductionStrategy result steps = do
       (x, xs, nxxs) <- mkLVar (Proxy @nxs)
       (y, ys, nyys) <- mkLVar (Proxy @nys)
       (a, na)       <- mkVar  (Proxy @na)
       (b, nb)       <- mkVar  (Proxy @nb)
       (c, nc)       <- mkVar  (Proxy @nc)
       pure $ mkIndStrategy Nothing (Just (result (Forall SL.nil, Forall SL.nil) (Forall a) (Forall b) (Forall c) .&& result (Forall SL.nil, Forall (y SL..: ys)) (Forall a) (Forall b) (Forall c) .&& result (Forall (x SL..: xs), Forall SL.nil) (Forall a) (Forall b) (Forall c)))
                            (steps (internalAxiom "IH" (\(Forall a' :: Forall na a) (Forall b' :: Forall nb b) (Forall c' :: Forall nc c) -> result (Forall xs, Forall ys) (Forall a') (Forall b') (Forall c'))) (x, xs, y, ys) a b c)
                            (indResult [nxxs, nyys, na, nb, nc] (result (Forall (x SL..: xs), Forall (y SL..: ys)) (Forall a) (Forall b) (Forall c)))

-- | Strong induction over two 'SList', simultaneously, taking three extra arguments
instance (KnownSymbol nxs, SymVal x, KnownSymbol nys, SymVal y, KnownSymbol na, SymVal a, KnownSymbol nb, SymVal b, KnownSymbol nc, SymVal c, EqSymbolic z) => SInductive ((Forall nxs [x], Forall nys [y]) -> Forall na a -> Forall nb b -> Forall nc c -> SBool) ((SList x, SList y) -> SBV a -> SBV b -> SBV c -> (SBool, KDProofRaw z)) where
  sInductionStrategy result steps = do
       (xs, nxs) <- mkVar (Proxy @nxs)
       (ys, nys) <- mkVar (Proxy @nys)
       (a, na)   <- mkVar  (Proxy @na)
       (b, nb)   <- mkVar  (Proxy @nb)
       (c, nc)   <- mkVar  (Proxy @nc)
       pure $ mkIndStrategy Nothing Nothing
                            (steps (internalAxiom "IH" (\(Forall xs' :: Forall nxs [x], Forall ys' :: Forall nys [y]) (Forall a' :: Forall na a) (Forall b' :: Forall nb b) (Forall c' :: Forall nc c) -> (xs', ys') `lexLeq2` (xs, ys) .=> result (Forall xs', Forall ys') (Forall a') (Forall b') (Forall c'))) (xs, ys) a b c)
                            (indResult [nxs, nys, na, nb, nc] (result (Forall xs, Forall ys) (Forall a) (Forall b) (Forall c)))

-- | Induction over two 'SList', simultaneously, taking four extra arguments
instance (KnownSymbol nxs, SymVal x, KnownSymbol nys, SymVal y, KnownSymbol na, SymVal a, KnownSymbol nb, SymVal b, KnownSymbol nc, SymVal c, KnownSymbol nd, SymVal d, EqSymbolic z) => Inductive ((Forall nxs [x], Forall nys [y]) -> Forall na a -> Forall nb b -> Forall nc c -> Forall nd d -> SBool) ((SBV x, SList x, SBV y, SList y) -> SBV a -> SBV b -> SBV c -> SBV d -> (SBool, KDProofRaw z)) where
  inductionStrategy result steps = do
       (x, xs, nxxs) <- mkLVar (Proxy @nxs)
       (y, ys, nyys) <- mkLVar (Proxy @nys)
       (a, na)       <- mkVar  (Proxy @na)
       (b, nb)       <- mkVar  (Proxy @nb)
       (c, nc)       <- mkVar  (Proxy @nc)
       (d, nd)       <- mkVar  (Proxy @nd)
       pure $ mkIndStrategy Nothing (Just (result (Forall SL.nil, Forall SL.nil) (Forall a) (Forall b) (Forall c) (Forall d) .&& result (Forall SL.nil, Forall (y SL..: ys)) (Forall a) (Forall b) (Forall c) (Forall d) .&& result (Forall (x SL..: xs), Forall SL.nil) (Forall a) (Forall b) (Forall c) (Forall d)))
                            (steps (internalAxiom "IH" (\(Forall a' :: Forall na a) (Forall b' :: Forall nb b) (Forall c' :: Forall nc c) (Forall d' :: Forall nd d) -> result (Forall xs, Forall ys) (Forall a') (Forall b') (Forall c') (Forall d'))) (x, xs, y, ys) a b c d)
                            (indResult [nxxs, nyys, na, nb, nc, nd] (result (Forall (x SL..: xs), Forall (y SL..: ys)) (Forall a) (Forall b) (Forall c) (Forall d)))

-- | Strong induction over two 'SList', simultaneously, taking four extra arguments
instance (KnownSymbol nxs, SymVal x, KnownSymbol nys, SymVal y, KnownSymbol na, SymVal a, KnownSymbol nb, SymVal b, KnownSymbol nc, SymVal c, KnownSymbol nd, SymVal d, EqSymbolic z) => SInductive ((Forall nxs [x], Forall nys [y]) -> Forall na a -> Forall nb b -> Forall nc c -> Forall nd d -> SBool) ((SList x, SList y) -> SBV a -> SBV b -> SBV c -> SBV d -> (SBool, KDProofRaw z)) where
  sInductionStrategy result steps = do
       (xs, nxs) <- mkVar (Proxy @nxs)
       (ys, nys) <- mkVar (Proxy @nys)
       (a, na)   <- mkVar  (Proxy @na)
       (b, nb)   <- mkVar  (Proxy @nb)
       (c, nc)   <- mkVar  (Proxy @nc)
       (d, nd)   <- mkVar  (Proxy @nd)
       pure $ mkIndStrategy Nothing Nothing
                            (steps (internalAxiom "IH" (\(Forall xs' :: Forall nxs [x], Forall ys' :: Forall nys [y]) (Forall a' :: Forall na a) (Forall b' :: Forall nb b) (Forall c' :: Forall nc c) (Forall d' :: Forall nd d) -> (xs', ys') `lexLeq2` (xs, ys) .=> result (Forall xs', Forall ys') (Forall a') (Forall b') (Forall c') (Forall d'))) (xs, ys) a b c d)
                            (indResult [nxs, nys, na, nb, nc, nd] (result (Forall xs, Forall ys) (Forall a) (Forall b) (Forall c) (Forall d)))

-- | Induction over two 'SList', simultaneously, taking five extra arguments
instance (KnownSymbol nxs, SymVal x, KnownSymbol nys, SymVal y, KnownSymbol na, SymVal a, KnownSymbol nb, SymVal b, KnownSymbol nc, SymVal c, KnownSymbol nd, SymVal d, KnownSymbol ne, SymVal e, EqSymbolic z) => Inductive ((Forall nxs [x], Forall nys [y]) -> Forall na a -> Forall nb b -> Forall nc c -> Forall nd d -> Forall ne e -> SBool) ((SBV x, SList x, SBV y, SList y) -> SBV a -> SBV b -> SBV c -> SBV d -> SBV e -> (SBool, KDProofRaw z)) where
  inductionStrategy result steps = do
       (x, xs, nxxs) <- mkLVar (Proxy @nxs)
       (y, ys, nyys) <- mkLVar (Proxy @nys)
       (a, na)       <- mkVar  (Proxy @na)
       (b, nb)       <- mkVar  (Proxy @nb)
       (c, nc)       <- mkVar  (Proxy @nc)
       (d, nd)       <- mkVar  (Proxy @nd)
       (e, ne)       <- mkVar  (Proxy @ne)
       pure $ mkIndStrategy Nothing (Just (result (Forall SL.nil, Forall SL.nil) (Forall a) (Forall b) (Forall c) (Forall d) (Forall e) .&& result (Forall SL.nil, Forall (y SL..: ys)) (Forall a) (Forall b) (Forall c) (Forall d) (Forall e) .&& result (Forall (x SL..: xs), Forall SL.nil) (Forall a) (Forall b) (Forall c) (Forall d) (Forall e)))
                            (steps (internalAxiom "IH" (\(Forall a' :: Forall na a) (Forall b' :: Forall nb b) (Forall c' :: Forall nc c) (Forall d' :: Forall nd d) (Forall e' :: Forall ne e) -> result (Forall xs, Forall ys) (Forall a') (Forall b') (Forall c') (Forall d') (Forall e'))) (x, xs, y, ys) a b c d e)
                            (indResult [nxxs, nyys, na, nb, nc, nd, ne] (result (Forall (x SL..: xs), Forall (y SL..: ys)) (Forall a) (Forall b) (Forall c) (Forall d) (Forall e)))

-- | Strong induction over two 'SList', simultaneously, taking five extra arguments
instance (KnownSymbol nxs, SymVal x, KnownSymbol nys, SymVal y, KnownSymbol na, SymVal a, KnownSymbol nb, SymVal b, KnownSymbol nc, SymVal c, KnownSymbol nd, SymVal d, KnownSymbol ne, SymVal e, EqSymbolic z) => SInductive ((Forall nxs [x], Forall nys [y]) -> Forall na a -> Forall nb b -> Forall nc c -> Forall nd d -> Forall ne e -> SBool) ((SList x, SList y) -> SBV a -> SBV b -> SBV c -> SBV d -> SBV e -> (SBool, KDProofRaw z)) where
  sInductionStrategy result steps = do
       (xs, nxs) <- mkVar (Proxy @nxs)
       (ys, nys) <- mkVar (Proxy @nys)
       (a, na)   <- mkVar  (Proxy @na)
       (b, nb)   <- mkVar  (Proxy @nb)
       (c, nc)   <- mkVar  (Proxy @nc)
       (d, nd)   <- mkVar  (Proxy @nd)
       (e, ne)   <- mkVar  (Proxy @ne)
       pure $ mkIndStrategy Nothing Nothing
                            (steps (internalAxiom "IH" (\(Forall xs' :: Forall nxs [x], Forall ys' :: Forall nys [y]) (Forall a' :: Forall na a) (Forall b' :: Forall nb b) (Forall c' :: Forall nc c) (Forall d' :: Forall nd d) (Forall e' :: Forall ne e) -> (xs', ys') `lexLeq2` (xs, ys) .=> result (Forall xs', Forall ys') (Forall a') (Forall b') (Forall c') (Forall d') (Forall e'))) (xs, ys) a b c d e)
                            (indResult [nxs, nys, na, nb, nc, nd, ne] (result (Forall xs, Forall ys) (Forall a) (Forall b) (Forall c) (Forall d) (Forall e)))

-- | Instantiation for a universally quantified variable
newtype Inst (nm :: Symbol) a = Inst (SBV a)

instance KnownSymbol nm => Show (Inst nm a) where
   show (Inst a) = symbolVal (Proxy @nm) ++ " |-> " ++ show a

-- | Instantiating a proof at different types of arguments. This is necessarily done using
-- dynamics, hand has a cost of not being applicable.
class Instantiatable a where
  -- | Apply a universal proof to some arguments, creating an instance of the proof itself.
  at :: Proof -> a -> Proof

  -- | Apply a universal proof to some arguments, for a pair of arguments, creating an instance of the proof itself
  at2 :: Proof -> a -> Proof

-- | Single parameter
instance (KnownSymbol na, HasKind a, Typeable a) => Instantiatable (Inst na a) where
  at  = instantiate $ \f (Inst a) -> f (Forall a :: Forall na a)
  at2 = at  -- Single parameter, so no chance of having a pair. Just use at.

-- | Two parameters
instance ( KnownSymbol na, HasKind a, Typeable a
         , KnownSymbol nb, HasKind b, Typeable b
         ) => Instantiatable (Inst na a, Inst nb b) where
  at  = instantiate $ \f (Inst a, Inst b) -> f (Forall a :: Forall na a) (Forall b :: Forall nb b)
  at2 = instantiate $ \f (Inst a, Inst b) -> f (Forall a :: Forall na a,  Forall b :: Forall nb b)

-- | Three parameters
instance ( KnownSymbol na, HasKind a, Typeable a
         , KnownSymbol nb, HasKind b, Typeable b
         , KnownSymbol nc, HasKind c, Typeable c
         ) => Instantiatable (Inst na a, Inst nb b, Inst nc c) where
  at  = instantiate $ \f (Inst a, Inst b, Inst c) -> f (Forall a :: Forall na a) (Forall b :: Forall nb b) (Forall c :: Forall nc c)
  at2 = instantiate $ \f (Inst a, Inst b, Inst c) -> f (Forall a :: Forall na a,  Forall b :: Forall nb b) (Forall c :: Forall nc c)

-- | Four parameters
instance ( KnownSymbol na, HasKind a, Typeable a
         , KnownSymbol nb, HasKind b, Typeable b
         , KnownSymbol nc, HasKind c, Typeable c
         , KnownSymbol nd, HasKind d, Typeable d
         ) => Instantiatable (Inst na a, Inst nb b, Inst nc c, Inst nd d) where
  at  = instantiate $ \f (Inst a, Inst b, Inst c, Inst d) -> f (Forall a :: Forall na a) (Forall b :: Forall nb b) (Forall c :: Forall nc c) (Forall d :: Forall nd d)
  at2 = instantiate $ \f (Inst a, Inst b, Inst c, Inst d) -> f (Forall a :: Forall na a,  Forall b :: Forall nb b) (Forall c :: Forall nc c) (Forall d :: Forall nd d)

-- | Five parameters
instance ( KnownSymbol na, HasKind a, Typeable a
         , KnownSymbol nb, HasKind b, Typeable b
         , KnownSymbol nc, HasKind c, Typeable c
         , KnownSymbol nd, HasKind d, Typeable d
         , KnownSymbol ne, HasKind e, Typeable e
         ) => Instantiatable (Inst na a, Inst nb b, Inst nc c, Inst nd d, Inst ne e) where
  at  = instantiate $ \f (Inst a, Inst b, Inst c, Inst d, Inst e) -> f (Forall a :: Forall na a) (Forall b :: Forall nb b) (Forall c :: Forall nc c) (Forall d :: Forall nd d) (Forall e :: Forall ne e)
  at2 = instantiate $ \f (Inst a, Inst b, Inst c, Inst d, Inst e) -> f (Forall a :: Forall na a,  Forall b :: Forall nb b) (Forall c :: Forall nc c) (Forall d :: Forall nd d) (Forall e :: Forall ne e)

-- | Instantiate a proof over an arg. This uses dynamic typing, kind of hacky, but works sufficiently well.
instantiate :: (Typeable f, Show arg) => (f -> arg -> SBool) -> Proof -> arg -> Proof
instantiate ap p@Proof{getProp, proofName} a = case fromDynamic getProp of
                                                 Nothing -> cantInstantiate
                                                 Just f  -> let result = f `ap` a
                                                                nm     = proofName ++ " @ " ++ paren sha
                                                            in p { getProof  = label nm result
                                                                 , getProp   = toDyn result
                                                                 , proofName = nm
                                                                 }
 where sha = show a
       cantInstantiate = error $ unlines [ "at: Cannot instantiate proof:"
                                         , "   Name: " ++ proofName
                                         , "   Type: " ++ trim (show getProp)
                                         , "   At  : " ++ sha
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
data Helper = HelperProof Proof -- A previously proven theorem
            | HelperAssum SBool -- A hypothesis

-- | Get all helpers used in a proof
getAllHelpers :: KDProof -> [Helper]
getAllHelpers (ProofStep   _           hs p)  = hs ++ getAllHelpers p
getAllHelpers (ProofBranch (_ :: Bool) () ps) = concatMap (getAllHelpers . snd) ps
getAllHelpers (ProofEnd    _           hs)    = hs

-- | Get proofs from helpers
getHelperProofs :: Helper -> [Proof]
getHelperProofs (HelperProof p) = [p]
getHelperProofs HelperAssum {}  = []

-- | Get proofs from helpers
getHelperAssumes :: Helper -> [SBool]
getHelperAssumes HelperProof  {} = []
getHelperAssumes (HelperAssum b) = [b]

-- | Smart constructor for creating a helper from a boolean. This is hardly needed, unless you're
-- mixing proofs and booleans in one group of hints.
hyp :: SBool -> Helper
hyp = HelperAssum

-- | Smart constructor for creating a helper from a boolean. This is hardly needed, unless you're
-- mixing proofs and booleans in one group of hints.
hprf :: Proof -> Helper
hprf = HelperProof

-- | A proof is a sequence of steps, supporting branching
data KDProofGen a bh b = ProofStep   a    [Helper] (KDProofGen a bh b)          -- ^ A single step
                       | ProofBranch Bool bh       [(SBool, KDProofGen a bh b)] -- ^ A branching step. Bool indicates if completeness check is needed
                       | ProofEnd    b    [Helper]                              -- ^ End of proof

-- | A proof, as written by the user. No produced result, but helpers on branches
type KDProofRaw a = KDProofGen a [Helper] ()

-- | A proof, as processed by KD. Producing a boolean result and each step is a boolean. Helpers on branches dispersed down, and thus empty
type KDProof = KDProofGen SBool () SBool

-- | Class capturing giving a proof-step helper
type family Hinted a where
  Hinted (KDProofRaw a) = KDProofRaw a
  Hinted a              = KDProofRaw a

-- | Attaching a hint
(??) :: HintsTo a b => a -> b -> Hinted a
(??) = addHint
infixl 2 ??

-- | Class capturing hints
class HintsTo a b where
  addHint :: a -> b -> Hinted a

-- | Giving just one proof as a helper.
instance Hinted a ~ KDProofRaw a => HintsTo a Proof where
  a `addHint` p = ProofStep a [HelperProof p] qed

-- | Giving just one boolean as a helper.
instance Hinted a ~ KDProofRaw a => HintsTo a SBool where
  a `addHint` p = ProofStep a [HelperAssum p] qed

-- | Giving just one helper
instance Hinted a ~ KDProofRaw a => HintsTo a Helper where
  a `addHint` h = ProofStep a [h] qed

-- | Giving a bunch of proofs as a helper.
instance Hinted a ~ KDProofRaw a => HintsTo a [Proof] where
  a `addHint` ps = ProofStep a (map HelperProof ps) qed

-- | Giving a bunch of booleans as a helper.
instance Hinted a ~ KDProofRaw a => HintsTo a [SBool] where
  a `addHint` ps = ProofStep a (map HelperAssum ps) qed

-- | Giving a set of helpers
instance Hinted a ~ KDProofRaw a => HintsTo a [Helper] where
  a `addHint` hs = ProofStep a hs qed

-- | Giving user a hint as a string. This doesn't actually do anything for the solver, it just helps with readability
instance Hinted a ~ KDProofRaw a => HintsTo a String where
  a `addHint` _ = ProofStep a [] qed

-- | Giving just one proof as a helper, starting from a proof
instance {-# OVERLAPPING #-} Hinted (KDProofRaw a) ~ KDProofRaw a => HintsTo (KDProofRaw a) Proof where
  ProofStep   a hs ps `addHint` h = ProofStep   a (hs ++ [HelperProof h]) ps
  ProofBranch b hs bs `addHint` h = ProofBranch b (hs ++ [HelperProof h]) bs
  ProofEnd    b hs    `addHint` h = ProofEnd    b (hs ++ [HelperProof h])

-- | Giving just one boolean as a helper.
instance {-# OVERLAPPING #-} Hinted (KDProofRaw a) ~ KDProofRaw a => HintsTo (KDProofRaw a) SBool where
  ProofStep   a hs ps `addHint` h = ProofStep   a (hs ++ [HelperAssum h]) ps
  ProofBranch b hs bs `addHint` h = ProofBranch b (hs ++ [HelperAssum h]) bs
  ProofEnd    b hs    `addHint` h = ProofEnd    b (hs ++ [HelperAssum h])

-- | Giving just one helper
instance {-# OVERLAPPING #-} Hinted (KDProofRaw a) ~ KDProofRaw a => HintsTo (KDProofRaw a) Helper where
  ProofStep   a hs ps `addHint` h = ProofStep   a (hs ++ [h]) ps
  ProofBranch b hs bs `addHint` h = ProofBranch b (hs ++ [h]) bs
  ProofEnd    b hs    `addHint` h = ProofEnd    b (hs ++ [h])

-- | Giving a bunch of proofs as a helper.
instance {-# OVERLAPPING #-} Hinted (KDProofRaw a) ~ KDProofRaw a => HintsTo (KDProofRaw a) [Proof] where
  ProofStep   a hs ps `addHint` hs' = ProofStep   a (hs ++ map HelperProof hs') ps
  ProofBranch b hs bs `addHint` hs' = ProofBranch b (hs ++ map HelperProof hs') bs
  ProofEnd    b hs    `addHint` hs' = ProofEnd    b (hs ++ map HelperProof hs')

-- | Giving a bunch of booleans as a helper.
instance {-# OVERLAPPING #-} Hinted (KDProofRaw a) ~ KDProofRaw a => HintsTo (KDProofRaw a) [SBool] where
  ProofStep   a hs ps `addHint` hs' = ProofStep   a (hs ++ map HelperAssum hs') ps
  ProofBranch b hs bs `addHint` hs' = ProofBranch b (hs ++ map HelperAssum hs') bs
  ProofEnd    b hs    `addHint` hs' = ProofEnd    b (hs ++ map HelperAssum hs')

-- | Giving a set of helpers
instance {-# OVERLAPPING #-} Hinted (KDProofRaw a) ~ KDProofRaw a => HintsTo (KDProofRaw a) [Helper] where
  ProofStep   a hs ps `addHint` hs' = ProofStep   a (hs ++ hs') ps
  ProofBranch b hs bs `addHint` hs' = ProofBranch b (hs ++ hs') bs
  ProofEnd    b hs    `addHint` hs' = ProofEnd    b (hs ++ hs')

-- | Giving user a hint as a string. This doesn't actually do anything for the solver, it just helps with readability
instance {-# OVERLAPPING #-} Hinted (KDProofRaw a) ~ KDProofRaw a => HintsTo (KDProofRaw a) String where
  a `addHint` _ = a

-- | Capture what a given step can chain-to. This is a closed-type family, i.e.,
-- we don't allow users to change this and write other chainable things. Probably it is not really necessary,
-- but we'll cross that bridge if someone actually asks for it.
type family ChainsTo a where
  ChainsTo (KDProofRaw a) = KDProofRaw a
  ChainsTo a              = KDProofRaw a

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
instance ChainStep a (KDProofRaw a) where
  chain x y = ProofStep x [] y

-- | Chaining from another proof step
instance ChainStep (KDProofRaw a) (KDProofRaw a) where
  chain (ProofStep   a  hs  p)  y = ProofStep   a hs (chain p y)
  chain (ProofBranch c  hs  ps) y = ProofBranch c hs [(branchCond, chain p y) | (branchCond, p) <- ps]
  chain (ProofEnd    () hs)     y = case y of
                                      ProofStep   a  hs' p  -> ProofStep   a  (hs' ++ hs) p
                                      ProofBranch b  hs' bs -> ProofBranch b  (hs' ++ hs) bs
                                      ProofEnd    () hs'    -> ProofEnd    () (hs' ++ hs)

-- | Mark the end of a calculational proof.
qed :: KDProofRaw a
qed = ProofEnd () []

-- | Mark a trivial proof. This is the same as 'qed', but reads better in proof scripts.
trivial :: KDProofRaw a
trivial = qed

-- | Start a calculational proof, with the given hypothesis. Use @[]@ as the
-- first argument if the calculation holds unconditionally. The first argument is
-- typically used to introduce hypotheses in proofs of implications such as @A .=> B .=> C@, where
-- we would put @[A, B]@ as the starting assumption. You can name these and later use in the derivation steps.
(|-) :: [SBool] -> KDProofRaw a -> (SBool, KDProofRaw a)
bs |- p = (sAnd bs, p)
infixl 0 |-

-- | Alternative unicode for `|-`.
(⊢) :: [SBool] -> KDProofRaw a -> (SBool, KDProofRaw a)
(⊢) = (|-)
infixl 0 ⊢

-- | Alternative unicode for `??`.
(⁇) :: HintsTo a b => a -> b -> Hinted a
(⁇) = (??)
infixl 2 ⁇

-- | The boolean case-split
cases :: [(SBool, KDProofRaw a)] -> KDProofRaw a
cases = ProofBranch True []

-- | Case splitting over a list; empty and full cases
split :: SymVal a => SList a -> KDProofRaw r -> (SBV a -> SList a -> KDProofRaw r) -> KDProofRaw r
split xs empty cons = ProofBranch False [] [ (      SL.null xs,  empty)
                                           , (sNot (SL.null xs), cons (SL.head xs) (SL.tail xs))
                                           ]

-- | Case splitting over two lists; empty and full cases for each
split2 :: (SymVal a, SymVal b)
       => (SList a, SList b)
       -> KDProofRaw r
       -> ((SBV b, SList b)                     -> KDProofRaw r) -- empty first
       -> ((SBV a, SList a)                     -> KDProofRaw r) -- empty second
       -> ((SBV a, SList a) -> (SBV b, SList b) -> KDProofRaw r) -- neither empty
       -> KDProofRaw r
split2 (xs, ys) ee ec ce cc = ProofBranch False
                                          []
                                          [ (      SL.null xs  .&&       SL.null ys , ee)
                                          , (      SL.null xs  .&& sNot (SL.null ys), ec (SL.head ys, SL.tail ys))
                                          , (sNot (SL.null xs) .&&       SL.null ys , ce (SL.head xs, SL.tail xs))
                                          , (sNot (SL.null xs) .&& sNot (SL.null ys), cc (SL.head xs, SL.tail xs) (SL.head ys, SL.tail ys))
                                          ]

-- | Specifying a case-split, helps with the boolean case.
(==>) :: SBool -> KDProofRaw a -> (SBool, KDProofRaw a)
(==>) = (,)
infix 0 ==>

-- | Alternative unicode for `==>`
(⟹) :: SBool -> KDProofRaw a -> (SBool, KDProofRaw a)
(⟹) = (==>)
infix 0 ⟹

{- HLint ignore module "Eta reduce" -}
