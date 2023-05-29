-----------------------------------------------------------------------------
-- |
-- Module    : Utils.SBVTestFramework
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Various goodies for testing SBV
-----------------------------------------------------------------------------

{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies        #-}
{-# LANGUAGE TypeOperators       #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module Utils.SBVTestFramework (
          showsAs
        , runSAT, numberOfModels
        , assert, assertIsThm, assertIsntThm, assertIsSat, assertIsntSat
        , goldenString
        , goldenVsStringShow
        , goldenCapturedIO
        , qc1, qc2
        , shouldNotTypeCheck
        -- module exports to simplify life
        , module Test.Tasty
        , module Test.Tasty.HUnit
        , module Data.SBV
        ) where

import qualified Control.Exception as C

import Control.DeepSeq     (force, NFData)
import Control.Exception   (evaluate, try, throwIO, TypeError(..))
import Control.Monad.Trans (liftIO)

import qualified Data.ByteString.Lazy.Char8 as LBC

import System.Directory   (removeFile)

import Test.Tasty            (testGroup, TestTree, TestName)
import Test.Tasty.HUnit      ((@?), Assertion, testCase, AssertionPredicable, assertFailure)

import Test.Tasty.Golden     (goldenVsString, goldenVsFileDiff)

import qualified Test.Tasty.QuickCheck   as QC
import qualified Test.QuickCheck.Monadic as QC

import Test.Tasty.Runners hiding (Result)

import Data.SBV
import Data.SBV.Control

import System.FilePath ((</>), (<.>))
import Data.List       (isInfixOf, isSuffixOf)


import Data.SBV.Internals (runSymbolic, Result, SBVRunMode(..), IStage(..), SBV(..), SVal(..), showModel, SMTModel(..), QueryContext(..), Outputtable)

-- | Generic assertion. This is less safe than usual, but will do.
assert :: AssertionPredicable t => t -> Assertion
assert t = t @? "assertion-failure"

-- | Checks that a particular result shows as @s@
showsAs :: Show a => a -> String -> Assertion
showsAs r s = assert $ show r == s

goldFile :: FilePath -> FilePath
goldFile nm = "SBVTestSuite" </> "GoldFiles" </> nm <.> "gold"

goldenString :: TestName -> IO String -> TestTree
goldenString n res = goldenVsString n (goldFile n) (fmap LBC.pack res)

goldenVsStringShow :: Show a => TestName -> IO a -> TestTree
goldenVsStringShow n res = goldenVsString n (goldFile n) (fmap (LBC.pack . show) res)

goldenCapturedIO :: TestName -> (FilePath -> IO ()) -> TestTree
goldenCapturedIO n res = goldenVsFileDiff n diff gf gfTmp (rm gfTmp >> res gfTmp)
  where gf    = goldFile n
        gfTmp = gf ++ "_temp"
        rm f  = removeFile f `C.catch` (\(_ :: C.SomeException) -> return ())

        diff ref new = ["diff", "-u", ref, new]

-- | Count the number of models. It's not kosher to
-- call this function if you provided a max-model count
-- that was hit, or the search was stopped because the
-- solver said 'Unknown' at some point.
numberOfModels :: Satisfiable a => a -> IO Int
numberOfModels p = do AllSatResult { allSatMaxModelCountReached  = maxHit
                                   , allSatSolverReturnedUnknown = unk
                                   , allSatSolverReturnedDSat    = ds
                                   , allSatResults               = rs
                                   } <- allSat p
                      let l = length rs
                      case (unk, ds, maxHit) of
                        (True, _, _)   -> error $ "Data.SBV.numberOfModels: Search was stopped because solver said 'Unknown'. At this point, we saw: " ++ show l ++ " model(s)."
                        (_, True, _)   -> error $ "Data.SBV.numberOfModels: Search was stopped because solver returned 'delta satisfiable'. At this point, we saw: " ++ show l ++ " model(s)."
                        (_,   _, True) -> error $ "Data.SBV.numberOfModels: Search was stopped because the user-specified max-model count was hit at " ++ show l ++ " model(s)."
                        _              -> return l

-- | Symbolically run a SAT instance using the default config
runSAT :: Outputtable a => Symbolic a -> IO Result
runSAT cmp = snd <$> runSymbolic defaultSMTCfg (SMTMode QueryInternal ISetup True defaultSMTCfg) (cmp >>= output >> pure ())

-- | Turn provable to an assertion, theorem case
assertIsThm :: Provable a => a -> Assertion
assertIsThm t = assert (isTheorem t)

-- | Turn provable to a negative assertion, theorem case
assertIsntThm :: Provable a => a -> Assertion
assertIsntThm t = assert (fmap not (isTheorem t))

-- | Turn provable to an assertion, satisfiability case
assertIsSat :: Satisfiable a => a -> Assertion
assertIsSat p = assert (isSatisfiable p)

-- | Turn provable to a negative assertion, satisfiability case
assertIsntSat :: Satisfiable a => a -> Assertion
assertIsntSat p = assert (fmap not (isSatisfiable p))

-- | Quick-check a unary function, creating one version for constant folding, and another for solver
qc1 :: (Eq a, SymVal a, SymVal b, Show a, QC.Arbitrary a, Eq b) => String -> (a -> b) -> (SBV a -> SBV b) -> [TestTree]
qc1 nm opC opS = [cf, sm]
   where cf = QC.testProperty (nm ++ ".constantFold") $ \i ->
                         case unliteral (opS (literal i)) of
                             Just r -> opC i == r
                             _      -> False

         sm = QC.testProperty (nm ++ ".symbolic") $ QC.monadicIO $ do
                        ((i, expected), result) <- QC.run $ runSMT $ do v   <- liftIO $ QC.generate QC.arbitrary
                                                                        i   <- free_
                                                                        res <- free_

                                                                        constrain $ i   .== literal v
                                                                        constrain $ res .== opS i

                                                                        let pre = (v, opC v)

                                                                        query $ do cs <- checkSat
                                                                                   case cs of
                                                                                     Unk    -> return (pre, Left "Unexpected: Solver responded Unknown!")
                                                                                     Unsat  -> return (pre, Left "Unexpected: Solver responded Unsatisfiable!")
                                                                                     DSat{} -> return (pre, Left "Unexpected: Solver responded Delta-satisfiable!")
                                                                                     Sat    -> do r <- getValue res
                                                                                                  return (pre, Right r)

                        let getCV vnm (SBV (SVal _ (Left c))) = (vnm, c)
                            getCV vnm (SBV (SVal k _       )) = error $ "qc2.getCV: Impossible happened, non-CV value while extracting: " ++ show (vnm, k)

                            vals = [ getCV "i"        (literal i)
                                   , getCV "Expected" (literal expected)
                                   ]

                            model = case result of
                                      Right v -> showModel defaultSMTCfg (SMTModel [] Nothing (vals ++ [getCV "Result" (literal v)]) [])
                                      Left  e -> showModel defaultSMTCfg (SMTModel [] Nothing vals []) ++ "\n" ++ e

                        QC.monitor (QC.counterexample model)

                        case result of
                           Right a -> QC.assert $ expected == a
                           _       -> QC.assert False


-- | Quick-check a binary function, creating one version for constant folding, and another for solver
qc2 :: (Eq a, Eq b, SymVal a, SymVal b, SymVal c, Show a, Show b, QC.Arbitrary a, QC.Arbitrary b, Eq c) => String -> (a -> b -> c) -> (SBV a -> SBV b -> SBV c) -> [TestTree]
qc2 nm opC opS = [cf, sm]
   where cf = QC.testProperty (nm ++ ".constantFold") $ \i j ->
                         case unliteral (opS (literal i) (literal j)) of
                             Just r -> opC i j == r
                             _      -> False

         sm = QC.testProperty (nm ++ ".symbolic") $ QC.monadicIO $ do
                        ((i1, i2, expected), result) <- QC.run $ runSMT $ do v1  <- liftIO $ QC.generate QC.arbitrary
                                                                             v2  <- liftIO $ QC.generate QC.arbitrary
                                                                             i1  <- free_
                                                                             i2  <- free_
                                                                             res <- free_

                                                                             constrain $ i1  .== literal v1
                                                                             constrain $ i2  .== literal v2
                                                                             constrain $ res .== i1 `opS` i2

                                                                             let pre = (v1, v2, v1 `opC` v2)

                                                                             query $ do cs <- checkSat
                                                                                        case cs of
                                                                                          Unk    -> return (pre, Left "Unexpected: Solver responded Unknown!")
                                                                                          Unsat  -> return (pre, Left "Unexpected: Solver responded Unsatisfiable!")
                                                                                          DSat{} -> return (pre, Left "Unexpected: Solver responded Delta-satisfiable!")
                                                                                          Sat    -> do r <- getValue res
                                                                                                       return (pre, Right r)

                        let getCV vnm (SBV (SVal _ (Left c))) = (vnm, c)
                            getCV vnm (SBV (SVal k _       )) = error $ "qc2.getCV: Impossible happened, non-CV value while extracting: " ++ show (vnm, k)

                            vals = [ getCV "i1"       (literal i1)
                                   , getCV "i2"       (literal i2)
                                   , getCV "Expected" (literal expected)
                                   ]

                            model = case result of
                                      Right v -> showModel defaultSMTCfg (SMTModel [] Nothing (vals ++ [getCV "Result" (literal v)]) [])
                                      Left  e -> showModel defaultSMTCfg (SMTModel [] Nothing vals []) ++ "\n" ++ e

                        QC.monitor (QC.counterexample model)

                        case result of
                           Right a -> QC.assert $ expected == a
                           _       -> QC.assert False


-- Adapted from https://github.com/CRogers/should-not-typecheck/blob/2929b8303634fcfe200e8e37b744171aed3a757b/src/Test/ShouldNotTypecheck.hs#L1
shouldNotTypeCheck :: NFData a => (() ~ () => a) -> Assertion
shouldNotTypeCheck a = do
  result <- try (evaluate $ force a)
  case result of
    Right _ -> assertFailure "Expected to not compile but it did compile."

    Left e@(TypeError msg)
      | "(deferred type error)" `isSuffixOf` msg
      -> case () of
           () |     "No instance for" `isInfixOf` msg
                 && "NFData"          `isInfixOf` msg
              -> assertFailure $ "Make sure the expression has an NFData instance! Full error:\n" ++ msg
              | True
              -> pure ()
      | True
      -> throwIO e

{- HLint ignore module "Reduce duplication" -}
