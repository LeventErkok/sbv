-----------------------------------------------------------------------------
-- |
-- Module    : TestSuite.Queries.BadOption
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Testing that a bad option setting is caught properly.
-----------------------------------------------------------------------------

{-# LANGUAGE ScopedTypeVariables #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module TestSuite.Queries.BadOption (tests)  where

import Data.SBV.Control
import qualified Control.Exception as C

import Utils.SBVTestFramework

-- Test suite
tests :: TestTree
tests =
  testGroup "Basics.QueryIndividual"
    [ goldenCapturedIO "query_badOption" $ \rf -> runSMTWith z3{verbose=True, redirectVerbose=Just rf} q
                                                  `C.catch`
                                                  (\(e::C.SomeException) -> appendFile rf ("\n" ++ show e))
    ]

q :: Symbolic ()
q = do _ <- sInteger "x"
       setOption $ OptionKeyword ":there-is-no-such-option" ["bad", "argument"]
       query $ return ()
