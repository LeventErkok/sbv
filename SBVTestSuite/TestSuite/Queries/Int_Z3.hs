-----------------------------------------------------------------------------
-- |
-- Module    : TestSuite.Queries.Int_Z3
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Testing Z3 specific interactive features.
-----------------------------------------------------------------------------

{-# LANGUAGE ScopedTypeVariables #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module TestSuite.Queries.Int_Z3 (tests)  where

import Data.SBV.Control

import Control.Monad (unless)

import Utils.SBVTestFramework

-- Test suite
tests :: TestTree
tests =
  testGroup "Basics.QueryIndividual"
    [ goldenCapturedIO "query_z3" $ \rf -> runSMTWith z3{verbose=True, redirectVerbose=Just rf} q
    ]

q :: Symbolic ()
q = do a <- sInt32 "a"
       b <- sInt32 "b"

       namedConstraint "a > 0" $ a .> 0
       constrain $ b .> 0

       query $ do constrain $ a+2 .<= 15
                  constrain $ a   .<  3
                  constrain $ b   .<  2
                  namedConstraint "a+b_<_12" $ a+b .< 12

                  gv <- inNewAssertionStack $ do

                            constrain $ a .< 2
                            cs <- checkSat

                            case cs of
                              Sat -> return ()
                              Unk -> getInfo ReasonUnknown >>= error . show
                              r   -> error $ "Something went bad, why not-sat/unk?: " ++ show r

                            -- Query a/b
                            getValue a

                  -- Now assert so that we get even a bigger value..
                  namedConstraint "extra" $ a .> literal gv
                  constrain $ b .< 2

                  _ <- checkSat

                  res <- (,) <$> getValue a <*> getValue b
                  unless (res == (2, 1)) $ error $ "Didn't get (2,1): " ++ show res
