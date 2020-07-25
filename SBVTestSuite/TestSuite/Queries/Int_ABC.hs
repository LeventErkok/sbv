-----------------------------------------------------------------------------
-- |
-- Module    : TestSuite.Queries.Int_ABC
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Testing ABC specific interactive features.
-----------------------------------------------------------------------------

{-# LANGUAGE ScopedTypeVariables #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module TestSuite.Queries.Int_ABC (tests)  where

import Data.SBV.Control

import Control.Monad (unless)

import Utils.SBVTestFramework

-- Test suite
tests :: TestTree
tests =
  testGroup "Basics.QueryIndividual"
    [ goldenCapturedIO "query_abc" $ \rf -> runSMTWith abc{verbose=True, redirectVerbose=Just rf} q
    ]

q :: Symbolic ()
q = do a <- sInt32 "a"
       b <- sInt32 "b"

       constrain $ a .> 0
       constrain $ b .> 0

       -- this is severely limited since ABC doesn't like multi check-sat calls, oh well.
       query $ do constrain $ a+2 .<= 15
                  constrain $ a   .<  2
                  constrain $ b   .<  2
                  constrain $ a+b .< 12

                  constrain $ a .< 2
                  cs <- checkSat

                  case cs of
                    Unk    -> getInfo ReasonUnknown >>= error . show
                    Unsat  -> error "Got UNSAT!"
                    DSat{} -> error "Got Delta-satisfiable!"
                    Sat    -> do -- Query a/b
                                 res <- (,) <$> getValue a <*> getValue b
                                 unless (res == (1, 1)) $ error $ "Didn't get (1,1): " ++ show res
