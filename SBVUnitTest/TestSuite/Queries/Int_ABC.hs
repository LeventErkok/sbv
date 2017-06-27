-----------------------------------------------------------------------------
-- |
-- Module      :  TestSuite.Queries.Int_ABC
-- Copyright   :  (c) Levent Erkok
-- License     :  BSD3
-- Maintainer  :  erkokl@gmail.com
-- Stability   :  experimental
--
-- Testing ABC specific interactive features.
-----------------------------------------------------------------------------
{-# LANGUAGE ScopedTypeVariables #-}

module TestSuite.Queries.Int_ABC (tests)  where

import Data.SBV
import Data.SBV.Control

import SBVTest

-- Test suite
tests :: TestTree
tests =
  testGroup "Basics.QueryIndividual"
    [ goldenCapturedIO "query_abc" $ print =<< runSMTWith abc{verbose=True} q
    ]


q :: Symbolic (Int32, Int32)
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
                    Sat -> io $ putStrLn "Everything is OK"
                    Unk -> io .print =<< getInfo ReasonUnknown
                    r   -> error $ "Something went bad, why not-sat/unk?: " ++ show r

                  -- Query a/b
                  av <- getValue a
                  bv <- getValue b
                  io $ putStrLn $ "(a,b) = " ++ show (av, bv)
                  return (av, bv)
