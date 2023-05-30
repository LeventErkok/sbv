-----------------------------------------------------------------------------
-- |
-- Module    : TestSuite.Basics.Exceptions
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Test the exception mechanism
-----------------------------------------------------------------------------

{-# LANGUAGE ScopedTypeVariables #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module TestSuite.Basics.Exceptions(testsLocal, testsRemote)  where

import Data.SBV.Control
import Utils.SBVTestFramework

import qualified Control.Exception as C

-- Test suite
testsLocal :: TestTree
testsLocal =
  testGroup "Basics.exceptions.local"
    [ goldenCapturedIO "exceptionLocal1" yicesExc
    , goldenCapturedIO "exceptionLocal2" z3Exc1
    ]

-- Yices throws an exception for this since exponent is too large
yicesExc :: FilePath -> IO ()
yicesExc rf = runSMTWith yices{verbose=True, redirectVerbose=Just rf} exc
                             `C.catch` \(e :: SBVException) -> do appendFile rf "CAUGHT SMT EXCEPTION"
                                                                  appendFile rf (show e)
 where exc = do x <- sWord32 "x"
                constrain $ lsb x .=> (x * (x .^ (-1::SWord32))) .== 1
                query $ do cs <- checkSat
                           cs `seq` return ()

testsRemote :: TestTree
testsRemote =
  testGroup "Basics.exceptions.remote"
    [ goldenCapturedIO "exceptionRemote1" z3Exc2
    ]

-- Create the case where we ask for integer-logic, but use reals
z3Exc1 :: FilePath -> IO ()
z3Exc1 rf = runSMTWith z3{verbose=True, redirectVerbose=Just rf} exc
                `C.catch` \(e :: SBVException) -> do appendFile rf "CAUGHT SMT EXCEPTION"
                                                     appendFile rf (show e)
   where exc = do setLogic QF_LIA
                  x <- sReal "x"
                  constrain $ x .== 2
                  query $ do cs <- checkSat
                             cs `seq` return ()

-- Similar to above, except linear logic, but use non-linear constructs
z3Exc2 :: FilePath -> IO ()
z3Exc2 rf = do r <- runSMT z3ExcCatch `C.catch` \(e :: SBVException) -> return ("OK, we got: " ++ sbvExceptionDescription e)
               appendFile rf ("\nFINAL: " ++ show r ++ "\nDONE!\n")
  where z3ExcCatch = do setLogic QF_LIA
                        x <- sInteger "x"
                        y <- sInteger "y"
                        query $ do constrain $ x*y .== x*x
                                   show <$> checkSat

{- HLint ignore module "Reduce duplication" -}
