-----------------------------------------------------------------------------
-- |
-- Module    : TestSuite.Arrays.Query
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Test suite for query mode arrays
-----------------------------------------------------------------------------

{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE ScopedTypeVariables #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module TestSuite.Arrays.Query(tests) where

import Data.SBV.Rational
import Data.SBV.Control

import Utils.SBVTestFramework

-- Test suite
tests :: TestTree
tests =
  testGroup "Arrays.Query"
    [ goldenCapturedIO "queryArrays1"  $ t q1
    , goldenCapturedIO "queryArrays2"  $ t q2
    , goldenCapturedIO "queryArrays3"  $ t q3
    , goldenCapturedIO "queryArrays4"  $ t q4
    , goldenCapturedIO "queryArrays5"  $ t q5
    , goldenCapturedIO "queryArrays6"  $ t q6
    , goldenCapturedIO "queryArrays7"  $ t q7
    , goldenCapturedIO "queryArrays8"  $ t q8
    , goldenCapturedIO "queryArrays9"  $ t q9
    , goldenCapturedIO "queryArrays10" $ t q10
    , goldenCapturedIO "queryArrays11" $ t q11
    , goldenCapturedIO "queryArrays12" $ t q12
    , goldenCapturedIO "queryArrays13" $ t q13
    , goldenCapturedIO "queryArrays14" $ t q14
    , goldenCapturedIO "queryArrays15" $ t q15
    , goldenCapturedIO "queryArrays16" $ t q16
    , goldenCapturedIO "queryArrays17" $ t q17
    ]
    where t tc goldFile = do r <- runSMTWith defaultSMTCfg{verbose=True, redirectVerbose=Just goldFile} tc
                             appendFile goldFile ("\n FINAL:" ++ show r ++ "\nDONE!\n")

q1 :: Symbolic (Word8, Word8, Int8)
q1 = do m  :: SArray Word8 Int8 <- sArray "a"

        a1 <- sWord8 "a1"
        a2 <- sWord8 "a2"

        constrain $ a1 ./= a2

        v1 <- sInt8 "v1"

        query $ do constrain $ v1 .== readArray (writeArray m a1 v1) a1
                   _ <- checkSat
                   va1 <- getValue a1
                   va2 <- getValue a2
                   vv1 <- getValue v1
                   return (va1, va2, vv1)

q2 :: Symbolic Word8
q2 = do i <- sWord8 "i"

        setLogic QF_UFBV

        query $ do constrain $ i .== select [0 .. 255] 0 i
                   _ <- checkSat
                   getValue i

q3 :: Symbolic Word8
q3 = do i <- sWord8 "i"

        setLogic QF_UFBV

        query $ do constrain $ i .== select (replicate 256 i) 0 i
                   _ <- checkSat
                   getValue i

q4 :: Symbolic (Word8, Word8)
q4 = do i <- sWord8 "i"
        j <- sWord8 "j"

        setLogic QF_UFBV

        query $ do constrain $ i .== select [0 .. 255] 0 i
                   _ <- checkSat
                   iv <- getValue i
                   constrain $ j .== select [0 .. 255] 0 j
                   constrain $ i .== literal iv
                   constrain $ j .== i+1
                   _ <- checkSat
                   jv <- getValue j
                   return (iv, jv)

q5 :: Symbolic (Maybe (Word8, Int8))
q5 = do m  :: SArray Word8 Int8 <- sArray "a"

        a <- sWord8 "a"
        v <- sInt8  "v"

        query $ do let m2    = writeArray (writeArray m a v) (a+1) (v+1)
                       vRead = readArray  m2 (a+1)

                   constrain $ v + 1 ./= vRead

                   cs <- checkSat

                   case cs of
                     Unsat  -> return Nothing
                     Unk    -> error "solver returned Unknown!"
                     DSat{} -> error "solver returned Delta-satisfiable!"
                     Sat    -> do av <- getValue a
                                  vv <- getValue v
                                  return $ Just (av, vv)

q6 :: Symbolic [Integer]
q6 = do (a :: SArray Integer Integer) <- sArray "a"

        query $ loop (writeArray a 1 1) []

  where loop a sofar = do push 1
                          constrain $ readArray a 1 .== 5
                          cs <- checkSat
                          case cs of
                            Unk    -> error "Unknown"
                            Unsat  -> do pop 1
                                         d <- freshVar $ "d" ++ show (length sofar)
                                         constrain $ d .>= 1 .&& d .< 3
                                         loop (writeArray a 1 (readArray a 1 + d)) (sofar ++ [d])
                            DSat{} -> error "solver returned Delta-satisfiable!"
                            Sat    -> mapM getValue sofar


q7 :: Symbolic (CheckSatResult, CheckSatResult)
q7 = do x :: SArray Integer Integer <- sArray "x"
        let y = writeArray x 0 1

        query $ do constrain $ readArray y 0 .== 2
                   r1 <- checkSat

                   resetAssertions

                   constrain $ readArray y 0 .== 2
                   r2 <- checkSat

                   pure (r1, r2)

q8 :: Symbolic (CheckSatResult, CheckSatResult)
q8 = query $ do x :: SArray Integer Integer <- freshVar "x"
                let y = writeArray x 0 1

                constrain $ readArray y 0 .== 2
                r1 <- checkSat

                resetAssertions

                constrain $ readArray y 0 .== 2
                r2 <- checkSat

                pure (r1, r2)

q9 :: Symbolic CheckSatResult
q9 = do x :: SArray Char Integer <- sArray "x"

        query $ do constrain $ readArray x (literal 'a') .== 5
                   checkSat

q10 :: Symbolic CheckSatResult
q10 = do x :: SArray Integer Char <- sArray "x"

         query $ do constrain $ readArray x 5 .== literal 'a'
                    checkSat

q11 :: Symbolic CheckSatResult
q11 = do x :: SArray Char Char    <- sArray "x"

         query $ do constrain $ readArray x (literal 'a') .== literal 'b'
                    checkSat

q12 :: Symbolic CheckSatResult
q12 = do x :: SArray Rational Integer <- sArray "x"

         query $ do constrain $ readArray x (5 .% 3) .== 5
                    checkSat

q13 :: Symbolic CheckSatResult
q13 = do x :: SArray Integer Rational <- sArray "x"

         query $ do constrain $ readArray x 5 .== 5 .% 3
                    checkSat

q14 :: Symbolic CheckSatResult
q14 = do x :: SArray Rational Rational    <- sArray "x"

         query $ do constrain $ readArray x (5 .% 3) .== 9 .% 8
                    checkSat

q15 :: Symbolic CheckSatResult
q15 = do x :: SArray Rational Char <- sArray "x"

         query $ do constrain $ readArray x (5 .% 3) .== literal 'z'
                    checkSat

q16 :: Symbolic CheckSatResult
q16 = do x :: SArray Char Rational <- sArray "x"

         query $ do constrain $ readArray x (literal 'z') .== 5 .% 3
                    checkSat

q17 :: Symbolic CheckSatResult
q17 = do x :: SArray (Char, Rational) (Rational, Char) <- sArray "x"

         query $ do constrain $ readArray x (literal ('z', 5 % 3)) .== literal (5 % 3, 'z')
                    checkSat
