-----------------------------------------------------------------------------
-- |
-- Module    : TestSuite.Basics.Tuple
-- Copyright : (c) Joel Burget
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Test tuples.
-----------------------------------------------------------------------------

{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE DeriveAnyClass      #-}
{-# LANGUAGE DeriveDataTypeable  #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving  #-}
{-# LANGUAGE TemplateHaskell     #-}
{-# LANGUAGE TypeApplications    #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module TestSuite.Basics.Tuple (tests)  where

import Prelude hiding ((!!))

import Data.SBV.Control
import Data.SBV.List ((!!), (.:))
import Data.SBV.Tuple

import qualified Data.SBV.List as L

import Utils.SBVTestFramework

data E = A | B | C
mkSymbolicEnumeration ''E

__unused :: SE
__unused = error "stop GHC from complaining unused names" sA sB sC

-- Test suite
tests :: TestTree
tests = testGroup "Basics.Tuple" [
          goldenCapturedIO "tuple_swap"       $ t tupleSwapSat
        , goldenCapturedIO "tuple_twoTwo"     $ t twoTwoTuples
        , goldenCapturedIO "tuple_nested"     $ t nested
        , goldenCapturedIO "tuple_list"       $ t list
        , goldenCapturedIO "tuple_enum"       $ t enum
        , goldenCapturedIO "tuple_unit"       $ t unit
        , goldenCapturedIO "tuple_makePair"   $ t makePair
        , goldenCapturedIO "tuple_unequal"    $ t unequal
        ]
    where t tc goldFile = do r <- runSMTWith defaultSMTCfg{verbose=True, redirectVerbose=Just goldFile} tc
                             appendFile goldFile ("\n FINAL: " ++ show r ++ "\nDONE!\n")

tupleSwapSat :: Symbolic ((Integer, Integer, Integer), (Integer, Integer, Integer))
tupleSwapSat = do
  [abx, bay] <- sTuples @(Integer, Integer, Integer) ["abx", "bay"]
  constrain $ abx^._1 .== bay^._2
  constrain $ abx^._2 .== bay^._1
  constrain $ abx^._1 .== 1
  constrain $ abx^._2 .== 2
  constrain $ abx^._3 .== 3
  constrain $ bay^._3 .== 4
  query $ do _ <- checkSat
             (,) <$> getValue abx <*> getValue bay

twoTwoTuples :: Symbolic ((Integer, String), (Char, Word8))
twoTwoTuples = do
  ab <- sTuple @(Integer, String) "ab"
  cd <- sTuple @(Char,    Word8)  "cd"
  constrain $ ab^._1 .== 1
  constrain $ cd^._1 .== literal 'c'
  query $ do _ <- checkSat
             (,) <$> getValue ab <*> getValue cd

nested :: Symbolic ((Integer, (String, Char)), Word8)
nested = do
  abcd <- sTuple @((Integer, (String, Char)), Word8) "abcd"
  constrain $     abcd^._1^._1 .== 1
  constrain $ abcd^._1^._2^._1 .== literal "foo"
  constrain $ abcd^._1^._2^._2 .== literal 'c'
  constrain $         abcd^._2 .== 0
  query $ do _ <- checkSat
             getValue abcd

list :: Symbolic [(Integer, [(Integer, String)])]
list = do
  lst <- sList @(Integer, [(Integer, String)]) "lst"

  constrain $ (lst !! 0)^._1 .== 2
  constrain $ (((lst !! 1)^._2) !! 0)^._2 .== literal "foo"
  constrain $ L.length lst .== 4
  constrain $ L.length ((lst !! 1)^._2) .== 5
  constrain $ L.length ((lst !! 2)^._2) .== 0

  constrain $ lst .== literal [(2,[]), (1,[(3,"foo"), (0,"bar"), (-1,"baz"), (-2,"quux"), (-3,"enough")]), (-4,[]), (-5,[])]

  query $ do _ <- checkSat
             getValue lst

enum :: Symbolic ([(E, [Bool])], (Word8, (E, Char, Float)))
enum = do
   vTup1 :: SList (E, [Bool]) <- sList "v1"
   q <- sBool "q"
   constrain $ sNot q
   constrain $ (vTup1 !! 1)^._2 .== sTrue .: q .: L.nil
   constrain $ L.length vTup1 .== 3

   case untuple (vTup1 !! 2)  of
     (e, b) -> do constrain $ e .== sC
                  constrain $ L.length b .== 6
                  constrain $ b !! 4 .== sTrue

   query $ do
     vTup2 :: STuple Word8 (E, Char, Float) <- freshVar "v2"
     constrain $ vTup2 .== literal (5, (C, 'A', 8.12))

     constrain $ vTup1 .== literal [(B, []), (A, [True, False]), (C, [False, False, False, False, True, False])]

     _ <- checkSat
     (,) <$> getValue vTup1 <*> getValue vTup2

unit :: Symbolic ()
unit = do
  x <- sTuple @() "x"
  y <- sTuple @() "y"
  constrain $ x .== y

makePair :: Symbolic ()
makePair = do
  [x, y] <- sIntegers ["x", "y"]
  let xy = tuple (x, y)
  constrain $ xy^._1 + xy^._2 .== 0

type TI = STuple Integer Integer

unequal :: Symbolic ()
unequal = do
   x :: TI <- free_
   y :: TI <- free_
   -- force unsat; we're simply testing we can generate the tuple inequality here
   constrain $ x .< y
   constrain $ x .> y

   query $ do cs <- checkSat
              case cs of
                Unsat -> return ()
                _     -> error "did not expect this!"

{- HLint ignore module "Use ."        -}
{- HLint ignore module "Redundant ^." -}
