-----------------------------------------------------------------------------
-- |
-- Module    : TestSuite.Char.Char
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Testing SChar constraints (as modeled thru strings in SMTLib)
-----------------------------------------------------------------------------

{-# LANGUAGE ScopedTypeVariables #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module TestSuite.Char.Char(tests) where

import Utils.SBVTestFramework
import Data.SBV.Control

import qualified Data.SBV.List   as L
import qualified Data.SBV.Set    as S
import qualified Data.SBV.Maybe  as M
import qualified Data.SBV.Either as E
import Data.SBV.Tuple

tests :: TestTree
tests =
  testGroup "Char" [
      goldenCapturedIO "charConstr00" $ \rf -> checkWith rf t00
    , goldenCapturedIO "charConstr01" $ \rf -> checkWith rf t01
    , goldenCapturedIO "charConstr02" $ \rf -> checkWith rf t02
    , goldenCapturedIO "charConstr03" $ \rf -> checkWith rf t03
    , goldenCapturedIO "charConstr04" $ \rf -> checkWith rf t04
    , goldenCapturedIO "charConstr05" $ \rf -> checkWith rf t05
    , goldenCapturedIO "charConstr06" $ \rf -> checkWith rf t06
    , goldenCapturedIO "charConstr07" $ \rf -> checkWith rf t07
    , goldenCapturedIO "charConstr08" $ \rf -> checkWith rf t08
    , goldenCapturedIO "charConstr09" $ \rf -> checkWith rf t09
    , goldenCapturedIO "charConstr10" $ \rf -> checkWith rf t10
    , goldenCapturedIO "charConstr11" $ \rf -> checkWith rf t11
    ]

checkWith :: FilePath -> Symbolic () -> IO ()
checkWith rf props = runSMTWith z3{verbose=True, redirectVerbose = Just rf} $ do
        _ <- props
        query $ do cs <- checkSat
                   case cs of
                     Unsat  -> io $ appendFile rf "\nUNSAT"
                     DSat{} -> io $ appendFile rf "\nDSAT"
                     Sat{}  -> getModel         >>= \m -> io $ appendFile rf $ "\nMODEL: "   ++ show m ++ "\nDONE."
                     Unk    -> getUnknownReason >>= \r -> io $ appendFile rf $ "\nUNKNOWN: " ++ show r ++ "\nDONE."

cf :: SInteger -> SChar
cf  = uninterpret "cf"

cf3 :: SInteger -> STuple3 Char Char Char
cf3 = uninterpret "cf3"

t00 :: Symbolic ()
t00 = do x <- sChar "x"
         constrain $ x ./= literal 'A'

t01 :: Symbolic ()
t01 = constrain $ cf 4 ./= literal 'A'

t02 :: Symbolic ()
t02 = constrain $ cf3 4 ./= literal ('A', 'B', 'C')

t03 :: Symbolic ()
t03 = do x::SEither Char Char <- free "x"
         constrain $ x ./= E.sLeft (literal 'A')

t04 :: Symbolic ()
t04 = do x::SEither Integer Char <- free "x"
         constrain $ x ./= E.sRight (literal 'A')

t05 :: Symbolic ()
t05 = do x::SEither Char Integer <- free "x"
         constrain $ x ./= E.sLeft (literal 'A')

t06 :: Symbolic ()
t06 = do x::SEither Char (Either Char Integer) <- free "x"
         constrain $ x ./= E.sLeft (literal 'A')

t07 :: Symbolic ()
t07 = do x::SMaybe Char <- free "x"
         constrain $ M.isJust x .&& x ./= M.sJust (literal 'A')

t08 :: Symbolic ()
t08 = do x :: SSet Char <- free "x"
         constrain $ S.member (literal 'A') x .&& sNot (S.member (literal 'B') x)

t09 :: Symbolic ()
t09 = do x :: SList ((Char, Char), [Integer]) <- free "x"
         constrain $ L.length x .== 1

t10 :: Symbolic ()
t10 = do x :: SList ((Char, Char), [Integer]) <- free "x"
         constrain $ L.length x .== 1
         constrain $ (x L.!! 0)^._1^._1 .== literal 'B'

cf4 :: SInteger -> SChar -> SList ((Char, Char), [Integer])
cf4 = uninterpret "cf4"

t11 :: Symbolic ()
t11 = do x <- sInteger "x"
         c <- sChar "c"
         constrain $ L.length (cf4 x c) .== 1

{- HLint ignore module "Use ."        -}
{- HLint ignore module "Redundant ^." -}
