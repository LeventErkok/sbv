-----------------------------------------------------------------------------
-- |
-- Module      :  TestSuite.Queries.FreshVars
-- Copyright   :  (c) Levent Erkok
-- License     :  BSD3
-- Maintainer  :  erkokl@gmail.com
-- Stability   :  experimental
--
-- Testing fresh-vars in query mode
-----------------------------------------------------------------------------

{-# LANGUAGE TemplateHaskell     #-}
{-# LANGUAGE StandaloneDeriving  #-}
{-# LANGUAGE DeriveDataTypeable  #-}
{-# LANGUAGE DeriveAnyClass      #-}
{-# LANGUAGE ScopedTypeVariables #-}

module TestSuite.Queries.FreshVars (tests)  where

import Data.SBV.Control

import Utils.SBVTestFramework

data BinOp  = Plus | Minus | Times
mkSymbolicEnumeration ''BinOp

-- Test suite
tests :: TestTree
tests =
  testGroup "Basics.Query"
    [ goldenCapturedIO "freshVars" testQuery
    ]

testQuery :: FilePath -> IO ()
testQuery rf = do r <- runSMTWith defaultSMTCfg{verbose=True, redirectVerbose=Just rf} fv
                  appendFile rf ("\n FINAL:" ++ show (SatResult r) ++ "\nDONE!\n")

type SBinOp = SBV BinOp

fv :: Symbolic SMTResult
fv = do a <- sInteger "a"

        constrain $ a .== 0

        query $ do vBool    :: SBool    <- freshVar  "vBool"
                   vWord8   :: SWord8   <- freshVar  "vWord8"
                   vWord16  :: SWord16  <- freshVar_
                   vWord32  :: SWord32  <- freshVar_
                   vWord64  :: SWord64  <- freshVar  "vWord64"
                   vInt8    :: SInt8    <- freshVar  "vInt8"
                   vInt16   :: SInt16   <- freshVar_
                   vInt32   :: SInt32   <- freshVar_
                   vInt64   :: SInt64   <- freshVar  "vInt64"
                   vFloat   :: SFloat   <- freshVar  "vFloat"
                   vDouble  :: SDouble  <- freshVar_
                   vReal    :: SReal    <- freshVar_
                   vInteger :: SInteger <- freshVar  "vInteger"
                   vBinOp   :: SBinOp   <- freshVar  "vBinOp"

                   constrain   vBool
                   constrain $ vWord8   .== 1
                   constrain $ vWord16  .== 2
                   constrain $ vWord32  .== 3
                   constrain $ vWord64  .== 4
                   constrain $ vInt8    .== 5
                   constrain $ vInt16   .== 6
                   constrain $ vInt32   .== 7
                   constrain $ vInt64   .== 8
                   constrain $ vFloat   .== 9
                   constrain $ vDouble  .== 10
                   constrain $ vReal    .== 11
                   constrain $ vInteger .== 12
                   constrain $ vBinOp   .== literal Plus

                   vSArray  :: SArray    Integer Integer <- freshArray "vSArray" Nothing
                   vFArray  :: SFunArray Bool    Char    <- freshArray "vFArray" Nothing
                   vi1                                   <- freshVar "i1"
                   vi2                                   <- freshVar "i2"
                   constrain $ readArray vSArray vi1 .== 2
                   constrain $ readArray vFArray vi2 .== literal 'a'

                   viSArray  :: SArray    Integer Integer <- freshArray "viSArray" (Just (literal 42))
                   viFArray  :: SFunArray Bool    Char    <- freshArray "viFArray" (Just (literal 'X'))
                   mustBe42                               <- freshVar "mustBe42"
                   mustBeX                                <- freshVar "mustBeX"

                   constrain $ readArray viSArray 96    .== mustBe42
                   constrain $ readArray viFArray false .== mustBeX

                   cs <- checkSat
                   case cs of
                     Sat -> do aVal        <- getValue a
                               vBoolVal    <- getValue vBool
                               vWord8Val   <- getValue vWord8
                               vWord16Val  <- getValue vWord16
                               vWord32Val  <- getValue vWord32
                               vWord64Val  <- getValue vWord64
                               vInt8Val    <- getValue vInt8
                               vInt16Val   <- getValue vInt16
                               vInt32Val   <- getValue vInt32
                               vInt64Val   <- getValue vInt64
                               vFloatVal   <- getValue vFloat
                               vDoubleVal  <- getValue vDouble
                               vRealVal    <- getValue vReal
                               vIntegerVal <- getValue vInteger
                               vBinOpVal   <- getValue vBinOp
                               vi1Val      <- getValue vi1
                               vi2Val      <- getValue vi2
                               mustBe42Val <- getValue mustBe42
                               mustBeXVal  <- getValue mustBeX

                               mkSMTResult [ a          |-> aVal
                                           , vBool      |-> vBoolVal
                                           , vWord8     |-> vWord8Val
                                           , vWord16    |-> vWord16Val
                                           , vWord32    |-> vWord32Val
                                           , vWord64    |-> vWord64Val
                                           , vInt8      |-> vInt8Val
                                           , vInt16     |-> vInt16Val
                                           , vInt32     |-> vInt32Val
                                           , vInt64     |-> vInt64Val
                                           , vFloat     |-> vFloatVal
                                           , vDouble    |-> vDoubleVal
                                           , vReal      |-> vRealVal
                                           , vInteger   |-> vIntegerVal
                                           , vBinOp     |-> vBinOpVal
                                           , vi1        |-> vi1Val
                                           , vi2        |-> vi2Val
                                           , mustBe42   |-> mustBe42Val
                                           , mustBeX    |-> mustBeXVal
                                           ]
                     _   -> error "didn't expect non-Sat here!"
