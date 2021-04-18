-----------------------------------------------------------------------------
-- |
-- Module    : TestSuite.Queries.FreshVars
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Testing fresh-vars in query mode
-----------------------------------------------------------------------------

{-# LANGUAGE DeriveAnyClass      #-}
{-# LANGUAGE DeriveDataTypeable  #-}
{-# LANGUAGE OverloadedLists     #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving  #-}
{-# LANGUAGE TemplateHaskell     #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module TestSuite.Queries.FreshVars (tests)  where

import Data.SBV.Control

import Utils.SBVTestFramework

data BinOp  = Plus | Minus | Times
mkSymbolicEnumeration ''BinOp

_unused :: a
_unused = error "stop GHC from complaining unused names" sPlus sMinus sTimes

-- Test suite
tests :: TestTree
tests =
  testGroup "Basics.Query"
    [ goldenCapturedIO "freshVars" testQuery
    ]

testQuery :: FilePath -> IO ()
testQuery rf = do r <- runSMTWith defaultSMTCfg{verbose=True, redirectVerbose=Just rf} fv
                  appendFile rf ("\n FINAL:" ++ show (SatResult r) ++ "\nDONE!\n")

fv :: Symbolic SMTResult
fv = do a <- sInteger "a"

        constrain $ a .== 0

        setOption $ OptionKeyword ":pp.max_depth"      ["4294967295"]
        setOption $ OptionKeyword ":pp.min_alias_size" ["4294967295"]

        query $ do vBool    :: SBool           <- freshVar  "vBool"
                   vWord8   :: SWord8          <- freshVar  "vWord8"
                   vWord16  :: SWord16         <- freshVar_
                   vWord32  :: SWord32         <- freshVar_
                   vWord64  :: SWord64         <- freshVar  "vWord64"
                   vInt8    :: SInt8           <- freshVar  "vInt8"
                   vInt16   :: SInt16          <- freshVar_
                   vInt32   :: SInt32          <- freshVar_
                   vInt64   :: SInt64          <- freshVar  "vInt64"
                   vFloat   :: SFloat          <- freshVar  "vFloat"
                   vDouble  :: SDouble         <- freshVar_
                   vReal    :: SReal           <- freshVar_
                   vInteger :: SInteger        <- freshVar  "vInteger"
                   vBinOp   :: SBinOp          <- freshVar  "vBinOp"
                   vQuad    :: SFPQuad         <- freshVar  "vQuad"
                   wQuad    :: SFPQuad         <- freshVar  "wQuad"

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
                   constrain $ vBinOp   .== sPlus

                   constrain $ vQuad .== wQuad
                   constrain $ sNot $ vQuad `fpIsEqualObject` wQuad
                   constrain $ fpIsPositive vQuad

                   vSArray  :: SArray    Integer Integer <- freshArray "vSArray" Nothing
                   vi1                                   <- freshVar "i1"
                   vi2                                   <- freshVar "i2"
                   constrain $ readArray vSArray vi1 .== 2

                   viSArray  :: SArray    Integer Integer <- freshArray "viSArray" (Just (literal 42))
                   mustBe42                               <- freshVar "mustBe42"

                   constrain $ readArray viSArray 96     .== mustBe42
                   constrain $ vi1 .== 1
                   constrain $ sNot vi2

                   vString  :: SString         <- freshVar  "vString"
                   vList1   :: SList Integer   <- freshVar  "vList1"
                   vList2   :: SList [Integer] <- freshVar  "vList2"
                   vList3   :: SList Word8     <- freshVar  "vList3"
                   vList4   :: SList [Word16]  <- freshVar  "vList4"

                   constrain $ vString  .== "hello"
                   constrain $ vList1   .== [1,2,3,4]
                   constrain $ vList2   .== [[1,2,3], [4,5,6,7]]
                   constrain $ vList3   .== [1,2]
                   constrain $ vList4   .== [[1,2,3],[],[4,5,6]]

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
                               vStringVal  <- getValue vString
                               vList1Val   <- getValue vList1
                               vList2Val   <- getValue vList2
                               vList3Val   <- getValue vList3
                               vList4Val   <- getValue vList4
                               vQuadVal    <- getValue vQuad
                               wQuadVal    <- getValue wQuad

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
                                           , vString    |-> vStringVal
                                           , vList1     |-> vList1Val
                                           , vList2     |-> vList2Val
                                           , vList3     |-> vList3Val
                                           , vList4     |-> vList4Val
                                           , vQuad      |-> vQuadVal
                                           , wQuad      |-> wQuadVal
                                           ]
                     _   -> error "didn't expect non-Sat here!"
