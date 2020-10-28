-----------------------------------------------------------------------------
-- |
-- Module    : TestSuite.Uninterpreted.Uninterpreted
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-----------------------------------------------------------------------------

{-# LANGUAGE DeriveAnyClass     #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell    #-}
{-# OPTIONS_GHC -Wall -Werror   #-}

module TestSuite.Uninterpreted.Uninterpreted(tests) where

import Utils.SBVTestFramework

data Q
mkUninterpretedSort ''Q

-- Test suite
tests :: TestTree
tests =
  testGroup "Uninterpreted.Uninterpreted"
    [ testCase         "uninterpreted-0"  $ assertIsThm   p0
    , testCase         "uninterpreted-1"  $ assertIsThm   p1
    , testCase         "uninterpreted-2"  $ assertIsntThm p2
    , goldenCapturedIO "uninterpreted-3"  $ t p3 satWith
    , goldenCapturedIO "uninterpreted-3a" $ t p3 allSatWith
    , goldenCapturedIO "uninterpreted-4"  $ t p4 satWith
    , goldenCapturedIO "uninterpreted-4a" $ t p4 allSatWith
    ]
  where t tc chk goldFile = do r <- chk defaultSMTCfg{verbose = True, redirectVerbose = Just goldFile} tc
                               appendFile goldFile ("\n FINAL:" ++ show r ++ "\nDONE!\n")

f :: SInt8 -> SWord32
f = uninterpret "f"

g :: SInt8 -> SWord16 -> SWord32
g = uninterpret "g"

p0 :: SInt8 -> SInt8 -> SBool
p0 x y   = x .== y .=> f x .== f y      -- OK

p1 :: SInt8 -> SWord16 -> SWord16 -> SBool
p1 x y z = y .== z .=> g x y .== g x z  -- OK

p2 :: SInt8 -> SWord16 -> SWord16 -> SBool
p2 x y z = y .== z .=> g x y .== f x    -- Not true


a, b :: SBool
a = sym "p"
b = sym "q"

p3 :: SBool
p3 = a .|| b

c, d :: SQ
c = sym "c"
d = sym "d"

p4 :: SBool
p4 = c ./= d
