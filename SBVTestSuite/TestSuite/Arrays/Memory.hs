-----------------------------------------------------------------------------
-- |
-- Module    : TestSuite.Arrays.Memory
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Test suite for Examples.Arrays.Memory
-----------------------------------------------------------------------------

{-# LANGUAGE Rank2Types #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module TestSuite.Arrays.Memory(tests) where

import Utils.SBVTestFramework

type AddressBase = Word32
type ValueBase   = Word64
type Address     = SBV AddressBase
type Value       = SBV ValueBase
type Memory      = SArray AddressBase ValueBase

-- | read-after-write: If you write a value and read it back, you'll get it
raw :: Address -> Value -> Memory -> SBool
raw a v m = readArray (writeArray m a v) a .== v

-- | if read from a place you didn't write to, the result doesn't change
rawd :: Address -> Address -> Value -> Memory -> SBool
rawd a b v m = a ./= b .=> readArray (writeArray m a v) b .== readArray m b

-- | write-after-write: If you write to the same location twice, then the first one is ignored
waw :: Address -> Value -> Value -> Memory -> Address -> SBool
waw a v1 v2 m0 i = readArray m2 i .== readArray m3 i
  where m1 = writeArray m0 a v1
        m2 = writeArray m1 a v2
        m3 = writeArray m0 a v2

-- | Two writes to different locations commute, i.e., can be done in any order
wcommutesGood :: (Address, Value) -> (Address, Value) -> Memory -> Address -> SBool
wcommutesGood (a, x) (b, y) m i = a ./= b .=> wcommutesBad (a, x) (b, y) m i

-- | Two writes do not commute if they can be done to the same location
wcommutesBad :: (Address, Value) -> (Address, Value) -> Memory -> Address -> SBool
wcommutesBad (a, x) (b, y) m i = readArray m0 i .== readArray m1 i
   where m0 = writeArray (writeArray m a x) b y
         m1 = writeArray (writeArray m b y) a x

-- | Extensionality
extensionality :: Memory -> Memory -> Predicate
extensionality m1 m2 = pure $ quantifiedBool $ \(Exists i) ->
                          (readArray m1 i ./= readArray m2 i) .|| m1 .== m2

-- | Extensionality, second variant. Expressible for both kinds of arrays.
extensionality2 :: Memory -> Memory -> Address -> Predicate
extensionality2 m1 m2 i = pure $ quantifiedBool $ \(Exists j) ->
                             (readArray m1 j ./= readArray m2 j) .|| readArray m1 i .== readArray m2 i

-- | Merge, using memory equality to check result
mergeEq :: SBool -> Memory -> Memory -> SBool
mergeEq b m1 m2 = ite b m1 m2 .== ite (sNot b) m2 m1

-- | Merge, using extensionality to check result
mergeExt :: SBool -> Memory -> Memory -> Address -> SBool
mergeExt b m1 m2 i = readArray (ite b m1 m2) i .== readArray (ite (sNot b) m2 m1) i

-- | Merge semantics
mergeSem :: SBool -> Memory -> Memory -> Address -> SBool
mergeSem b m1 m2 i = readArray (ite b m1 m2) i .== ite b (readArray m1 i) (readArray m2 i)

-- | Merge semantics 2, but make sure to populate the array so merge does something interesting
mergeSem2 :: SBool -> Memory -> Memory -> (Address, Value) -> (Address, Value) -> Address -> SBool
mergeSem2 b m1 m2 (a1, v1) (a2, v2) i = readArray (ite b m1' m2') i .== ite b (readArray m1' i) (readArray m2' i)
   where m1' = writeArray (writeArray m1 a1 v1) a2 v2
         m2' = writeArray (writeArray m2 a1 v1) a2 v2

-- | Merge is done correctly:
mergeSem3 :: SBool -> Memory -> (Address, Value) -> (Address, Value) -> SBool
mergeSem3 b m (a1, v1) (a2, v2) = readArray (ite b m1 m2) a1 .== ite b (readArray m1 a1) (readArray m2 a1)
  where m1 = writeArray m a1 v1
        m2 = writeArray m a2 v2

-- | Another merge check
mergeSem4 :: SBool -> Memory -> Address -> Address -> SBool
mergeSem4 b m a1 a2 = readArray m3 a2 .== ite b (readArray m a2) 3
  where m1 = writeArray m a1 1
        m2 = writeArray (writeArray m a1 2) a2 3
        m3 = ite b m1 m2

tests :: TestTree
tests =
  testGroup "Arrays.Memory"
    [ testCase "raw_SArray"              $ assertIsThm   (raw             :: Address -> Value -> Memory -> SBool)
    , testCase "rawd_SArray"             $ assertIsThm   (rawd            :: Address -> Address -> Value -> Memory -> SBool)
    , testCase "waw_SArray"              $ assertIsThm   (waw             :: Address -> Value -> Value -> Memory -> Address -> SBool)
    , testCase "wcommute-good_SArray"    $ assertIsThm   (wcommutesGood   :: (Address, Value) -> (Address, Value) -> Memory -> Address -> SBool)
    , testCase "wcommute-bad_SArray"     $ assertIsntThm (wcommutesBad    :: (Address, Value) -> (Address, Value) -> Memory -> Address -> SBool)
    , testCase "ext_SArray"              $ assertIsThm   (extensionality  :: Memory -> Memory -> Predicate)
    , testCase "ext2_SArray"             $ assertIsThm   (extensionality2 :: Memory -> Memory -> Address -> Predicate)
    , testCase "mergeEq_SArray"          $ assertIsThm   (mergeEq         :: SBool -> Memory -> Memory -> SBool)
    , testCase "mergeExt_SArray"         $ assertIsThm   (mergeExt        :: SBool -> Memory -> Memory -> Address -> SBool)
    , testCase "mergeSem_SArray"         $ assertIsThm   (mergeSem        :: SBool -> Memory -> Memory -> Address -> SBool)
    , testCase "mergeSem2_SArray"        $ assertIsThm   (mergeSem2       :: SBool -> Memory -> Memory -> (Address, Value) -> (Address, Value) -> Address -> SBool)
    , testCase "mergeSem3_SArray"        $ assertIsThm   (mergeSem3       :: SBool -> Memory -> (Address, Value) -> (Address, Value) -> SBool)
    , testCase "mergeSem4_SArray"        $ assertIsntThm (mergeSem4       :: SBool -> Memory -> Address -> Address -> SBool)
    ]
