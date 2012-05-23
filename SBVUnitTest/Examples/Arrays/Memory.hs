-----------------------------------------------------------------------------
-- |
-- Module      :  Examples.Arrays.Memory
-- Copyright   :  (c) Levent Erkok
-- License     :  BSD3
-- Maintainer  :  erkokl@gmail.com
-- Stability   :  experimental
--
-- Simple memory abstraction and properties
-----------------------------------------------------------------------------

module Examples.Arrays.Memory where

import Data.SBV

type Address = SWord32
type Value   = SWord64
type Memory  = SArray Word32 Word64

-- | read-after-write: If you write a value and read it back, you'll get it
raw :: Address -> Value -> Memory -> SBool
raw a v m = readArray (writeArray m a v) a .== v

-- | write-after-write: If you write to the same location twice, then the first one is ignored
waw :: Address -> Value -> Value -> Memory -> SBool
waw a v1 v2 m0 = m2 .== m3
  where m1 = writeArray m0 a v1
        m2 = writeArray m1 a v2
        m3 = writeArray m0 a v2

-- | Two writes to different locations commute, i.e., can be done in any order
wcommutesGood :: (Address, Value) -> (Address, Value) -> Memory -> SBool
wcommutesGood (a, x) (b, y) m = a ./= b ==> wcommutesBad (a, x) (b, y) m

-- | Two writes do not commute if they can be done to the same location
wcommutesBad :: (Address, Value) -> (Address, Value) -> Memory -> SBool
wcommutesBad (a, x) (b, y) m = writeArray (writeArray m a x) b y .== writeArray (writeArray m b y) a x

tests :: IO ()
tests = do print =<< prove raw
           print =<< prove waw
           print =<< prove wcommutesBad
           print =<< prove wcommutesGood
