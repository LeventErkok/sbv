{- (c) Copyright Levent Erkok. All rights reserved.
--
-- The sbv library is distributed with the BSD3 license. See the LICENSE file
-- in the distribution for details.
-}

module Data.SBV.Examples.Arrays.Memory where

import Data.SBV
import Data.SBV.Utils.SBVTest

type Address = SWord32
type Value   = SWord64
type Memory  = SArray Word32 Word64

raw :: Address -> Value -> Memory -> SBool
raw a v m = readArray (writeArray m a v) a .== v

waw :: Address -> Value -> Value -> Memory -> SBool
waw a v1 v2 m0 = m2 .== m3
  where m1 = writeArray m0 a v1
        m2 = writeArray m1 a v2
        m3 = writeArray m0 a v2

wcommutesGood :: (Address, Value) -> (Address, Value) -> Memory -> SBool
wcommutesGood (a, x) (b, y) m = a ./= b ==> wcommutesBad (a, x) (b, y) m

wcommutesBad :: (Address, Value) -> (Address, Value) -> Memory -> SBool
wcommutesBad (a, x) (b, y) m = writeArray (writeArray m a x) b y .== writeArray (writeArray m b y) a x

tests :: IO ()
tests = do print =<< prove raw
           print =<< prove waw
           print =<< prove wcommutesBad
           print =<< prove wcommutesGood


testSuite :: SBVTestSuite
testSuite = mkTestSuite $ \_ -> test [
     "memory-raw"           ~: assert       =<< isTheorem raw
   , "memory-waw"           ~: assert       =<< isTheorem waw
   , "memory-wcommute-bad"  ~: assert . not =<< isTheorem wcommutesBad
   , "memory-wcommute-good" ~: assert       =<< isTheorem wcommutesGood
   ]
