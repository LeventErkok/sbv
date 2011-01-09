{- (c) Copyright Levent Erkok. All rights reserved.
--
-- The sbv library is distributed with the BSD3 license. See the LICENSE file
-- in the distribution for details.
-}

module Data.SBV.Examples.Basics.Higher where

import Data.SBV
import Data.SBV.Utils.SBVTest

type B = SWord8

f11 :: B -> B
f11 x = x

f12 :: B -> (B, B)
f12 x = (x, x)

f21 :: (B, B) -> B
f21 (x, y) = x + y

f22 :: (B, B) -> (B, B)
f22 (x, y) = (x, y)

f31 :: B -> B -> B
f31 x y = x + y

f32 :: B -> B -> (B, B)
f32 x y = (x, y)

f33 :: B -> B -> B -> (B, B, B)
f33 x y z = (x, y, z)


t :: IO [ThmResult]
t = sequence $ [
       f11 === f11
     , f12 === f12
     , f21 === f21
     , f22 === f22
     , f31 === f31
     , f32 === f32
     , f33 === f33
     ]

-- Test suite
testSuite :: SBVTestSuite
testSuite = mkTestSuite $ \goldCheck -> test [
   "higher-1"  ~: (f11 === f11)   `goldCheck` "higher-1.gold"
 , "higher-2"  ~: (f12 === f12)   `goldCheck` "higher-2.gold"
 , "higher-3"  ~: (f21 === f21)   `goldCheck` "higher-3.gold"
 , "higher-4"  ~: (f22 === f22)   `goldCheck` "higher-4.gold"
 , "higher-5"  ~: (f31 === f31)   `goldCheck` "higher-5.gold"
 , "higher-6"  ~: (f32 === f32)   `goldCheck` "higher-6.gold"
 , "higher-7"  ~: (f33 === f33)   `goldCheck` "higher-7.gold"
 , "higher-8"  ~: double          `goldCheck` "higher-8.gold"
 , "higher-9"  ~: onlyFailsFor128 `goldCheck` "higher-9.gold"
 ]
 where double          = (2*) === (\x -> x+(x::SWord8))
       onlyFailsFor128 = (2*) === (\x -> ite (x .== 128) 5 (x+(x::SWord8)))

