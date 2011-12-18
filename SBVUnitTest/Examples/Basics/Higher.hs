-----------------------------------------------------------------------------
-- |
-- Module      :  Examples.Basics.Higher
-- Copyright   :  (c) Levent Erkok
-- License     :  BSD3
-- Maintainer  :  erkokl@gmail.com
-- Stability   :  experimental
-- Portability :  portable
--
-- Testing function equality
-----------------------------------------------------------------------------

module Examples.Basics.Higher where

import Data.SBV

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
t = sequence [
       f11 === f11
     , f12 === f12
     , f21 === f21
     , f22 === f22
     , f31 === f31
     , f32 === f32
     , f33 === f33
     ]
