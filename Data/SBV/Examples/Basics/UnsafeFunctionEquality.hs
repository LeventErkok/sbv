{- (c) Copyright Levent Erkok. All rights reserved.
--
-- The sbv library is distributed with the BSD3 license. See the LICENSE file
-- in the distribution for details.
-}

{-# OPTIONS_GHC -fno-warn-orphans #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FlexibleInstances #-}

module Data.SBV.Examples.Basics.UnsafeFunctionEquality where

import System.IO.Unsafe
import Data.SBV
import Data.SBV.Utils.SBVTest

-- I claim this is actually safe, similar to trusted FFI calls..
instance Equality (a -> b) => Eq (a -> b) where
  f == g = unsafePerformIO $ do
              r <- f === g
              case r of
                ThmResult (Unsatisfiable _) -> return True
                ThmResult (Satisfiable _ _) -> return False
                _                           ->  error $ "Cannot decide function equality!"


-- tests

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


t :: [Bool]
t =  [ f11 == f11
     , f12 == f12
     , f21 == f21
     , f22 == f22
     , f31 == f31
     , f32 == f32
     , f33 == f33
     , f33 /= f33
     ]

-- Test suite
testSuite :: SBVTestSuite
testSuite = mkTestSuite $ \_ -> test [
   "functionEq-1" ~: assert       $ f11 == f11
 , "functionEq-2" ~: assert       $ f12 == f12
 , "functionEq-3" ~: assert       $ f22 == f22
 , "functionEq-4" ~: assert       $ f31 == f31
 , "functionEq-5" ~: assert       $ f32 == f32
 , "functionEq-6" ~: assert       $ f33 == f33
 , "functionEq-7" ~: assert . not $ f11 /= f11
 ]
