-----------------------------------------------------------------------------
-- |
-- Module      :  Data.SBV.Utils.Boolean
-- Copyright   :  (c) Levent Erkok
-- License     :  BSD3
-- Maintainer  :  erkokl@gmail.com
-- Stability   :  experimental
-- Portability :  portable
--
-- Abstraction of booleans. Unfortunately, Haskell makes Bool's very hard to
-- work with, by making it a fixed-data type. This is our workaround
-----------------------------------------------------------------------------

module Data.SBV.Utils.Boolean where

infixl 6 <+>       -- xor
infixr 3 &&&, ~&   -- and, nand
infixr 2 |||, ~|   -- or, nor
infixr 1 ==>, <=>  -- implies, iff

-- | The boolean class
-- minimal complete definition: true, bnot, &&&
-- but it's advisable to define false, ||| as well (typically)
class Boolean b where
  true   :: b
  false  :: b
  bnot   :: b -> b
  (&&&)  :: b -> b -> b
  (|||)  :: b -> b -> b
  (~&)   :: b -> b -> b
  (~|)   :: b -> b -> b
  (<+>)  :: b -> b -> b
  (==>)  :: b -> b -> b
  (<=>)  :: b -> b -> b

  -- default definitions
  false   = bnot true
  a ||| b = bnot (bnot a &&& bnot b)
  a ~& b  = bnot (a &&& b)
  a ~| b  = bnot (a ||| b)
  a <+> b = (a &&& bnot b) ||| (bnot a &&& b)
  a <=> b = (a &&& b) ||| (bnot a &&& bnot b)
  a ==> b = bnot a ||| b

bAnd, bOr :: Boolean b => [b] -> b
bAnd = foldr (&&&) true
bOr  = foldr (|||) false

bAny, bAll :: Boolean b => (a -> b) -> [a] -> b
bAll f = bAnd . map f
bAny f = bOr  . map f

fromBool :: Boolean b => Bool -> b
fromBool True  = true
fromBool False = false

instance Boolean Bool where
  true   = True
  false  = False
  bnot   = not
  (&&&)  = (&&)
  (|||)  = (||)
