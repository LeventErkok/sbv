{- (c) Copyright Levent Erkok. All rights reserved.
--
-- The sbv library is distributed with the BSD3 license. See the LICENSE file
-- in the distribution for details.
-}

module Data.SBV.BitVectors.Bit where

import Data.Bits
import Control.Parallel.Strategies(NFData(..))

data Bit = Zero | One
         deriving (Eq, Ord)

instance Show Bit where
  show Zero = "0"
  show One  = "1"

instance Num Bit where
  Zero + a = a
  One  + _ = One
  Zero * _ = Zero
  One  * a = a
  negate One  = Zero
  negate Zero = One
  abs = id
  signum Zero = 0
  signum One  = 1
  fromInteger 0 = Zero
  fromInteger _ = One

instance Bits Bit where
  a .&. b  = a * b 
  a .|. b  = a + b
  Zero `xor` a = a
  One  `xor` a = negate a
  complement = negate
  bitSize _ = 1
  isSigned _ = False
  a `shiftL` n
    | n == 0   = a
    | True     = Zero
  shiftR = shiftL
  a `rotateL` _ = a
  rotateR = rotateR

bool2Bit :: Bool -> Bit
bool2Bit False = Zero
bool2Bit True  = One

bit2Bool :: Bit -> Bool
bit2Bool Zero = False
bit2Bool One  = True

instance NFData Bit
