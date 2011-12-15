-----------------------------------------------------------------------------
-- |
-- Module      :  Data.SBV.BitVectors.GenTest
-- Copyright   :  (c) Levent Erkok
-- License     :  BSD3
-- Maintainer  :  erkokl@gmail.com
-- Stability   :  experimental
-- Portability :  portable
--
-- Test generation from symbolic programs
-----------------------------------------------------------------------------

module Data.SBV.BitVectors.GenTest (genTest) where

import Data.SBV.BitVectors.Data

-- | Generate a set of concrete test values from a symbolic program. The output
-- can be rendered as test vectors in different languages as necessary.
genTest :: Outputtable a => Int -> Symbolic a -> IO [([CW], [CW])]
genTest n m = sequence [tc | _ <- [1 .. n]]
  where tc = do (_, Result _ tvals _ _ cs _ _ _ _ _ os) <- runSymbolic' QuickCheck (m >>= output)
                let cval o = case o `lookup` cs of
                               Nothing -> error "Cannot quick-check in the presence of uninterpeted constants!"
                               Just s  -> s
                return (map snd tvals, map cval os)
