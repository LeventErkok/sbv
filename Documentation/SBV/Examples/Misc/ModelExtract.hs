-----------------------------------------------------------------------------
-- |
-- Module    : Documentation.SBV.Examples.Misc.ModelExtract
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Demonstrates use of programmatic model extraction. When programming with
-- SBV, we typically use `sat`/`allSat` calls to compute models automatically.
-- In more advanced uses, however, the user might want to use programmable
-- extraction features to do fancier programming. We demonstrate some of
-- these utilities here.
-----------------------------------------------------------------------------

{-# OPTIONS_GHC -Wall -Werror #-}

module Documentation.SBV.Examples.Misc.ModelExtract where

import Data.SBV

-- | A simple function to generate a new integer value, that is not in the
-- given set of values. We also require the value to be non-negative
outside :: [Integer] -> IO SatResult
outside disallow = sat $ do x <- sInteger "x"
                            let notEq i = constrain $ x ./= literal i
                            mapM_ notEq disallow
                            return $ x .>= 0

-- | We now use "outside" repeatedly to generate 10 integers, such that we not only disallow
-- previously generated elements, but also any value that differs from previous solutions
-- by less than 5.  Here, we use the `getModelValue` function. We could have also extracted the dictionary
-- via `getModelDictionary` and did fancier programming as well, as necessary. We have:
--
-- >>> genVals
-- [45,40,35,30,25,20,15,10,5,0]
genVals :: IO [Integer]
genVals = go [] []
  where go _ model
         | length model >= 10 = return model
        go disallow model
          = do res <- outside disallow
               -- Look up the value of "x" in the generated model
               -- Note that we simply get an integer here; but any
               -- SBV known type would be OK as well.
               case "x" `getModelValue` res of
                 Just c -> go ([c-4 .. c+4] ++ disallow) (c : model)
                 _      -> return model
