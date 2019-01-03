{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications    #-}

module Documentation.SBV.Examples.Misc.Tuple where

import Data.SBV
import Data.SBV.Tuple

example :: IO SatResult
example = sat $ do
  [ab, cd] <- sTuples @(Integer, Integer, Integer) ["ab", "cd"]
  constrain $ field1 ab .== field2 cd
  constrain $ field2 ab .== field1 cd
