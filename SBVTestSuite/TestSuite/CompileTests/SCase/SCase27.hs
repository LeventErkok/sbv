{-# LANGUAGE TemplateHaskell #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module T where

import Data.SBV

-- don't allow multiple accessors
data A = A1 { u :: Integer }
       | B1 { u :: Integer, s :: String}
       | C1

mkSymbolic ''A
