{-# LANGUAGE TemplateHaskell   #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module T where

import Data.SBV

-- Testing bad fields
data A = F (A -> Bool)
       | I Integer

mkSymbolic [''A]
