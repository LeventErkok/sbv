{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TemplateHaskell   #-}
{-# LANGUAGE TypeApplications  #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module T where

import Data.SBV

data A = A1 { u :: Integer }
       | B1 { s :: String, k :: Float }
       | C1

mkSymbolic ''A
