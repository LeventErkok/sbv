{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE QuasiQuotes       #-}
{-# LANGUAGE TemplateHaskell   #-}
{-# LANGUAGE TypeApplications  #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module T where

import Data.SBV

-- Testing constructor/type name conflct
data A = A Integer
       | B Float
       | C A A

mkSymbolic [''A]

t :: SA -> SA
t a = [sCase|A a of
         A u     -> sA (u+1)
         B f     -> sB (f+2)
         C a1 a2 -> sC (t a1) (t a2)
      |]
