-----------------------------------------------------------------------------
-- |
-- Module      :  TestSuite.Uninterpreted.Axioms
-- Copyright   :  (c) Levent Erkok
-- License     :  BSD3
-- Maintainer  :  erkokl@gmail.com
-- Stability   :  experimental
--
-- Test suite for basic axioms and uninterpreted functions
-----------------------------------------------------------------------------

{-# LANGUAGE DeriveDataTypeable #-}
module TestSuite.Uninterpreted.Axioms(testSuite) where

import Data.SBV
import SBVTest
import Data.Generics

-- Test suite
testSuite :: SBVTestSuite
testSuite = mkTestSuite $ \_ -> test [
  "unint-axioms" ~: assert =<< isThm p0
 ]

-- Example provided by Thomas DuBuisson:
data Bitstring = Bitstring () deriving (Eq, Ord, Data, Typeable, Read, Show)
instance SymWord Bitstring
instance HasKind Bitstring
type SBitstring = SBV Bitstring

a :: SBitstring -> SBool
a = uninterpret "a"

e :: SBitstring -> SBitstring -> SBitstring
e = uninterpret "e"

axE :: [String]
axE = [ "(assert (forall ((p Bitstring) (k Bitstring))"
      , "         (=> (and (a k) (a p)) (a (e k p)))))"
      ]

p0 :: Symbolic SBool
p0 = do
    p <- free "p" :: Symbolic SBitstring
    k <- free "k" :: Symbolic SBitstring
    addAxiom "axE" axE
    constrain $ a p
    constrain $ a k
    return $ a (e k p)
