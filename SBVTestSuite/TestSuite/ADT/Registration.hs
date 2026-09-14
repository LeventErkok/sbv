-----------------------------------------------------------------------------
-- |
-- Module    : TestSuite.ADT.Registration
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Registration of ADT dependencies without incidental uses of their fields.
-----------------------------------------------------------------------------

{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE FlexibleInstances   #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell     #-}
{-# LANGUAGE TypeApplications    #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module TestSuite.ADT.Registration (tests) where

import Data.Proxy (Proxy(..))
import Data.SBV.Control
import Test.Tasty.HUnit (assertEqual)
import Utils.SBVTestFramework

-- | A parameterized leaf whose definition must be discovered from its uses.
newtype RegistrationLeaf a = RegistrationLeaf a deriving (Eq, Ord, Show)

-- | An ADT reference underneath a tuple field.
newtype RegistrationTuple = RegistrationTuple (RegistrationLeaf Word8, Word8) deriving Show

-- | An ADT reference underneath a list field.
newtype RegistrationList = RegistrationList [RegistrationLeaf Word8] deriving Show

-- | An ADT reference underneath a set field.
newtype RegistrationSet = RegistrationSet (RCSet (RegistrationLeaf Word8)) deriving Show

-- | An ADT reference in an array's index type.
newtype RegistrationKey = RegistrationKey (ArrayModel (RegistrationLeaf Word8) Word8) deriving Show

-- | An ADT reference in an array's element type.
newtype RegistrationValue = RegistrationValue (ArrayModel Word8 (RegistrationLeaf Word8)) deriving Show

-- | A synonym must not hide dependencies from the registration traversal.
type RegistrationAlias = ([RegistrationLeaf Word8], Word8)

-- | A field whose container structure is supplied by a type synonym.
newtype RegistrationSynonym = RegistrationSynonym RegistrationAlias deriving Show

-- | Type arguments may themselves contain ADT references behind containers.
newtype RegistrationParameter a = RegistrationParameter (Maybe ([RegistrationLeaf a], a)) deriving Show

-- | Discover dependencies of an ADT that is itself only referenced by name.
newtype RegistrationChain = RegistrationChain RegistrationTuple deriving Show

-- | The root of a mutually recursive group, with a nested reference to its peer.
data RegistrationEven = RegistrationEnd | RegistrationEven (RegistrationOdd, Word8) deriving Show

-- | The return edge of the mutually recursive group.
newtype RegistrationOdd = RegistrationOdd RegistrationEven deriving Show

-- | Generate all schemas without registering any symbolic values in advance.
mkSymbolic [''RegistrationLeaf, ''RegistrationTuple, ''RegistrationList, ''RegistrationSet, ''RegistrationKey, ''RegistrationValue, ''RegistrationSynonym, ''RegistrationParameter, ''RegistrationChain, ''RegistrationEven, ''RegistrationOdd]

-- | Each fresh solver session uses only its root type. In particular, neither
-- literals, field selectors, nor extra inner-type inputs may mask missing schemas.
tests :: TestTree
tests = testGroup "ADT.Registration"
  [ testGroup phase
      [ check interactive "tuple"         (Proxy @RegistrationTuple)
      , check interactive "list"          (Proxy @RegistrationList)
      , check interactive "set"           (Proxy @RegistrationSet)
      , check interactive "array key"     (Proxy @RegistrationKey)
      , check interactive "array value"   (Proxy @RegistrationValue)
      , check interactive "type synonym"  (Proxy @RegistrationSynonym)
      , check interactive "parameter"     (Proxy @(RegistrationParameter Word8))
      , check interactive "transitive"    (Proxy @RegistrationChain)
      , check interactive "mutual root"   (Proxy @RegistrationEven)
      , check interactive "mutual peer"   (Proxy @RegistrationOdd)
      ]
  | (phase, interactive) <- [("symbolic", Nothing), ("query named", Just False), ("query unnamed", Just True)]
  ]
 where check :: forall a. SymVal a => Maybe Bool -> String -> Proxy a -> TestTree
       check interactive testName _ = testCase testName $ do
         result <- runSMT $ case interactive of
           Just anonymous -> query $ do left  <- if anonymous then freshVar_ @a else freshVar @a "left"
                                        right <- if anonymous then freshVar_ @a else freshVar @a "right"
                                        constrain (left ./= right)
                                        checkSat
           Nothing -> do left  <- free "left"  :: Symbolic (SBV a)
                         right <- free "right" :: Symbolic (SBV a)
                         constrain (left ./= right)
                         query checkSat
         assertEqual "Distinct root values must be satisfiable without explicit subfield registration" Sat result
