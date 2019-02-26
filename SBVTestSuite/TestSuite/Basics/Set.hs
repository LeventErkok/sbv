-----------------------------------------------------------------------------
-- |
-- Module    : TestSuite.Basics.Set
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Test sets.
-----------------------------------------------------------------------------

{-# LANGUAGE DeriveAnyClass      #-}
{-# LANGUAGE DeriveDataTypeable  #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving  #-}
{-# LANGUAGE TemplateHaskell     #-}

module TestSuite.Basics.Set (tests)  where

import Data.SBV hiding (complement)
import Data.SBV.Set

import Data.SBV.Control

import Utils.SBVTestFramework hiding (complement)

data E = A | B | C
mkSymbolicEnumeration ''E

type SC = SSet  Char
type RC = RCSet Char

-- I'd love to have these more complicated sets. But
-- there's a z3 bug in set-model generation that spits
-- out models that we cannot parse. So, we're sticking
-- to really simple examples here. In particular, I'd
-- at least like the sets to be different, but even
-- that's enough to trip z3.
cSetA, cSetB :: SC
cSetA = singleton $ literal 'a'
cSetB = singleton $ literal 'a'

-- Test suite
tests :: TestTree
tests = testGroup "Basics.Set" [
          goldenCapturedIO "set_uninterp1"  $ ta setE1
        , goldenCapturedIO "set_uninterp2"  $ tq setE2
        , goldenCapturedIO "set_compl1"     $ tq $ templateU  complement
        , goldenCapturedIO "set_union1"     $ tq $ templateB  union
        , goldenCapturedIO "set_intersect1" $ tq $ templateB  intersection
        , goldenCapturedIO "set_diff1"      $ tq $ templateB  difference
        , goldenCapturedIO "set_empty1"     $ tq $ templateUB isEmpty
        , goldenCapturedIO "set_full1"      $ tq $ templateUB isFull
        , goldenCapturedIO "set_subset1"    $ tq $ templateBB isSubsetOf
        , goldenCapturedIO "set_psubset1"   $ tq $ templateBB isProperSubsetOf
        , goldenCapturedIO "set_disj1"      $ tq $ templateBB disjoint
        , goldenCapturedIO "set_member1"    $ tq $ templateBE member
        , goldenCapturedIO "set_notMember1" $ tq $ templateBE notMember
        ]
    where ta tc goldFile    = record goldFile =<< tc defaultSMTCfg{verbose=True, redirectVerbose=Just goldFile}
          tq tc goldFile    = record goldFile =<< runSMTWith defaultSMTCfg{verbose=True, redirectVerbose=Just goldFile} tc
          record goldFile r = appendFile goldFile ("\nFINAL:\n" ++ show r ++ "\nDONE!\n")

setE1 :: SMTConfig -> IO AllSatResult
setE1 cfg = allSatWith cfg $ \(_ :: SSet E) -> sTrue

setE2 :: Symbolic (RCSet E, RCSet E)
setE2 = do a :: SSet E <- sSet "a"
           b :: SSet E <- sSet "b"

           constrain $ distinct [a, b]

           query $ do ensureSat
                      (,) <$> getValue a <*> getValue b

templateU :: (SC -> SC) -> Symbolic (RC, RC, RC, RC, RC)
templateU f = do a <- sSet "a"

                 constrain $ a .== cSetA

                 let o1 = f a
                     o2 = f o1
                     o3 = o1 `intersection` a
                     o4 = o1 `union`        a

                 query $ do ensureSat
                            (,,,,) <$> getValue a <*> getValue o1 <*> getValue o2 <*> getValue o3 <*> getValue o4

templateB :: (SC -> SC -> SC) -> Symbolic (RC, RC, RC, RC, RC, RC)
templateB f = do a <- sSet "a"
                 b <- sSet "b"

                 constrain $ a .== cSetA
                 constrain $ b .== cSetB

                 let o1 =            a `f`            b
                     o2 =            a `f` complement b
                     o3 = complement a `f`            b
                     o4 = complement a `f` complement b

                 query $ do ensureSat
                            (,,,,,) <$> getValue a <*> getValue b <*> getValue o1 <*> getValue o2 <*> getValue o3 <*> getValue o4

templateUB :: (SC -> SBool) -> Symbolic (RC, Bool, Bool)
templateUB f = do a <- sSet "a"

                  constrain $ a .== cSetA

                  let o1 = f a
                      o2 = f (complement a)

                  query $ do ensureSat
                             (,,) <$> getValue a <*> getValue o1 <*> getValue o2

templateBB :: (SC -> SC -> SBool) -> Symbolic (RC, RC, Bool, Bool, Bool, Bool)
templateBB f = do a <- sSet "a"
                  b <- sSet "b"

                  constrain $ a .== cSetA
                  constrain $ b .== cSetB

                  let o1 =            a `f`            b
                      o2 =            a `f` complement b
                      o3 = complement a `f`            b
                      o4 = complement a `f` complement b

                  query $ do ensureSat
                             (,,,,,) <$> getValue a <*> getValue b <*> getValue o1 <*> getValue o2 <*> getValue o3 <*> getValue o4

templateBE :: (SChar -> SC -> SBool) -> Symbolic (Char, RC, Bool, Bool)
templateBE f = do a <- sChar "a"
                  b <- sSet  "b"

                  constrain $ a .== literal 'a'
                  constrain $ b .== cSetB

                  let o1 = a `f`            b
                      o2 = a `f` complement b

                  query $ do ensureSat
                             (,,,) <$> getValue a <*> getValue b <*> getValue o1 <*> getValue o2

{-# ANN module ("HLint: ignore Reduce duplication" :: String) #-}
