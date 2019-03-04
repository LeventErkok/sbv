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

cSetAL :: SC
cSetAL = fromList "hello"
-- cSetBL :: SC
-- cSetBL = fromList "there"

cCharA :: SChar
cCharA = literal 'e'

-- The goal is to get rid of the following test vectors, and
-- use the more interesting ones above. Unfortunately,
-- there's a z3 bug in set-model generation that spits
-- out models that we cannot parse. So, we're sticking
-- to really simple examples in some cases here.
cSetA :: SC
cSetA = singleton $ literal 'a'
-- cSetB :: SC
-- cSetB = singleton $ literal 'b'

-- Test suite
tests :: TestTree
tests = testGroup "Basics.Set" [
          goldenCapturedIO "set_uninterp1"  $ ta setE1
        , goldenCapturedIO "set_uninterp2"  $ tq setE2
        , goldenCapturedIO "set_compl1"     $ tq $ templateU   cSetAL        complement
        , goldenCapturedIO "set_union1"     $ tq $ templateB   cSetA  cSetA  union
        , goldenCapturedIO "set_intersect1" $ tq $ templateB   cSetA  cSetA  intersection
        , goldenCapturedIO "set_diff1"      $ tq $ templateB   cSetA  cSetA  difference
        , goldenCapturedIO "set_empty1"     $ tq $ templateUB  cSetAL        isEmpty
        , goldenCapturedIO "set_full1"      $ tq $ templateUB  cSetAL        isFull
        , goldenCapturedIO "set_subset1"    $ tq $ templateBB  cSetA  cSetA  isSubsetOf
        , goldenCapturedIO "set_psubset1"   $ tq $ templateBB  cSetA  cSetA  isProperSubsetOf
        , goldenCapturedIO "set_disj1"      $ tq $ templateBB  cSetA  cSetA  disjoint
        , goldenCapturedIO "set_insert1"    $ tq $ templateBE  cCharA cSetAL insert
        , goldenCapturedIO "set_delete1"    $ tq $ templateBE  cCharA cSetAL delete
        , goldenCapturedIO "set_member1"    $ tq $ templateBEB cCharA cSetAL member
        , goldenCapturedIO "set_notMember1" $ tq $ templateBEB cCharA cSetAL notMember
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

templateU :: SC -> (SC -> SC) -> Symbolic (RC, RC, RC, RC, RC)
templateU is f = do a <- sSet "a"

                    constrain $ a .== is

                    let o1 = f a
                        o2 = f o1
                        o3 = o1 `intersection` a
                        o4 = o1 `union`        a

                    query $ do ensureSat
                               (,,,,) <$> getValue a <*> getValue o1 <*> getValue o2 <*> getValue o3 <*> getValue o4

templateB :: SC -> SC -> (SC -> SC -> SC) -> Symbolic (RC, RC, RC, RC, RC, RC)
templateB is1 is2 f = do a <- sSet "a"
                         b <- sSet "b"

                         constrain $ a .== is1
                         constrain $ b .== is2

                         let o1 =            a `f`            b
                             o2 =            a `f` complement b
                             o3 = complement a `f`            b
                             o4 = complement a `f` complement b

                         query $ do ensureSat
                                    (,,,,,) <$> getValue a <*> getValue b <*> getValue o1 <*> getValue o2 <*> getValue o3 <*> getValue o4

templateUB :: SC -> (SC -> SBool) -> Symbolic (RC, Bool, Bool)
templateUB is f = do a <- sSet "a"

                     constrain $ a .== is

                     let o1 = f a
                         o2 = f (complement a)

                     query $ do ensureSat
                                (,,) <$> getValue a <*> getValue o1 <*> getValue o2

templateBB :: SC -> SC -> (SC -> SC -> SBool) -> Symbolic (RC, RC, Bool, Bool, Bool, Bool)
templateBB is1 is2 f = do a <- sSet "a"
                          b <- sSet "b"

                          constrain $ a .== is1
                          constrain $ b .== is2

                          let o1 =            a `f`            b
                              o2 =            a `f` complement b
                              o3 = complement a `f`            b
                              o4 = complement a `f` complement b

                          query $ do ensureSat
                                     (,,,,,) <$> getValue a <*> getValue b <*> getValue o1 <*> getValue o2 <*> getValue o3 <*> getValue o4

templateBE :: SChar -> SC -> (SChar -> SC -> SC) -> Symbolic (Char, RC, RC, RC)
templateBE ic is f = do a <- sChar "a"
                        b <- sSet  "b"

                        constrain $ a .== ic
                        constrain $ b .== is

                        let o1 = a `f`            b
                            o2 = a `f` complement b

                        query $ do ensureSat
                                   (,,,) <$> getValue a <*> getValue b <*> getValue o1 <*> getValue o2

templateBEB :: SChar -> SC -> (SChar -> SC -> SBool) -> Symbolic (Char, RC, Bool, Bool)
templateBEB ic is f = do a <- sChar "a"
                         b <- sSet  "b"

                         constrain $ a .== ic
                         constrain $ b .== is

                         let o1 = a `f`            b
                             o2 = a `f` complement b

                         query $ do ensureSat
                                    (,,,) <$> getValue a <*> getValue b <*> getValue o1 <*> getValue o2

{-# ANN module ("HLint: ignore Reduce duplication" :: String) #-}
