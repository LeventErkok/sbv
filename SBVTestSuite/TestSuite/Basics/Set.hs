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

{-# OPTIONS_GHC -Wall -Werror #-}

module TestSuite.Basics.Set (tests)  where

import Data.SBV hiding (complement)
import Data.SBV.Set

import Data.SBV.Control

import Data.SBV.Tuple

import Utils.SBVTestFramework hiding (complement)

data E = A | B | C
mkSymbolicEnumeration ''E

__unused :: SE
__unused = error "stop GHC from complaining unused names" sA sB sC

type SC = SSet  Integer
type RC = RCSet Integer

cSetAL :: SC
cSetAL = fromList [1,2,3,3,4]

cIntA :: SInteger
cIntA = literal 2

cSetA :: SC
cSetA = singleton $ literal 0

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
        , goldenCapturedIO "set_insert1"    $ tq $ templateBE  cIntA  cSetAL insert
        , goldenCapturedIO "set_delete1"    $ tq $ templateBE  cIntA  cSetAL delete
        , goldenCapturedIO "set_member1"    $ tq $ templateBEB cIntA  cSetAL member
        , goldenCapturedIO "set_notMember1" $ tq $ templateBEB cIntA  cSetAL notMember
        , goldenCapturedIO "set_tupleSet"   $ ta setOfTuples
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

templateBE :: SInteger -> SC -> (SInteger -> SC -> SC) -> Symbolic (Integer, RC, RC, RC)
templateBE ic is f = do a <- sInteger "a"
                        b <- sSet     "b"

                        constrain $ a .== ic
                        constrain $ b .== is

                        let o1 = a `f`            b
                            o2 = a `f` complement b

                        query $ do ensureSat
                                   (,,,) <$> getValue a <*> getValue b <*> getValue o1 <*> getValue o2

templateBEB :: SInteger -> SC -> (SInteger -> SC -> SBool) -> Symbolic (Integer, RC, Bool, Bool)
templateBEB ic is f = do a <- sInteger "a"
                         b <- sSet     "b"

                         constrain $ a .== ic
                         constrain $ b .== is

                         let o1 = a `f`            b
                             o2 = a `f` complement b

                         query $ do ensureSat
                                    (,,,) <$> getValue a <*> getValue b <*> getValue o1 <*> getValue o2

setOfTuples :: SMTConfig -> IO SatResult
setOfTuples cfg = satWith cfg $ do
    let x = tuple (empty :: SSet Bool, empty :: SSet Bool)
    y <- free_
    return $ x ./= y

{- HLint ignore module "Reduce duplication" -}
