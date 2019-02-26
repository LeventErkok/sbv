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

import Data.SBV.RegExp (RegExpMatchable, match, identifier)

import Data.SBV.Control

import Utils.SBVTestFramework hiding (complement)

data E = A | B | C
mkSymbolicEnumeration ''E

isIdentifier :: RegExpMatchable a => a -> SBool
isIdentifier = (`match` identifier)

sIdentifier :: String -> Symbolic SChar
sIdentifier nm = do n <- sChar nm
                    constrain $ isIdentifier n
                    return n

type SC = SSet  Char
type RC = RCSet Char

-- Test suite
tests :: TestTree
tests = testGroup "Basics.Set" [
          goldenCapturedIO "set_uninterp1"  $ ta setE1
        , goldenCapturedIO "set_uninterp2"  $ tq setE2
        , goldenCapturedIO "set_compl1"     $ tq $ templateU complement
        , goldenCapturedIO "set_union1"     $ tq $ templateB union
        , goldenCapturedIO "set_intersect1" $ tq $ templateB intersection
        , goldenCapturedIO "set_diff1"      $ tq $ templateB difference
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

templateU :: (SC -> SC) -> Symbolic (Char, RC, RC, RC, RC)
templateU f = do a <- sIdentifier "a"

                 let sa = singleton a

                     o1 = f sa
                     o2 = f o1
                     o3 = o1 `intersection` sa
                     o4 = o1 `union`        sa

                 query $ do ensureSat
                            (,,,,) <$> getValue a <*> getValue o1 <*> getValue o2 <*> getValue o3 <*> getValue o4

templateB :: (SC -> SC -> SC) -> Symbolic (Char, Char, RC, RC, RC, RC)
templateB f = do a <- sIdentifier "a"
                 b <- sIdentifier "b"

                 let sa = singleton a
                     sb = singleton b

                     o1 =            sa `f`            sb
                     o2 =            sa `f` complement sb
                     o3 = complement sa `f`            sb
                     o4 = complement sa `f` complement sb

                 query $ do ensureSat
                            (,,,,,) <$> getValue a <*> getValue b <*> getValue o1 <*> getValue o2 <*> getValue o3 <*> getValue o4
