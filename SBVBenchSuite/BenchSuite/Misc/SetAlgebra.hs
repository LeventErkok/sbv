-----------------------------------------------------------------------------
-- |
-- Module    : BenchSuite.Misc.SetAlgebra
-- Copyright : (c) Jeffrey Young
--                 Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Bench suite for Documentation.SBV.Examples.Misc.SetAlgebra
-----------------------------------------------------------------------------

{-# OPTIONS_GHC -Wall -Werror #-}

{-# LANGUAGE ScopedTypeVariables #-}

module BenchSuite.Misc.SetAlgebra(benchmarks) where

import Data.SBV hiding (complement)
import Data.SBV.Set
import Documentation.SBV.Examples.Misc.SetAlgebra

import BenchSuite.Bench.Bench


-- benchmark suite
benchmarks :: Runner
benchmarks =  rGroup $ fmap (`using` _prove)
              [ run "Commutivity.Union"           commutivityCup
              , run "Commutivity.Intersection"    commutivityCap
              , run "Associativity.Union"         assocCup
              , run "Associativity.Intersection"  assocCap
              , run "Distributivity.Union"        distribCup
              , run "Distributivity.Intersection" distribCap
              , run "Identity.Union"              identCup
              , run "Identity.Intersection"       identCap
              , run "Complement.Union"            compCup
              , run "Complement.Intersection"     compCap
              , run "Complement.Empty"            compEmpty
              , run "Complement.Complement"       compComp
              , run "Complement.Full"             compFull
              , run "Complement.Unique"           compUniq
              , run "Idempotency.Cup"             idempCup
              , run "Idempotency.Cap"             idempCap
              , run "Domination.Cup"              domCup
              , run "Domination.Cap"              domCap
              , run "Absorption.Cup"              absorbCup
              , run "Absorption.Cap"              absorbCap
              , run "Intersection.Difference"     intdiff
              , run "DeMorgans.Cup"               demorgCup
              , run "DeMorgans.Cap"               demorgCap
              , run "InclusionIsPO"               incPo
              , run "SubsetEquality"              subEq
              , run "SubsetEquality.Transitivity" subEqTrans
              , run "JoinMeet.1"                  joinMeet1
              , run "JoinMeet.2"                  joinMeet2
              , run "JoinMeet.3"                  joinMeet3
              , run "JoinMeet.4"                  joinMeet4
              , run "JoinMeet.5"                  joinMeet5
              , run "SubsetChar.Union"            subsetCharCup
              , run "SubsetChar.Intersection"     subsetCharCap
              , run "SubsetChar.Implication"      subsetCharImpl
              , run "SubsetChar.Complement"       subsetCharComp

              , run "RelativeComplements.Union"              relCompCup
              , run "RelativeComplements.Intersection"       relCompCap
              , run "RelativeComplements.UnionInters"        relCompCapCup
              , run "RelativeComplements.InterInters.1"      relCompCapCap
              , run "RelativeComplements.InterInters.2"      relCompCapCap2
              , run "RelativeComplements.UnionUnion"         relCompCupCup
              , run "RelativeComplements.Identity"           relCompIdent
              , run "RelativeComplements.UnitLeft"           relCompUnitL
              , run "RelativeComplements.UnitRight"          relCompUnitR
              , run "RelativeComplements.ComplementIdentity" relCompCompInt
              , run "RelativeComplements.ComplementUnion"    relCompCompUni
              , run "RelativeComplements.CompComp"           relCompComp
              , run "RelativeComplements.CompFull"           relCompFull
              , run "DistributionSubset.Union"               distSubset1
              , run "DistributionSubset.Intersection"        distSubset2
              ]
  where _prove = runner proveWith
        commutivityCup = \(a :: SI) b -> a `union` b .== b `union` a
        commutivityCap = \(a :: SI) b -> a `intersection` b .== b `intersection` a
        assocCup       = \(a :: SI) b c -> a `union` (b `union` c) .== (a `union` b) `union` c
        assocCap       = \(a :: SI) b c -> a `intersection` (b `intersection` c) .== (a `intersection` b) `intersection` c
        distribCup     = \(a :: SI) b c -> a `union` (b `intersection` c) .== (a `union` b) `intersection` (a `union` c)
        distribCap     = \(a :: SI) b c -> a `intersection` (b `union` c) .== (a `intersection` b) `union` (a `intersection` c)
        identCup       = \(a :: SI) -> a `union` empty .== a
        identCap       = \(a :: SI) -> a `intersection` full .== a
        compCup        = \(a :: SI) -> a `union` complement a .== full
        compCap        = \(a :: SI) -> a `intersection` complement a .== empty
        compEmpty      = complement (empty :: SI) .== full
        compComp       = \(a :: SI) -> complement (complement a) .== a
        compFull       = complement (full :: SI) .== empty
        compUniq       = \(a :: SI) b -> a `union` b .== full .&& a `intersection` b .== empty .<=> b .== complement a
        idempCup       = \(a :: SI) -> a `union` a .== a
        idempCap       = \(a :: SI) -> a `intersection` a .== a
        domCup         = \(a :: SI) -> a `union` full .== full
        domCap         = \(a :: SI) -> a `intersection` empty .== empty
        absorbCup      = \(a :: SI) b -> a `union` (a `intersection` b) .== a
        absorbCap      = \(a :: SI) b -> a `intersection` (a `union` b) .== a
        intdiff        = \(a :: SI) b -> a `intersection` b .== a `difference` (a `difference` b)
        demorgCup      = \(a :: SI) b -> complement (a `union` b) .== complement a `intersection` complement b
        demorgCap      = \(a :: SI) b -> complement (a `intersection` b) .== complement a `union` complement b
        incPo          = \(a :: SI) -> a `isSubsetOf` a
        subEq          = \(a :: SI) b -> a `isSubsetOf` b .&& b `isSubsetOf` a .<=> a .== b
        subEqTrans     = \(a :: SI) b c -> a `isSubsetOf` b .&& b `isSubsetOf` c .=> a `isSubsetOf` c
        joinMeet1      = \(a :: SI) b -> a `isSubsetOf` (a `union` b)
        joinMeet2      = \(a :: SI) b c -> a `isSubsetOf` c .&& b `isSubsetOf` c .=> (a `union` b) `isSubsetOf` c
        joinMeet3      = \(a :: SI) b -> (a `intersection` b) `isSubsetOf` a
        joinMeet4      = \(a :: SI) b -> (a `intersection` b) `isSubsetOf` b
        joinMeet5      = \(a :: SI) b c -> c `isSubsetOf` a .&& c `isSubsetOf` b .=> c `isSubsetOf` (a `intersection` b)
        subsetCharCup  = \(a :: SI) b -> a `isSubsetOf` b .<=> a `union` b .== b
        subsetCharCap  = \(a :: SI) b -> a `isSubsetOf` b .<=> a `intersection` b .== a
        subsetCharImpl = \(a :: SI) b -> a `isSubsetOf` b .<=> a `difference` b .== empty
        subsetCharComp = \(a :: SI) b -> a `isSubsetOf` b .<=> complement b `isSubsetOf` complement a
        relCompCup     = \(a :: SI) b c -> c \\ (a `union` b) .== (c \\ a) `intersection` (c \\ b)
        relCompCap     = \(a :: SI) b c -> c \\ (a `intersection` b) .== (c \\ a) `union` (c \\ b)
        relCompCapCup  = \(a :: SI) b c -> c \\ (b \\ a) .== (a `intersection` c) `union` (c \\ b)
        relCompCapCap  = \(a :: SI) b c -> (b \\ a) `intersection` c .== (b `intersection` c) \\ a
        relCompCapCap2 = \(a :: SI) b c -> (b \\ a) `intersection` c .== b `intersection` (c \\ a)
        relCompCupCup  = \(a :: SI) b c -> (b \\ a) `union` c .== (b `union` c) \\ (a \\ c)
        relCompIdent   = \(a :: SI) -> a \\ a .== empty
        relCompUnitL   = \(a :: SI) -> empty \\ a .== empty
        relCompUnitR   = \(a :: SI) -> empty \\ empty .== a
        relCompCompInt = \(a :: SI) b -> b \\ a .== complement a `intersection` b
        relCompCompUni = \(a :: SI) b -> complement (b \\ a) .== a `union` complement b
        relCompComp    = \(a :: SI) -> full \\ a .== complement a
        relCompFull    = \(a :: SI) -> a \\ full .== empty
        distSubset1    = \(a :: SI) b c -> a `isSubsetOf` (b `union` c) .=> a `isSubsetOf` b .&& a `isSubsetOf` c
        distSubset2    = \(a :: SI) b c -> (b `intersection` c) `isSubsetOf` a .=> b `isSubsetOf` a .&& c `isSubsetOf` a
