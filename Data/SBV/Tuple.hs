-----------------------------------------------------------------------------
-- |
-- Module    : Data.SBV.Tuple
-- Copyright : (c) Joel Burget
--                 Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Accessing symbolic tuple fields and deconstruction.
-----------------------------------------------------------------------------

{-# LANGUAGE DataKinds              #-}
{-# LANGUAGE FlexibleContexts       #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE KindSignatures         #-}
{-# LANGUAGE Rank2Types             #-}
{-# LANGUAGE ScopedTypeVariables    #-}
{-# LANGUAGE TypeApplications       #-}

{-# OPTIONS_GHC -Wall -Werror -fno-warn-orphans #-}

module Data.SBV.Tuple (
  -- * Symbolic field access
    (^.), _1, _2, _3, _4, _5, _6, _7, _8
  -- * Tupling and untupling
  , tuple, untuple
  -- * Swapping, only for 2-tuples
  , swap
  ) where

import GHC.TypeLits

import Data.SBV.Core.Data
import Data.SBV.Core.Symbolic
import Data.SBV.Core.Model

-- $setup
-- >>> -- For doctest purposes only:
-- >>> :set -XTypeApplications
-- >>> import Data.SBV

-- | Field access, inspired by the lens library. This is merely reverse
-- application, but allows us to write things like @(1, 2)^._1@ which is
-- likely to be familiar to most Haskell programmers out there. Note that
-- this is precisely equivalent to @_1 (1, 2)@, but perhaps it reads a little
-- nicer.
(^.) :: a -> (a -> b) -> b
t ^. f = f t
infixl 8 ^.

-- | Swap the elements of a 2-tuple
swap :: (SymVal a, SymVal b) => STuple a b -> STuple b a
swap t = tuple (b, a)
  where (a, b) = untuple t

-- | Dynamic interface to exporting tuples, this function is not
-- exported on purpose; use it only via the field functions '_1', '_2', etc.
symbolicFieldAccess :: (SymVal a, HasKind tup) => Int -> SBV tup -> SBV a
symbolicFieldAccess i tup
  | 1 > i || i > lks
  = bad $ "Index is out of bounds, " ++ show i ++ " is outside [1," ++ show lks ++ "]"
  | SBV (SVal kval (Left v)) <- tup
  = case cvVal v of
      CTuple vs | kval      /= ktup -> bad $ "Kind/value mismatch: "      ++ show kval
                | length vs /= lks  -> bad $ "Value has fewer elements: " ++ show (CV kval (CTuple vs))
                | True              -> literal $ fromCV $ CV kElem (vs !! (i-1))
      _                             -> bad $ "Kind/value mismatch: " ++ show v
  | True
  = symAccess
  where ktup = kindOf tup

        (lks, eks) = case ktup of
                       KTuple ks -> (length ks, ks)
                       _         -> bad "Was expecting to receive a tuple!"

        kElem = eks !! (i-1)

        bad :: String -> a
        bad problem = error $ unlines [ "*** Data.SBV.field: Impossible happened"
                                      , "***   Accessing element: " ++ show i
                                      , "***   Argument kind    : " ++ show ktup
                                      , "***   Problem          : " ++ problem
                                      , "*** Please report this as a bug!"
                                      ]

        symAccess :: SBV a
        symAccess = SBV $ SVal kElem $ Right $ cache y
          where y st = do sv <- svToSV st $ unSBV tup
                          newExpr st kElem (SBVApp (TupleAccess i lks) [sv])

-- | Field labels
data Label (l :: Symbol) = Get

-- | The class 'HasField' captures the notion that a type has a certain field
class (SymVal elt, HasKind tup) => HasField l elt tup | l tup -> elt where
  field :: Label l -> SBV tup -> SBV elt

instance (HasKind a, HasKind b                                                                  , SymVal a) => HasField "_1" a (a, b)                   where field _ = symbolicFieldAccess 1
instance (HasKind a, HasKind b, HasKind c                                                       , SymVal a) => HasField "_1" a (a, b, c)                where field _ = symbolicFieldAccess 1
instance (HasKind a, HasKind b, HasKind c, HasKind d                                            , SymVal a) => HasField "_1" a (a, b, c, d)             where field _ = symbolicFieldAccess 1
instance (HasKind a, HasKind b, HasKind c, HasKind d, HasKind e                                 , SymVal a) => HasField "_1" a (a, b, c, d, e)          where field _ = symbolicFieldAccess 1
instance (HasKind a, HasKind b, HasKind c, HasKind d, HasKind e, HasKind f                      , SymVal a) => HasField "_1" a (a, b, c, d, e, f)       where field _ = symbolicFieldAccess 1
instance (HasKind a, HasKind b, HasKind c, HasKind d, HasKind e, HasKind f, HasKind g           , SymVal a) => HasField "_1" a (a, b, c, d, e, f, g)    where field _ = symbolicFieldAccess 1
instance (HasKind a, HasKind b, HasKind c, HasKind d, HasKind e, HasKind f, HasKind g, HasKind h, SymVal a) => HasField "_1" a (a, b, c, d, e, f, g, h) where field _ = symbolicFieldAccess 1

instance (HasKind a, HasKind b                                                                  , SymVal b) => HasField "_2" b (a, b)                   where field _ = symbolicFieldAccess 2
instance (HasKind a, HasKind b, HasKind c                                                       , SymVal b) => HasField "_2" b (a, b, c)                where field _ = symbolicFieldAccess 2
instance (HasKind a, HasKind b, HasKind c, HasKind d                                            , SymVal b) => HasField "_2" b (a, b, c, d)             where field _ = symbolicFieldAccess 2
instance (HasKind a, HasKind b, HasKind c, HasKind d, HasKind e                                 , SymVal b) => HasField "_2" b (a, b, c, d, e)          where field _ = symbolicFieldAccess 2
instance (HasKind a, HasKind b, HasKind c, HasKind d, HasKind e, HasKind f                      , SymVal b) => HasField "_2" b (a, b, c, d, e, f)       where field _ = symbolicFieldAccess 2
instance (HasKind a, HasKind b, HasKind c, HasKind d, HasKind e, HasKind f, HasKind g           , SymVal b) => HasField "_2" b (a, b, c, d, e, f, g)    where field _ = symbolicFieldAccess 2
instance (HasKind a, HasKind b, HasKind c, HasKind d, HasKind e, HasKind f, HasKind g, HasKind h, SymVal b) => HasField "_2" b (a, b, c, d, e, f, g, h) where field _ = symbolicFieldAccess 2

instance (HasKind a, HasKind b, HasKind c                                                       , SymVal c) => HasField "_3" c (a, b, c)                where field _ = symbolicFieldAccess 3
instance (HasKind a, HasKind b, HasKind c, HasKind d                                            , SymVal c) => HasField "_3" c (a, b, c, d)             where field _ = symbolicFieldAccess 3
instance (HasKind a, HasKind b, HasKind c, HasKind d, HasKind e                                 , SymVal c) => HasField "_3" c (a, b, c, d, e)          where field _ = symbolicFieldAccess 3
instance (HasKind a, HasKind b, HasKind c, HasKind d, HasKind e, HasKind f                      , SymVal c) => HasField "_3" c (a, b, c, d, e, f)       where field _ = symbolicFieldAccess 3
instance (HasKind a, HasKind b, HasKind c, HasKind d, HasKind e, HasKind f, HasKind g           , SymVal c) => HasField "_3" c (a, b, c, d, e, f, g)    where field _ = symbolicFieldAccess 3
instance (HasKind a, HasKind b, HasKind c, HasKind d, HasKind e, HasKind f, HasKind g, HasKind h, SymVal c) => HasField "_3" c (a, b, c, d, e, f, g, h) where field _ = symbolicFieldAccess 3

instance (HasKind a, HasKind b, HasKind c, HasKind d                                            , SymVal d) => HasField "_4" d (a, b, c, d)             where field _ = symbolicFieldAccess 4
instance (HasKind a, HasKind b, HasKind c, HasKind d, HasKind e                                 , SymVal d) => HasField "_4" d (a, b, c, d, e)          where field _ = symbolicFieldAccess 4
instance (HasKind a, HasKind b, HasKind c, HasKind d, HasKind e, HasKind f                      , SymVal d) => HasField "_4" d (a, b, c, d, e, f)       where field _ = symbolicFieldAccess 4
instance (HasKind a, HasKind b, HasKind c, HasKind d, HasKind e, HasKind f, HasKind g           , SymVal d) => HasField "_4" d (a, b, c, d, e, f, g)    where field _ = symbolicFieldAccess 4
instance (HasKind a, HasKind b, HasKind c, HasKind d, HasKind e, HasKind f, HasKind g, HasKind h, SymVal d) => HasField "_4" d (a, b, c, d, e, f, g, h) where field _ = symbolicFieldAccess 4

instance (HasKind a, HasKind b, HasKind c, HasKind d, HasKind e                                 , SymVal e) => HasField "_5" e (a, b, c, d, e)          where field _ = symbolicFieldAccess 5
instance (HasKind a, HasKind b, HasKind c, HasKind d, HasKind e, HasKind f                      , SymVal e) => HasField "_5" e (a, b, c, d, e, f)       where field _ = symbolicFieldAccess 5
instance (HasKind a, HasKind b, HasKind c, HasKind d, HasKind e, HasKind f, HasKind g           , SymVal e) => HasField "_5" e (a, b, c, d, e, f, g)    where field _ = symbolicFieldAccess 5
instance (HasKind a, HasKind b, HasKind c, HasKind d, HasKind e, HasKind f, HasKind g, HasKind h, SymVal e) => HasField "_5" e (a, b, c, d, e, f, g, h) where field _ = symbolicFieldAccess 5

instance (HasKind a, HasKind b, HasKind c, HasKind d, HasKind e, HasKind f                      , SymVal f) => HasField "_6" f (a, b, c, d, e, f)       where field _ = symbolicFieldAccess 6
instance (HasKind a, HasKind b, HasKind c, HasKind d, HasKind e, HasKind f, HasKind g           , SymVal f) => HasField "_6" f (a, b, c, d, e, f, g)    where field _ = symbolicFieldAccess 6
instance (HasKind a, HasKind b, HasKind c, HasKind d, HasKind e, HasKind f, HasKind g, HasKind h, SymVal f) => HasField "_6" f (a, b, c, d, e, f, g, h) where field _ = symbolicFieldAccess 6

instance (HasKind a, HasKind b, HasKind c, HasKind d, HasKind e, HasKind f, HasKind g           , SymVal g) => HasField "_7" g (a, b, c, d, e, f, g)    where field _ = symbolicFieldAccess 7
instance (HasKind a, HasKind b, HasKind c, HasKind d, HasKind e, HasKind f, HasKind g, HasKind h, SymVal g) => HasField "_7" g (a, b, c, d, e, f, g, h) where field _ = symbolicFieldAccess 7

instance (HasKind a, HasKind b, HasKind c, HasKind d, HasKind e, HasKind f, HasKind g, HasKind h, SymVal h) => HasField "_8" h (a, b, c, d, e, f, g, h) where field _ = symbolicFieldAccess 8

-- | Access the 1st element of an @STupleN@, @2 <= N <= 8@. Also see '^.'.
_1 :: HasField "_1" b a => SBV a -> SBV b
_1 = field (Get @"_1")

-- | Access the 2nd element of an @STupleN@, @2 <= N <= 8@. Also see '^.'.
_2 :: HasField "_2" b a => SBV a -> SBV b
_2 = field (Get @"_2")

-- | Access the 3rd element of an @STupleN@, @3 <= N <= 8@. Also see '^.'.
_3 :: HasField "_3" b a => SBV a -> SBV b
_3 = field (Get @"_3")

-- | Access the 4th element of an @STupleN@, @4 <= N <= 8@. Also see '^.'.
_4 :: HasField "_4" b a => SBV a -> SBV b
_4 = field (Get @"_4")

-- | Access the 5th element of an @STupleN@, @5 <= N <= 8@. Also see '^.'.
_5 :: HasField "_5" b a => SBV a -> SBV b
_5 = field (Get @"_5")

-- | Access the 6th element of an @STupleN@, @6 <= N <= 8@. Also see '^.'.
_6 :: HasField "_6" b a => SBV a -> SBV b
_6 = field (Get @"_6")

-- | Access the 7th element of an @STupleN@, @7 <= N <= 8@. Also see '^.'.
_7 :: HasField "_7" b a => SBV a -> SBV b
_7 = field (Get @"_7")

-- | Access the 8th element of an @STupleN@, @8 <= N <= 8@. Also see '^.'.
_8 :: HasField "_8" b a => SBV a -> SBV b
_8 = field (Get @"_8")

-- | Constructing a tuple from its parts and deconstructing back.
class Tuple tup a | a -> tup, tup -> a where
  -- | Deconstruct a tuple, getting its constituent parts apart. Forms an
  -- isomorphism pair with 'tuple':
  --
  -- >>> prove $ \p -> tuple @(Integer, Bool, (String, Char)) (untuple p) .== p
  -- Q.E.D.
  untuple :: SBV tup -> a

  -- | Constructing a tuple from its parts. Forms an isomorphism pair with 'untuple':
  --
  -- >>> prove $ \p -> untuple @(Integer, Bool, (String, Char)) (tuple p) .== p
  -- Q.E.D.
  tuple   :: a -> SBV tup

instance (SymVal a, SymVal b) => Tuple (a, b) (SBV a, SBV b) where
  untuple p = (p^._1, p^._2)

  tuple p@(sa, sb)
    | Just a <- unliteral sa, Just b <- unliteral sb
    = literal (a, b)
    | True
    = SBV $ SVal k $ Right $ cache res
    where k      = kindOf p
          res st = do asv <- sbvToSV st sa
                      bsv <- sbvToSV st sb
                      newExpr st k (SBVApp (TupleConstructor 2) [asv, bsv])

instance (SymVal a, SymVal b, SymVal c)
      => Tuple (a, b, c) (SBV a, SBV b, SBV c) where
  untuple p = (p^._1, p^._2, p^._3)

  tuple p@(sa, sb, sc)
    | Just a <- unliteral sa, Just b <- unliteral sb, Just c <- unliteral sc
    = literal (a, b, c)
    | True
    = SBV $ SVal k $ Right $ cache res
    where k      = kindOf p
          res st = do asv <- sbvToSV st sa
                      bsv <- sbvToSV st sb
                      csv <- sbvToSV st sc
                      newExpr st k (SBVApp (TupleConstructor 3) [asv, bsv, csv])

instance (SymVal a, SymVal b, SymVal c, SymVal d)
      => Tuple (a, b, c, d) (SBV a, SBV b, SBV c, SBV d) where
  untuple p = (p^._1, p^._2, p^._3, p^._4)

  tuple p@(sa, sb, sc, sd)
    | Just a <- unliteral sa, Just b <- unliteral sb, Just c <- unliteral sc, Just d <- unliteral sd
    = literal (a, b, c, d)
    | True
    = SBV $ SVal k $ Right $ cache res
    where k      = kindOf p
          res st = do asv <- sbvToSV st sa
                      bsv <- sbvToSV st sb
                      csv <- sbvToSV st sc
                      dsv <- sbvToSV st sd
                      newExpr st k (SBVApp (TupleConstructor 4) [asv, bsv, csv, dsv])

instance (SymVal a, SymVal b, SymVal c, SymVal d, SymVal e)
      => Tuple (a, b, c, d, e) (SBV a, SBV b, SBV c, SBV d, SBV e) where
  untuple p = (p^._1, p^._2, p^._3, p^._4, p^._5)

  tuple p@(sa, sb, sc, sd, se)
    | Just a <- unliteral sa, Just b <- unliteral sb, Just c <- unliteral sc, Just d <- unliteral sd, Just e <- unliteral se
    = literal (a, b, c, d, e)
    | True
    = SBV $ SVal k $ Right $ cache res
    where k      = kindOf p
          res st = do asv <- sbvToSV st sa
                      bsv <- sbvToSV st sb
                      csv <- sbvToSV st sc
                      dsv <- sbvToSV st sd
                      esv <- sbvToSV st se
                      newExpr st k (SBVApp (TupleConstructor 5) [asv, bsv, csv, dsv, esv])

instance (SymVal a, SymVal b, SymVal c, SymVal d, SymVal e, SymVal f)
      => Tuple (a, b, c, d, e, f) (SBV a, SBV b, SBV c, SBV d, SBV e, SBV f) where
  untuple p = (p^._1, p^._2, p^._3, p^._4, p^._5, p^._6)

  tuple p@(sa, sb, sc, sd, se, sf)
    | Just a <- unliteral sa, Just b <- unliteral sb, Just c <- unliteral sc, Just d <- unliteral sd, Just e <- unliteral se, Just f <- unliteral sf
    = literal (a, b, c, d, e, f)
    | True
    = SBV $ SVal k $ Right $ cache res
    where k      = kindOf p
          res st = do asv <- sbvToSV st sa
                      bsv <- sbvToSV st sb
                      csv <- sbvToSV st sc
                      dsv <- sbvToSV st sd
                      esv <- sbvToSV st se
                      fsv <- sbvToSV st sf
                      newExpr st k (SBVApp (TupleConstructor 6) [asv, bsv, csv, dsv, esv, fsv])

instance (SymVal a, SymVal b, SymVal c, SymVal d, SymVal e, SymVal f, SymVal g)
      => Tuple (a, b, c, d, e, f, g) (SBV a, SBV b, SBV c, SBV d, SBV e, SBV f, SBV g) where
  untuple p = (p^._1, p^._2, p^._3, p^._4, p^._5, p^._6, p^._7)

  tuple p@(sa, sb, sc, sd, se, sf, sg)
    | Just a <- unliteral sa, Just b <- unliteral sb, Just c <- unliteral sc, Just d <- unliteral sd, Just e <- unliteral se, Just f <- unliteral sf, Just g <- unliteral sg
    = literal (a, b, c, d, e, f, g)
    | True
    = SBV $ SVal k $ Right $ cache res
    where k      = kindOf p
          res st = do asv <- sbvToSV st sa
                      bsv <- sbvToSV st sb
                      csv <- sbvToSV st sc
                      dsv <- sbvToSV st sd
                      esv <- sbvToSV st se
                      fsv <- sbvToSV st sf
                      gsv <- sbvToSV st sg
                      newExpr st k (SBVApp (TupleConstructor 7) [asv, bsv, csv, dsv, esv, fsv, gsv])

instance (SymVal a, SymVal b, SymVal c, SymVal d, SymVal e, SymVal f, SymVal g, SymVal h)
      => Tuple (a, b, c, d, e, f, g, h) (SBV a, SBV b, SBV c, SBV d, SBV e, SBV f, SBV g, SBV h) where
  untuple p = (p^._1, p^._2, p^._3, p^._4, p^._5, p^._6, p^._7, p^._8)

  tuple p@(sa, sb, sc, sd, se, sf, sg, sh)
    | Just a <- unliteral sa, Just b <- unliteral sb, Just c <- unliteral sc, Just d <- unliteral sd, Just e <- unliteral se, Just f <- unliteral sf, Just g <- unliteral sg, Just h <- unliteral sh
    = literal (a, b, c, d, e, f, g, h)
    | True
    = SBV $ SVal k $ Right $ cache res
    where k      = kindOf p
          res st = do asv <- sbvToSV st sa
                      bsv <- sbvToSV st sb
                      csv <- sbvToSV st sc
                      dsv <- sbvToSV st sd
                      esv <- sbvToSV st se
                      fsv <- sbvToSV st sf
                      gsv <- sbvToSV st sg
                      hsv <- sbvToSV st sh
                      newExpr st k (SBVApp (TupleConstructor 8) [asv, bsv, csv, dsv, esv, fsv, gsv, hsv])

-- Optimization for tuples

-- 2-tuple
instance ( SymVal a, Metric a
         , SymVal b, Metric b)
         => Metric (a, b) where
   msMinimize nm p = do msMinimize (nm ++ "^._1") (p^._1)
                        msMinimize (nm ++ "^._2") (p^._2)
   msMaximize nm p = do msMaximize (nm ++ "^._1") (p^._1)
                        msMaximize (nm ++ "^._2") (p^._2)

-- 3-tuple
instance ( SymVal a, Metric a
         , SymVal b, Metric b
         , SymVal c, Metric c)
         => Metric (a, b, c) where
   msMinimize nm p = do msMinimize (nm ++ "^._1") (p^._1)
                        msMinimize (nm ++ "^._2") (p^._2)
                        msMinimize (nm ++ "^._3") (p^._3)
   msMaximize nm p = do msMaximize (nm ++ "^._1") (p^._1)
                        msMaximize (nm ++ "^._2") (p^._2)
                        msMaximize (nm ++ "^._3") (p^._3)

-- 4-tuple
instance ( SymVal a, Metric a
         , SymVal b, Metric b
         , SymVal c, Metric c
         , SymVal d, Metric d)
         => Metric (a, b, c, d) where
   msMinimize nm p = do msMinimize (nm ++ "^._1") (p^._1)
                        msMinimize (nm ++ "^._2") (p^._2)
                        msMinimize (nm ++ "^._3") (p^._3)
                        msMinimize (nm ++ "^._4") (p^._4)
   msMaximize nm p = do msMaximize (nm ++ "^._1") (p^._1)
                        msMaximize (nm ++ "^._2") (p^._2)
                        msMaximize (nm ++ "^._3") (p^._3)
                        msMaximize (nm ++ "^._4") (p^._4)

-- 5-tuple
instance ( SymVal a, Metric a
         , SymVal b, Metric b
         , SymVal c, Metric c
         , SymVal d, Metric d
         , SymVal e, Metric e)
         => Metric (a, b, c, d, e) where
   msMinimize nm p = do msMinimize (nm ++ "^._1") (p^._1)
                        msMinimize (nm ++ "^._2") (p^._2)
                        msMinimize (nm ++ "^._3") (p^._3)
                        msMinimize (nm ++ "^._4") (p^._4)
                        msMinimize (nm ++ "^._5") (p^._5)
   msMaximize nm p = do msMaximize (nm ++ "^._1") (p^._1)
                        msMaximize (nm ++ "^._2") (p^._2)
                        msMaximize (nm ++ "^._3") (p^._3)
                        msMaximize (nm ++ "^._4") (p^._4)
                        msMaximize (nm ++ "^._5") (p^._5)

-- 6-tuple
instance ( SymVal a, Metric a
         , SymVal b, Metric b
         , SymVal c, Metric c
         , SymVal d, Metric d
         , SymVal e, Metric e
         , SymVal f, Metric f)
         => Metric (a, b, c, d, e, f) where
   msMinimize nm p = do msMinimize (nm ++ "^._1") (p^._1)
                        msMinimize (nm ++ "^._2") (p^._2)
                        msMinimize (nm ++ "^._3") (p^._3)
                        msMinimize (nm ++ "^._4") (p^._4)
                        msMinimize (nm ++ "^._5") (p^._5)
                        msMinimize (nm ++ "^._6") (p^._6)
   msMaximize nm p = do msMaximize (nm ++ "^._1") (p^._1)
                        msMaximize (nm ++ "^._2") (p^._2)
                        msMaximize (nm ++ "^._3") (p^._3)
                        msMaximize (nm ++ "^._4") (p^._4)
                        msMaximize (nm ++ "^._5") (p^._5)
                        msMaximize (nm ++ "^._6") (p^._6)

-- 7-tuple
instance ( SymVal a, Metric a
         , SymVal b, Metric b
         , SymVal c, Metric c
         , SymVal d, Metric d
         , SymVal e, Metric e
         , SymVal f, Metric f
         , SymVal g, Metric g)
         => Metric (a, b, c, d, e, f, g) where
   msMinimize nm p = do msMinimize (nm ++ "^._1") (p^._1)
                        msMinimize (nm ++ "^._2") (p^._2)
                        msMinimize (nm ++ "^._3") (p^._3)
                        msMinimize (nm ++ "^._4") (p^._4)
                        msMinimize (nm ++ "^._5") (p^._5)
                        msMinimize (nm ++ "^._6") (p^._6)
                        msMinimize (nm ++ "^._7") (p^._7)
   msMaximize nm p = do msMaximize (nm ++ "^._1") (p^._1)
                        msMaximize (nm ++ "^._2") (p^._2)
                        msMaximize (nm ++ "^._3") (p^._3)
                        msMaximize (nm ++ "^._4") (p^._4)
                        msMaximize (nm ++ "^._5") (p^._5)
                        msMaximize (nm ++ "^._6") (p^._6)
                        msMaximize (nm ++ "^._7") (p^._7)

-- 8-tuple
instance ( SymVal a, Metric a
         , SymVal b, Metric b
         , SymVal c, Metric c
         , SymVal d, Metric d
         , SymVal e, Metric e
         , SymVal f, Metric f
         , SymVal g, Metric g
         , SymVal h, Metric h)
         => Metric (a, b, c, d, e, f, g, h) where
   msMinimize nm p = do msMinimize (nm ++ "^._1") (p^._1)
                        msMinimize (nm ++ "^._2") (p^._2)
                        msMinimize (nm ++ "^._3") (p^._3)
                        msMinimize (nm ++ "^._4") (p^._4)
                        msMinimize (nm ++ "^._5") (p^._5)
                        msMinimize (nm ++ "^._6") (p^._6)
                        msMinimize (nm ++ "^._7") (p^._7)
                        msMinimize (nm ++ "^._8") (p^._8)
   msMaximize nm p = do msMaximize (nm ++ "^._1") (p^._1)
                        msMaximize (nm ++ "^._2") (p^._2)
                        msMaximize (nm ++ "^._3") (p^._3)
                        msMaximize (nm ++ "^._4") (p^._4)
                        msMaximize (nm ++ "^._5") (p^._5)
                        msMaximize (nm ++ "^._6") (p^._6)
                        msMaximize (nm ++ "^._7") (p^._7)
                        msMaximize (nm ++ "^._8") (p^._8)

{- HLint ignore module "Reduce duplication" -}
