-----------------------------------------------------------------------------
-- |
-- Module    : Data.SBV.Tuple
-- Author    : Joel Burget, Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Accessing symbolic tuple fields and deconstruction.
-----------------------------------------------------------------------------

{-# LANGUAGE DataKinds              #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE FlexibleContexts       #-}
{-# LANGUAGE KindSignatures         #-}
{-# LANGUAGE MultiParamTypeClasses  #-}

module Data.SBV.Tuple (
  -- * Symbolic field access
    (^.), _1, _2, _3, _4, _5, _6, _7, _8
  -- * Untupling
  , untuple
  ) where

import GHC.TypeLits

import Data.SBV.Core.Data
import Data.SBV.Core.Symbolic

-- | Field access, inspired by the lens library. This is merely reverse
-- application, but allows us to write things like @(1, 2)^._1@ which is
-- likely to be familiar to most Haskell programmers out there. Note that
-- this is precisely equivalent to @_1 (1, 2)@, but perhaps it reads a little
-- nicer.
(^.) :: a -> (a -> b) -> b
t ^. f = f t
infixl 8 ^.

-- | Dynamic interface to exporting tuples, this function is not
-- exported on purpose; use it only via the field functions '_1', '_2', etc.
symbolicFieldAccess :: SymWord a => Int -> SBV tup -> SBV a
symbolicFieldAccess i tup
  | 1 > i || i > lks
  = bad $ "Index is out of bounds, " ++ show i ++ " is outside [1," ++ show lks ++ "]"
  | SBV (SVal kval (Left v)) <- tup
  = case cwVal v of
      CWTuple vs | kval      /= ktup -> bad $ "Kind/value mismatch: "      ++ show kval
                 | length vs /= lks  -> bad $ "Value has fewer elements: " ++ show (CW kval (CWTuple vs))
                 | True              -> literal $ fromCW $ CW kElem (vs !! (i-1))
      _                              -> bad $ "Kind/value mismatch: " ++ show v
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
          where y st = do sw <- svToSW st $ unSBV tup
                          newExpr st kElem (SBVApp (TupleAccess i lks) [sw])

-- | Field labels
data Label (l :: Symbol) = Get

-- | The class 'HasField' captures the notion that a type has a certain field
class SymWord elt => HasField l elt tup | l tup -> elt where
  field :: Label l -> SBV tup -> SBV elt

instance SymWord a => HasField "_1" a (a, b)                   where field _ = symbolicFieldAccess 1
instance SymWord a => HasField "_1" a (a, b, c)                where field _ = symbolicFieldAccess 1
instance SymWord a => HasField "_1" a (a, b, c, d)             where field _ = symbolicFieldAccess 1
instance SymWord a => HasField "_1" a (a, b, c, d, e)          where field _ = symbolicFieldAccess 1
instance SymWord a => HasField "_1" a (a, b, c, d, e, f)       where field _ = symbolicFieldAccess 1
instance SymWord a => HasField "_1" a (a, b, c, d, e, f, g)    where field _ = symbolicFieldAccess 1
instance SymWord a => HasField "_1" a (a, b, c, d, e, f, g, h) where field _ = symbolicFieldAccess 1

instance SymWord b => HasField "_2" b (a, b)                   where field _ = symbolicFieldAccess 2
instance SymWord b => HasField "_2" b (a, b, c)                where field _ = symbolicFieldAccess 2
instance SymWord b => HasField "_2" b (a, b, c, d)             where field _ = symbolicFieldAccess 2
instance SymWord b => HasField "_2" b (a, b, c, d, e)          where field _ = symbolicFieldAccess 2
instance SymWord b => HasField "_2" b (a, b, c, d, e, f)       where field _ = symbolicFieldAccess 2
instance SymWord b => HasField "_2" b (a, b, c, d, e, f, g)    where field _ = symbolicFieldAccess 2
instance SymWord b => HasField "_2" b (a, b, c, d, e, f, g, h) where field _ = symbolicFieldAccess 2

instance SymWord c => HasField "_3" c (a, b, c)                where field _ = symbolicFieldAccess 3
instance SymWord c => HasField "_3" c (a, b, c, d)             where field _ = symbolicFieldAccess 3
instance SymWord c => HasField "_3" c (a, b, c, d, e)          where field _ = symbolicFieldAccess 3
instance SymWord c => HasField "_3" c (a, b, c, d, e, f)       where field _ = symbolicFieldAccess 3
instance SymWord c => HasField "_3" c (a, b, c, d, e, f, g)    where field _ = symbolicFieldAccess 3
instance SymWord c => HasField "_3" c (a, b, c, d, e, f, g, h) where field _ = symbolicFieldAccess 3

instance SymWord d => HasField "_4" d (a, b, c, d)             where field _ = symbolicFieldAccess 4
instance SymWord d => HasField "_4" d (a, b, c, d, e)          where field _ = symbolicFieldAccess 4
instance SymWord d => HasField "_4" d (a, b, c, d, e, f)       where field _ = symbolicFieldAccess 4
instance SymWord d => HasField "_4" d (a, b, c, d, e, f, g)    where field _ = symbolicFieldAccess 4
instance SymWord d => HasField "_4" d (a, b, c, d, e, f, g, h) where field _ = symbolicFieldAccess 4

instance SymWord e => HasField "_5" e (a, b, c, d, e)          where field _ = symbolicFieldAccess 5
instance SymWord e => HasField "_5" e (a, b, c, d, e, f)       where field _ = symbolicFieldAccess 5
instance SymWord e => HasField "_5" e (a, b, c, d, e, f, g)    where field _ = symbolicFieldAccess 5
instance SymWord e => HasField "_5" e (a, b, c, d, e, f, g, h) where field _ = symbolicFieldAccess 5

instance SymWord f => HasField "_6" f (a, b, c, d, e, f)       where field _ = symbolicFieldAccess 6
instance SymWord f => HasField "_6" f (a, b, c, d, e, f, g)    where field _ = symbolicFieldAccess 6
instance SymWord f => HasField "_6" f (a, b, c, d, e, f, g, h) where field _ = symbolicFieldAccess 6

instance SymWord g => HasField "_7" g (a, b, c, d, e, f, g)    where field _ = symbolicFieldAccess 7
instance SymWord g => HasField "_7" g (a, b, c, d, e, f, g, h) where field _ = symbolicFieldAccess 7

instance SymWord h => HasField "_8" h (a, b, c, d, e, f, g, h) where field _ = symbolicFieldAccess 8

-- | Access the 1st element of an @STupleN@, @2 <= N <= 8@. Also see '^.'.
_1 :: HasField "_1" b a => SBV a -> SBV b
_1 = field (Get :: Label "_1")

-- | Access the 2nd element of an @STupleN@, @2 <= N <= 8@. Also see '^.'.
_2 :: HasField "_2" b a => SBV a -> SBV b
_2 = field (Get :: Label "_2")

-- | Access the 3nd element of an @STupleN@, @3 <= N <= 8@. Also see '^.'.
_3 :: HasField "_3" b a => SBV a -> SBV b
_3 = field (Get :: Label "_3")

-- | Access the 4th element of an @STupleN@, @4 <= N <= 8@. Also see '^.'.
_4 :: HasField "_4" b a => SBV a -> SBV b
_4 = field (Get :: Label "_4")

-- | Access the 5th element of an @STupleN@, @5 <= N <= 8@. Also see '^.'.
_5 :: HasField "_5" b a => SBV a -> SBV b
_5 = field (Get :: Label "_5")

-- | Access the 6th element of an @STupleN@, @6 <= N <= 8@. Also see '^.'.
_6 :: HasField "_6" b a => SBV a -> SBV b
_6 = field (Get :: Label "_6")

-- | Access the 7th element of an @STupleN@, @7 <= N <= 8@. Also see '^.'.
_7 :: HasField "_7" b a => SBV a -> SBV b
_7 = field (Get :: Label "_7")

-- | Access the 8th element of an @STupleN@, @8 <= N <= 8@. Also see '^.'.
_8 :: HasField "_8" b a => SBV a -> SBV b
_8 = field (Get :: Label "_8")

-- | Unconstructing a tuple to its parts
class Untuple tup a | tup -> a where
  -- | Deconstruct a tuple, getting its constituent parts apart.
  untuple :: SBV tup -> a

instance (SymWord a, SymWord b) => Untuple (a, b) (SBV a, SBV b) where
  untuple p = (p^._1, p^._2)

instance (SymWord a, SymWord b, SymWord c) => Untuple (a, b, c) (SBV a, SBV b, SBV c) where
  untuple p = (p^._1, p^._2, p^._3)

instance (SymWord a, SymWord b, SymWord c, SymWord d) => Untuple (a, b, c, d) (SBV a, SBV b, SBV c, SBV d) where
  untuple p = (p^._1, p^._2, p^._3, p^._4)

instance (SymWord a, SymWord b, SymWord c, SymWord d, SymWord e) => Untuple (a, b, c, d, e) (SBV a, SBV b, SBV c, SBV d, SBV e) where
  untuple p = (p^._1, p^._2, p^._3, p^._4, p^._5)

instance (SymWord a, SymWord b, SymWord c, SymWord d, SymWord e, SymWord f) => Untuple (a, b, c, d, e, f) (SBV a, SBV b, SBV c, SBV d, SBV e, SBV f) where
  untuple p = (p^._1, p^._2, p^._3, p^._4, p^._5, p^._6)

instance (SymWord a, SymWord b, SymWord c, SymWord d, SymWord e, SymWord f, SymWord g) => Untuple (a, b, c, d, e, f, g) (SBV a, SBV b, SBV c, SBV d, SBV e, SBV f, SBV g) where
  untuple p = (p^._1, p^._2, p^._3, p^._4, p^._5, p^._6, p^._7)

instance (SymWord a, SymWord b, SymWord c, SymWord d, SymWord e, SymWord f, SymWord g, SymWord h) => Untuple (a, b, c, d, e, f, g, h) (SBV a, SBV b, SBV c, SBV d, SBV e, SBV f, SBV g, SBV h) where
  untuple p = (p^._1, p^._2, p^._3, p^._4, p^._5, p^._6, p^._7, p^._8)
