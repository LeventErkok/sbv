-----------------------------------------------------------------------------
-- |
-- Module    : Documentation.SBV.Examples.ADT.Shapes
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Generate shapes satisfying constraints on their dimensions and area. This
-- example demonstrates symbolic pattern matching on an algebraic datatype,
-- enumerating models with 'allSatWith', and extracting concrete Haskell values
-- in query mode.
-----------------------------------------------------------------------------

{-# OPTIONS_GHC -Wall -Werror #-}

{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE QuasiQuotes       #-}
{-# LANGUAGE TemplateHaskell   #-}
{-# LANGUAGE TypeApplications  #-}

module Documentation.SBV.Examples.ADT.Shapes where

import Data.SBV
import Data.SBV.Control

-- | Shapes with signed 32-bit dimensions. We reserve 'Rectangle' for shapes
-- with unequal sides, so squares have their own constructor.
data Shape = Dot                                        -- ^ A point, with zero area.
           | Square    { side  :: Int32 }                -- ^ A square.
           | Rectangle { sideA :: Int32, sideB :: Int32 } -- ^ A rectangle.
           deriving Show

-- | Generate 'SShape', symbolic constructors such as 'sSquare', and the
-- support needed to pass shapes to and from the solver.
mkSymbolic [''Shape]

-- | Compute the area using 'sCase' to match a symbolic shape. Ordinary Haskell
-- pattern matching cannot inspect a shape whose constructor is not yet known.
area :: SShape -> SInt32
area s = [sCase| s of
            Dot           -> 0
            Square a      -> a * a
            Rectangle a b -> a * b
         |]

-- | Require positive dimensions below 100, and unequal sides for rectangles.
-- The bounds also ensure that area calculations cannot overflow 'Int32'.
-- A dot has no dimensions to constrain.
goodShape :: SShape -> SBool
goodShape s = [sCase| s of
                 Dot           -> sTrue
                 Square a      -> a .> 0 .&& a .< 100
                 Rectangle a b -> a .> 0 .&& a .< 100 .&& b .> 0 .&& b .< 100 .&& a ./= b
              |]

-- | Create a symbolic shape and constrain its dimensions. Creating the value
-- automatically declares the datatype to the solver.
newShape :: Symbolic SShape
newShape = do x <- free "shape"
              constrain $ goodShape x
              pure x

-- | Select non-dot shapes with area between 10 and 30, inclusive.
-- The explicit exclusion of 'Dot' is redundant with the area bound, but
-- illustrates a symbolic comparison with a datatype constructor.
interesting :: SShape -> SBool
interesting x = area x .>= 10 .&& area x .<= 30 .&& x ./= sDot

-- | Ask for five distinct models using SBV's built-in enumeration.
--
-- >>> examples
-- Solution #1:
--   shape = Rectangle 24 1 :: Shape
-- Solution #2:
--   shape = Rectangle 1 25 :: Shape
-- Solution #3:
--   shape = Rectangle 25 1 :: Shape
-- Solution #4:
--   shape = Square 5 :: Shape
-- Solution #5:
--   shape = Square 4 :: Shape
-- Found 5 different solutions.
examples :: IO AllSatResult
examples = allSatWith z3{allSatMaxModelCount = Just 5} (interesting <$> newShape)

-- | Enumerate shapes manually in query mode. After each satisfiability check,
-- 'getValue' returns a concrete 'Shape'. We exclude that value using 'literal'
-- before asking for the next model. Stop after five shapes, or earlier if
-- there are no more solutions, and return them in discovery order.
--
-- >>> extracted
-- [Square {side = 4},Rectangle {sideA = 15, sideB = 1},Square {side = 5},Rectangle {sideA = 4, sideB = 6},Rectangle {sideA = 12, sideB = 2}]
extracted :: IO [Shape]
extracted = runSMT $ do
        x <- newShape
        constrain $ interesting x

        let loop :: Int -> [Shape] -> Query [Shape]
            loop 5 sofar = pure $ reverse sofar
            loop i sofar = do cs <- checkSat
                              case cs of
                                Sat   -> do xv <- getValue x
                                            -- Exclude the entire shape, including its fields.
                                            constrain $ x ./= literal xv
                                            loop (i+1) (xv : sofar)
                                Unsat -> pure $ reverse sofar
                                _     -> error $ "Solver said: " ++ show cs

        query $ loop 0 []
