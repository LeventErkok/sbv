-----------------------------------------------------------------------------
-- |
-- Module    : Documentation.SBV.Examples.Queries.Abducts
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Demonstrates extraction of abducts via queries.
--
-- N.B. Interpolants are only supported by CVC5 currently.
-----------------------------------------------------------------------------

{-# OPTIONS_GHC -Wall -Werror #-}

module Documentation.SBV.Examples.Queries.Abducts where

import Data.SBV
import Data.SBV.Control

-- | Abduct extraction example. We have the constraint @x >= 0@
-- and we want to make @x + y >= 2@. We have:
--
-- >>> example
-- Got: (define-fun abd () Bool (and (= s0 s1) (= s0 1)))
-- Got: (define-fun abd () Bool (and (= 2 s1) (= s0 1)))
-- Got: (define-fun abd () Bool (and (= s0 s1) (<= 1 s1)))
-- Got: (define-fun abd () Bool (= 2 s1))
--
-- Note that @s0@ refers to @x@ and @s1@ refers to @y@ above. You can verify
-- that adding any of these will ensure @x + y >= 2@.
example :: IO ()
example = runSMTWith cvc5 $ do

       setOption $ ProduceAbducts True

       x <- sInteger "x"
       y <- sInteger "y"

       constrain $ x .>= 0

       query $ do abd <- getAbduct Nothing "abd" $ x + y .>= 2
                  io $ putStrLn $ "Got: " ++ abd

                  let next = getAbductNext >>= io . putStrLn . ("Got: " ++)

                  -- Get and display a couple of abducts
                  next
                  next
                  next
