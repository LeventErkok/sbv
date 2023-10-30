-----------------------------------------------------------------------------
-- |
-- Module    : Documentation.SBV.Examples.Puzzles.Coins
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Solves the following puzzle:
--
-- @
-- You and a friend pass by a standard coin operated vending machine and you decide to get a candy bar.
-- The price is US $0.95, but after checking your pockets you only have a dollar (US $1) and the machine
-- only takes coins. You turn to your friend and have this conversation:
--   you: Hey, do you have change for a dollar?
--   friend: Let's see. I have 6 US coins but, although they add up to a US $1.15, I can't break a dollar.
--   you: Huh? Can you make change for half a dollar?
--   friend: No.
--   you: How about a quarter?
--   friend: Nope, and before you ask I cant make change for a dime or nickel either.
--   you: Really? and these six coins are all US government coins currently in production? 
--   friend: Yes.
--   you: Well can you just put your coins into the vending machine and buy me a candy bar, and I'll pay you back?
--   friend: Sorry, I would like to but I cant with the coins I have.
-- What coins are your friend holding?
-- @
--
-- To be fair, the problem has no solution /mathematically/. But there is a solution when one takes into account that
-- vending machines typically do not take the 50 cent coins!
--
-----------------------------------------------------------------------------

{-# OPTIONS_GHC -Wall -Werror #-}

module Documentation.SBV.Examples.Puzzles.Coins where

import Data.SBV

-- | We will represent coins with 16-bit words (more than enough precision for coins).
type Coin = SWord16

-- | Create a coin. The argument Int argument just used for naming the coin. Note that
-- we constrain the value to be one of the valid U.S. coin values as we create it.
mkCoin :: Int -> Symbolic Coin
mkCoin i = do c <- free $ 'c' : show i
              constrain $ sAny (.== c) [1, 5, 10, 25, 50, 100]
              return c

-- | Return all combinations of a sequence of values.
combinations :: [a] -> [[a]]
combinations coins = concat [combs i coins | i <- [1 .. length coins]]
  where combs 0 _      = [[]]
        combs _ []     = []
        combs k (x:xs) = map (x:) (combs (k-1) xs) ++ combs k xs

-- | Constraint 1: Cannot make change for a dollar.
c1 :: [Coin] -> SBool
c1 xs = sum xs ./= 100

-- | Constraint 2: Cannot make change for half a dollar.
c2 :: [Coin] -> SBool
c2 xs = sum xs ./= 50

-- | Constraint 3: Cannot make change for a quarter.
c3 :: [Coin] -> SBool
c3 xs = sum xs ./= 25

-- | Constraint 4: Cannot make change for a dime.
c4 :: [Coin] -> SBool
c4 xs = sum xs ./= 10

-- | Constraint 5: Cannot make change for a nickel
c5 :: [Coin] -> SBool
c5 xs = sum xs ./= 5

-- | Constraint 6: Cannot buy the candy either. Here's where we need to have the extra knowledge
-- that the vending machines do not take 50 cent coins.
c6 :: [Coin] -> SBool
c6 xs = sum (map val xs) ./= 95
   where val x = ite (x .== 50) 0 x

-- | Solve the puzzle. We have:
--
-- >>> puzzle
-- Satisfiable. Model:
--   c1 = 50 :: Word16
--   c2 = 25 :: Word16
--   c3 = 10 :: Word16
--   c4 = 10 :: Word16
--   c5 = 10 :: Word16
--   c6 = 10 :: Word16
--
-- i.e., your friend has 4 dimes, a quarter, and a half dollar.
puzzle :: IO SatResult
puzzle = sat $ do
        cs <- mapM mkCoin [1..6]

        -- Assert each of the constraints for all combinations that has
        -- at least two coins (to make change)
        mapM_ constrain [c s | s <- combinations cs, length s >= 2, c <- [c1, c2, c3, c4, c5, c6]]

        -- the following constraint is not necessary for solving the puzzle
        -- however, it makes sure that the solution comes in decreasing value of coins,
        -- thus allowing the above test to succeed regardless of the solver used.
        constrain $ sAnd $ zipWith (.>=) cs (drop 1 cs)

        -- assert that the sum must be 115 cents.
        return $ sum cs .== 115
