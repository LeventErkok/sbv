-----------------------------------------------------------------------------
-- |
-- Module      :  Data.SBV.Examples.Existentials.Diophantine
-- Copyright   :  (c) Levent Erkok
-- License     :  BSD3
-- Maintainer  :  erkokl@gmail.com
-- Stability   :  experimental
--
-- Finding minimal natural number solutions to linear Diophantine equations,
-- using explicit quantification.
-----------------------------------------------------------------------------
module Data.SBV.Examples.Existentials.Diophantine where

import Data.SBV

--------------------------------------------------------------------------------------------------
-- * Representing solutions
--------------------------------------------------------------------------------------------------
-- | For a homogeneous problem, the solution is any linear combination of the resulting vectors.
-- For a non-homogeneous problem, the solution is any linear combination of the vectors in the
-- second component plus one of the vectors in the first component.
data Solution = Homogeneous    [[Integer]]
              | NonHomogeneous [[Integer]] [[Integer]]
              deriving Show

--------------------------------------------------------------------------------------------------
-- * Solving diophantine equations
--------------------------------------------------------------------------------------------------
-- | ldn: Solve a (L)inear (D)iophantine equation, returning minimal solutions over (N)aturals.
-- The input is given as a rows of equations, with rhs values separated into a tuple.
ldn :: [([Integer], Integer)] -> IO Solution
ldn problem = do solution <- basis (map (map literal) m)
                 if homogeneous
                    then return $ Homogeneous solution
                    else do let ones  = [xs | (1:xs) <- solution]
                                zeros = [xs | (0:xs) <- solution]
                            return $ NonHomogeneous ones zeros
  where rhs = map snd problem
        lhs = map fst problem
        homogeneous = all (== 0) rhs
        m | homogeneous = lhs
          | True        = zipWith (\x y -> -x : y) rhs lhs

-- | Find the basis solution. By definition, the basis has all non-trivial (i.e., non-0) solutions
-- that cannot be written as the sum of two other solutions. We use the mathematically equivalent
-- statement that a solution is in the basis if it's least according to the lexicographic
-- order using the ordinary less-than relation. (NB. We explicitly tell z3 to use the logic
-- AUFLIA for this problem, as the BV solver that is chosen automatically has a performance
-- issue. See: https://z3.codeplex.com/workitem/88.)
basis :: [[SInteger]] -> IO [[Integer]]
basis m = extractModels `fmap` allSatWith z3{useLogic = Just (PredefinedLogic AUFLIA)} cond
 where cond = do as <- mkExistVars  n
                 bs <- mkForallVars n
                 return $ ok as &&& (ok bs ==> as .== bs ||| bnot (bs `less` as))
       n = if null m then 0 else length (head m)
       ok xs = bAny (.> 0) xs &&& bAll (.>= 0) xs &&& bAnd [sum (zipWith (*) r xs) .== 0 | r <- m]
       as `less` bs = bAnd (zipWith (.<=) as bs) &&& bOr (zipWith (.<) as bs)

--------------------------------------------------------------------------------------------------
-- * Examples
--------------------------------------------------------------------------------------------------

-- | Solve the equation:
--
--    @2x + y - z = 2@
--
-- We have:
--
-- >>> test
-- NonHomogeneous [[0,2,0],[1,0,0]] [[0,1,1],[1,0,2]]
--
-- which means that the solutions are of the form:
--
--    @(1, 0, 0) + k (0, 1, 1) + k' (1, 0, 2) = (1+k', k, k+2k')@
--
-- OR
--
--    @(0, 2, 0) + k (0, 1, 1) + k' (1, 0, 2) = (k', 2+k, k+2k')@
--
-- for arbitrary @k@, @k'@. It's easy to see that these are really solutions
-- to the equation given. It's harder to see that they cover all possibilities,
-- but a moments thought reveals that is indeed the case.
test :: IO Solution
test = ldn [([2,1,-1], 2)]

-- | A puzzle: Five sailors and a monkey escape from a naufrage and reach an island with
-- coconuts. Before dawn, they gather a few of them and decide to sleep first and share
-- the next day. At night, however, one of them awakes, counts the nuts, makes five parts,
-- gives the remaining nut to the monkey, saves his share away, and sleeps. All other
-- sailors do the same, one by one. When they all wake up in the morning, they again make 5 shares,
-- and give the last remaining nut to the monkey. How many nuts were there at the beginning?
--
-- We can model this as a series of diophantine equations:
--
-- @
--       x_0 = 5 x_1 + 1
--     4 x_1 = 5 x_2 + 1
--     4 x_2 = 5 x_3 + 1
--     4 x_3 = 5 x_4 + 1
--     4 x_4 = 5 x_5 + 1
--     4 x_5 = 5 x_6 + 1
-- @
--
-- We need to solve for x_0, over the naturals. We have:
--
-- >>> sailors
-- [15621,3124,2499,1999,1599,1279,1023]
--
-- That is:
--
-- @
--   * There was a total of 15621 coconuts
--   * 1st sailor: 15621 = 3124*5+1, leaving 15621-3124-1 = 12496
--   * 2nd sailor: 12496 = 2499*5+1, leaving 12496-2499-1 =  9996
--   * 3rd sailor:  9996 = 1999*5+1, leaving  9996-1999-1 =  7996
--   * 4th sailor:  7996 = 1599*5+1, leaving  7996-1599-1 =  6396
--   * 5th sailor:  6396 = 1279*5+1, leaving  6396-1279-1 =  5116
--   * In the morning, they had: 5116 = 1023*5+1.
-- @
--
-- Note that this is the minimum solution, that is, we are guaranteed that there's
-- no solution with less number of coconuts. In fact, any member of @[15625*k-4 | k <- [1..]]@
-- is a solution, i.e., so are @31246@, @46871@, @62496@, @78121@, etc.
sailors :: IO [Integer]
sailors = do NonHomogeneous (xs:_) _ <- ldn [ ([1, -5,  0,  0,  0,  0,  0], 1)
                                            , ([0,  4, -5 , 0,  0,  0,  0], 1)
                                            , ([0,  0,  4, -5 , 0,  0,  0], 1)
                                            , ([0,  0,  0,  4, -5,  0,  0], 1)
                                            , ([0,  0,  0,  0,  4, -5,  0], 1)
                                            , ([0,  0,  0,  0,  0,  4, -5], 1)
                                            ]
             return xs
