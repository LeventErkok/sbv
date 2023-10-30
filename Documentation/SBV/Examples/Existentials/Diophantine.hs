-----------------------------------------------------------------------------
-- |
-- Module    : Documentation.SBV.Examples.Existentials.Diophantine
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Finding minimal natural number solutions to linear Diophantine equations,
-- using explicit quantification.
-----------------------------------------------------------------------------

{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections       #-}
{-# LANGUAGE TypeApplications    #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module Documentation.SBV.Examples.Existentials.Diophantine where

import Data.List (intercalate, transpose)

import Data.SBV
import Data.Proxy

import GHC.TypeLits

--------------------------------------------------------------------------------------------------
-- * Representing solutions
--------------------------------------------------------------------------------------------------
-- | For a homogeneous problem, the solution is any linear combination of the resulting vectors.
-- For a non-homogeneous problem, the solution is any linear combination of the vectors in the
-- second component plus one of the vectors in the first component.
data Solution = Homogeneous    [[Integer]]
              | NonHomogeneous [[Integer]] [[Integer]]

instance Show Solution where
  show s = case s of
             Homogeneous        xss -> comb supplyH (map (False,) xss)
             NonHomogeneous css xss -> intercalate "\n" [comb supplyNH ((True, cs) : map (False,) xss) | cs <- css]
    where supplyH  = ['k' : replicate i '\'' | i <- [0 ..]]
          supplyNH = "" : supplyH

          comb supply xss = vec $ map add (transpose (zipWith muls supply xss))
            where muls x (isConst, cs) = map mul cs
                    where mul 0 = "0"
                          mul 1 | isConst = "1"
                                | True    = x
                          mul k | isConst = show k
                                | True    = show k ++ x

                  add [] = "0"
                  add xs = foldr1 plus xs

                  plus "0" y   = y
                  plus x   "0" = x
                  plus x   y   = x ++ "+" ++ y

          vec xs = "(" ++ intercalate ", " xs ++ ")"

--------------------------------------------------------------------------------------------------
-- * Solving diophantine equations
--------------------------------------------------------------------------------------------------
-- | ldn: Solve a (L)inear (D)iophantine equation, returning minimal solutions over (N)aturals.
-- The input is given as a rows of equations, with rhs values separated into a tuple. The first
-- argument must be a proxy of a natural, must be total number of columns in the system. (i.e.,
-- #of variables + 1). The second parameter limits the search to bound: In case there are
-- too many solutions, you might want to limit your search space.
ldn :: forall proxy n. KnownNat n => proxy n -> Maybe Int -> [([Integer], Integer)] -> IO Solution
ldn pn mbLim problem = do solution <- basis pn mbLim (map (map literal) m)
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
-- statement that a solution is in the basis if it's least according to the natural partial
-- order using the ordinary less-than relation.
basis :: forall proxy n. KnownNat n => proxy n -> Maybe Int -> [[SInteger]] -> IO [[Integer]]
basis _ mbLim m = extractModels `fmap` allSatWith z3{allSatMaxModelCount = mbLim} cond
 where cond = do as <- mkFreeVars  n

                 constrain $ \(ForallN bs :: ForallN n nm Integer) ->
                        ok as .&& (ok bs .=> as .== bs .|| sNot (bs `less` as))

       n = case m of
            []  -> 0
            f:_ -> length f

       ok xs = sAny (.> 0) xs .&& sAll (.>= 0) xs .&& sAnd [sum (zipWith (*) r xs) .== 0 | r <- m]

       as `less` bs = sAnd (zipWith (.<=) as bs) .&& sOr (zipWith (.<) as bs)

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
-- (k, 2+k', 2k+k')
-- (1+k, k', 2k+k')
--
-- That is, for arbitrary @k@ and @k'@, we have two different solutions. (An infinite family.)
-- You can verify these solutuions by substituting the values for @x@, @y@ and @z@ in the above, for each choice.
-- It's harder to see that they cover all possibilities, but a moments thought reveals that is indeed the case.
test :: IO Solution
test = ldn (Proxy @4) Nothing [([2,1,-1], 2)]

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
-- We need to solve for x_0, over the naturals. If you run this program, z3 takes its time (quite long!)
-- but, it eventually computes: [15621,3124,2499,1999,1599,1279,1023] as the answer.
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
--
-- Note that we iteratively deepen our search by requesting increasing number of
-- solutions to avoid the all-sat pitfall.
sailors :: IO [Integer]
sailors = search 1
  where search i = do soln <- ldn (Proxy @8)
                                  (Just i)
                                  [ ([1, -5,  0,  0,  0,  0,  0], 1)
                                  , ([0,  4, -5 , 0,  0,  0,  0], 1)
                                  , ([0,  0,  4, -5 , 0,  0,  0], 1)
                                  , ([0,  0,  0,  4, -5,  0,  0], 1)
                                  , ([0,  0,  0,  0,  4, -5,  0], 1)
                                  , ([0,  0,  0,  0,  0,  4, -5], 1)
                                  ]
                      case soln of
                        NonHomogeneous (xs:_) _ -> return xs
                        _                       -> search (i+1)
