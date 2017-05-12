-----------------------------------------------------------------------------
-- |
-- Module      :  Data.SBV.Examples.Misc.UnsatCore
-- Copyright   :  (c) Levent Erkok
-- License     :  BSD3
-- Maintainer  :  erkokl@gmail.com
-- Stability   :  experimental
--
-- Demonstrates extraction of unsat-cores.
-----------------------------------------------------------------------------

module Data.SBV.Examples.Misc.UnsatCore where

import Data.SBV

-- | A simple goal with three constraints, two of which are
-- conflicting with each other. The third is irrelevant, in the sense
-- that it does not contribute to the fact that the goal is unsatisfiable.
p :: Goal
p = do a <- sInteger "a"
       b <- sInteger "b"

       -- create named constraints, which will allow
       -- unsat-core extraction with the given names
       namedConstraint "less than 5"  $ a .< 5
       namedConstraint "more than 10" $ a .> (10::SInteger)
       namedConstraint "irrelevant"   $ a .> b

-- | Extract the unsat-core of 'p'. We have:
--
-- >>> ucCore
-- Unsatisfiable. Unsat core:
--   less than 5
--   more than 10
-- =====================================
-- Unsat core is: ["less than 5","more than 10"]
--
-- Demonstrating that the constraint @a .> b@ is /not/ needed for unsatisfiablity in this case.
ucCore :: IO ()
ucCore = do r <- satWith z3{getUnsatCore=True} p
            print r
            putStrLn "====================================="
            case extractUnsatCore r of
              Nothing -> putStrLn "No unsat core!"
              Just xs -> putStrLn $ "Unsat core is: " ++ show xs
