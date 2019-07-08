-----------------------------------------------------------------------------
-- |
-- Module    : Documentation.SBV.Examples.Queries.UnsatCore
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Demonstrates extraction of unsat-cores via queries.
-----------------------------------------------------------------------------

{-# OPTIONS_GHC -Wall -Werror #-}

module Documentation.SBV.Examples.Queries.UnsatCore where

import Data.SBV
import Data.SBV.Control

-- | A simple goal with three constraints, two of which are
-- conflicting with each other. The third is irrelevant, in the sense
-- that it does not contribute to the fact that the goal is unsatisfiable.
p :: Symbolic (Maybe [String])
p = do a <- sInteger "a"
       b <- sInteger "b"

       -- tell the solver we want unsat-cores
       setOption $ ProduceUnsatCores True

       -- create named constraints, which will allow
       -- unsat-core extraction with the given names
       namedConstraint "less than 5"  $ a .< 5
       namedConstraint "more than 10" $ a .> 10
       namedConstraint "irrelevant"   $ a .> b

       -- To obtain the unsat-core, we run a query
       query $ do cs <- checkSat
                  case cs of
                    Unsat -> Just <$> getUnsatCore
                    _     -> return Nothing


-- | Extract the unsat-core of 'p'. We have:
--
-- >>> ucCore
-- Unsat core is: ["less than 5","more than 10"]
--
-- Demonstrating that the constraint @a .> b@ is /not/ needed for unsatisfiablity in this case.
ucCore :: IO ()
ucCore = do mbCore <- runSMT p
            case mbCore of
              Nothing   -> putStrLn "Problem is satisfiable."
              Just core -> putStrLn $ "Unsat core is: " ++ show core
