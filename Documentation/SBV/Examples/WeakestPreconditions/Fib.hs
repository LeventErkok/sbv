-----------------------------------------------------------------------------
-- |
-- Module    : Documentation.SBV.Examples.WeakestPreconditions.Fib
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Proof of correctness of an imperative fibonacci algorithm, using weakest
-- preconditions. Note that due to the recursive nature of fibonacci, we
-- cannot write the spec directly, so we use an uninterpreted function
-- and proper axioms to complete the proof.
-----------------------------------------------------------------------------

{-# LANGUAGE DeriveAnyClass        #-}
{-# LANGUAGE DeriveFoldable        #-}
{-# LANGUAGE DeriveGeneric         #-}
{-# LANGUAGE DeriveTraversable     #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NamedFieldPuns        #-}

module Documentation.SBV.Examples.WeakestPreconditions.Fib where

import Data.SBV
import Data.SBV.Control

import Data.SBV.Tools.WeakestPreconditions

import GHC.Generics (Generic)

-- * Program state

-- | The state for the sum program, parameterized over a base type @a@.
data FibS a = FibS { n :: a    -- ^ The input value
                   , i :: a    -- ^ Loop counter
                   , k :: a    -- ^ track fib (i+1)
                   , m :: a    -- ^ track fib i
                   }
                   deriving (Show, Generic, Mergeable, Functor, Foldable, Traversable)

-- | Show instance for 'FibS'. The above deriving clause would work just as well,
-- but we want it to be a little prettier here, and hence the @OVERLAPS@ directive.
instance {-# OVERLAPS #-} (SymVal a, Show a) => Show (FibS (SBV a)) where
   show (FibS n i k m) = "{n = " ++ sh n ++ ", i = " ++ sh i ++ ", k = " ++ sh k ++ ", m = " ++ sh m ++ "}"
     where sh v = case unliteral v of
                    Nothing -> "<symbolic>"
                    Just l  -> show l

-- | 'Fresh' instance for the program state
instance (SymVal a, SMTValue a) => Fresh IO (FibS (SBV a)) where
  fresh = FibS <$> freshVar_  <*> freshVar_  <*> freshVar_ <*> freshVar_

-- | Helper type synonym
type F = FibS SInteger

-- * The algorithm

-- | The imperative fibonacci algorithm:
--
-- @
--     i = 0
--     k = 1
--     m = 0
--     while i < n:
--        m, k = k, m + k
--        i++
-- @
--
-- When the loop terminates, @m@ contains @fib(n)@.
algorithm :: Stmt F
algorithm = Seq [ Assign $ \st -> st{i = 0, k = 1, m = 0}
                , assert "n >= 0" $ \FibS{n} -> n .>= 0
                , While "i < n"
                        (\FibS{n, i, k, m} -> i .<= n .&& k .== fib (i+1) .&& m .== fib i)
                        (Just (\FibS{n, i} -> [n-i]))
                        (\FibS{n, i} -> i .< n)
                        $ Seq [ Assign $ \st@FibS{m, k} -> st{m = k, k = m + k}
                              , Assign $ \st@FibS{i}    -> st{i = i+1}
                              ]
                ]

-- | We cannot define fibonacci at the SBV level over integers,
-- since it would not be symbolically terminating. So, we use an
-- uninterpreted function instead, and set up the proper axioms manually.
fib :: SInteger -> SInteger
fib = uninterpret "fib"

-- | Constraints and axioms we need to state explicitly to tell
-- the SMT solver about our specification for fibonacci.
axiomatizeFib :: Symbolic ()
axiomatizeFib = do constrain $ fib 0 .== 0
                   constrain $ fib 1 .== 1

                   -- This is unfortunate; but SBV currently does not support
                   -- adding quantified constraints. So we have to write this
                   -- axiom in SMT-Lib. Note also how carefully we've chosen
                   -- this axiom to work with our proof!
                   addAxiom "fib_n" [ "(assert (forall ((x Int))"
                                    , "                (= (fib (+ x 2)) (+ (fib (+ x 1)) (fib x)))))"
                                    ]

-- | Precondition for our program: @n@ must be non-negative.
pre :: F -> SBool
pre FibS{n} = n .>= 0

-- | Postcondition for our program: @m = fib n@
post :: F -> SBool
post FibS{n, m} = m .== fib n

-- | Stability condition: Program must leave @n@ unchanged.
noChange :: Stable F
noChange = [stable "n" n]

-- | A program is the algorithm, together with its pre- and post-conditions.
imperativeFib :: Program F
imperativeFib = Program { setup         = axiomatizeFib
                        , precondition  = pre
                        , program       = algorithm
                        , postcondition = post
                        , stability     = noChange
                        }

-- | Correctness. We have:
--
-- >>> correctness
-- Total correctness is established.
-- Q.E.D.
correctness :: IO (ProofResult (FibS Integer))
correctness = wpProveWith defaultWPCfg{wpVerbose=True} imperativeFib
