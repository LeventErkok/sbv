-----------------------------------------------------------------------------
-- |
-- Module      :  Data.SBV.Examples.BitPrecise.PrefixSum
-- Copyright   :  (c) Levent Erkok
-- License     :  BSD3
-- Maintainer  :  erkokl@gmail.com
-- Stability   :  experimental
--
-- The PrefixSum algorithm over power-lists and proof of
-- the Ladner-Fischer implementation.
-- See <http://www.cs.utexas.edu/users/psp/powerlist.pdf>
-- and <http://www.cs.utexas.edu/~plaxton/c/337/05f/slides/ParallelRecursion-4.pdf>.
-----------------------------------------------------------------------------

{-# LANGUAGE Rank2Types          #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Data.SBV.Examples.BitPrecise.PrefixSum where

import Data.SBV
import qualified Data.SBV.Provers.Yices as Yices
import Data.SBV.Internals(runSymbolic)

----------------------------------------------------------------------
-- * Formalizing power-lists
----------------------------------------------------------------------

-- | A poor man's representation of powerlists and
-- basic operations on them: <http://www.cs.utexas.edu/users/psp/powerlist.pdf>.
-- We merely represent power-lists by ordinary lists.
type PowerList a = [a]

-- | The tie operator, concatenation.
tiePL :: PowerList a -> PowerList a -> PowerList a
tiePL = (++)

-- | The zip operator, zips the power-lists of the same size, returns
-- a powerlist of double the size.
zipPL :: PowerList a -> PowerList a -> PowerList a
zipPL []     []     = []
zipPL (x:xs) (y:ys) = x : y : zipPL xs ys
zipPL _      _      = error "zipPL: nonsimilar powerlists received"

-- | Inverse of zipping.
unzipPL :: PowerList a -> (PowerList a, PowerList a)
unzipPL = unzip . chunk2
  where chunk2 []       = []
        chunk2 (x:y:xs) = (x,y) : chunk2 xs
        chunk2 _        = error "unzipPL: malformed powerlist"

----------------------------------------------------------------------
-- * Reference prefix-sum implementation
----------------------------------------------------------------------

-- | Reference prefix sum (@ps@) is simply Haskell's @scanl1@ function.
ps :: (a, a -> a -> a) -> PowerList a -> PowerList a
ps (_, f) = scanl1 f

----------------------------------------------------------------------
-- * The Ladner-Fischer parallel version
----------------------------------------------------------------------

-- | The Ladner-Fischer (@lf@) implementation of prefix-sum. See <http://www.cs.utexas.edu/~plaxton/c/337/05f/slides/ParallelRecursion-4.pdf>
-- or pg. 16 of <http://www.cs.utexas.edu/users/psp/powerlist.pdf>.
lf :: (a, a -> a -> a) -> PowerList a -> PowerList a
lf _ []         = error "lf: malformed (empty) powerlist"
lf _ [x]        = [x]
lf (zero, f) pl = zipPL (zipWith f (rsh lfpq) p) lfpq
   where (p, q) = unzipPL pl
         pq     = zipWith f p q
         lfpq   = lf (zero, f) pq
         rsh xs = zero : init xs


----------------------------------------------------------------------
-- * Sample proofs for concrete operators
----------------------------------------------------------------------

-- | Correctness theorem, for a powerlist of given size, an associative operator, and its left-unit element.
flIsCorrect :: Int -> (forall a. (OrdSymbolic a, Num a, Bits a) => (a, a -> a -> a)) -> Symbolic SBool
flIsCorrect n zf = do
        args :: PowerList SWord32 <- mkForallVars n
        return $ ps zf args .== lf zf args

-- | Proves Ladner-Fischer is equivalent to reference specification for addition.
-- @0@ is the left-unit element, and we use a power-list of size @8@.
thm1 :: IO ThmResult
thm1 = prove $ flIsCorrect  8 (0, (+))

-- | Proves Ladner-Fischer is equivalent to reference specification for the function @max@.
-- @0@ is the left-unit element, and we use a power-list of size @16@.
thm2 :: IO ThmResult
thm2 = prove $ flIsCorrect 16 (0, smax)

----------------------------------------------------------------------
-- * Attempt at proving for arbitrary operators
----------------------------------------------------------------------
-- | Try proving correctness for an arbitrary operator. This proof will /not/ go through since the
-- SMT solver does not know that the operator associative and has the given left-unit element. We have:
--
-- >>> thm3
-- Falsifiable. Counter-example:
--   s0 = 0 :: SWord32
--   s1 = 0 :: SWord32
--   s2 = 0 :: SWord32
--   s3 = 0 :: SWord32
--   s4 = 1073741824 :: SWord32
--   s5 = 0 :: SWord32
--   s6 = 0 :: SWord32
--   s7 = 0 :: SWord32
--   -- uninterpreted: u
--        u  = 0
--   -- uninterpreted: flOp
--        flOp 0          0          = 2147483648
--        flOp 0          1073741824 = 3221225472
--        flOp 2147483648 0          = 3221225472
--        flOp 2147483648 1073741824 = 1073741824
--        flOp _          _          = 0
--
-- You can verify that the function @flOp@ is indeed not associative:
--
-- @
--   ghci> flOp 3221225472 (flOp 2147483648 1073741824)
--   0
--   ghci> flOp (flOp 3221225472 2147483648) 1073741824
--   3221225472
-- @
--
-- Also, the unit @0@ is clearly not a left-unit for @flOp@, as the last
-- equation for @flOp@ will simply map many elements to @0@.
-- (NB. We need to use yices for this proof as the uninterpreted function
-- examples are only supported through the yices interface currently.)
thm3 :: IO ThmResult
thm3 = proveWith yicesSMT09 $ do args :: PowerList SWord32 <- mkForallVars 8
                                 return $ ps (u, op) args .== lf (u, op) args
  where op :: SWord32 -> SWord32 -> SWord32
        op = uninterpret "flOp"
        u :: SWord32
        u = uninterpret "u"

----------------------------------------------------------------------
-- * Proving for arbitrary operators using axioms
----------------------------------------------------------------------
-- | Generate an instance of the prefix-sum problem for an arbitrary operator, by telling the SMT solver
-- the necessary axioms for associativity and left-unit. The first argument states how wide the power list should be.
genPrefixSumInstance :: Int -> Symbolic SBool
genPrefixSumInstance n = do
     args :: PowerList SWord32 <- mkForallVars n
     addAxiom "flOp is associative"     assocAxiom
     addAxiom "u is left-unit for flOp" leftUnitAxiom
     return $ ps (u, op) args .== lf (u, op) args
  where op :: SWord32 -> SWord32 -> SWord32
        op = uninterpret "flOp"
        u  :: SWord32
        u  = uninterpret "u"
        -- axioms.. These are a bit brittle. Note that we have to
        -- refer to the uninterpreted symbols with the prefix "uninterpreted_" when
        -- used with the SMTLib1 interface to avoid any collision. This is admittedly
        -- ugly, but it'll do till we get a sub-DSL for writing proper axioms (if ever)
        assocAxiom :: [String]
        assocAxiom = [
             ":assumption (forall (?x BitVec[32]) (?y BitVec[32]) (?z BitVec[32])"
           , "                    (= (uninterpreted_flOp ?x (uninterpreted_flOp ?y ?z))"
           , "                       (uninterpreted_flOp (uninterpreted_flOp ?x ?y) ?z)"
           , "                    )"
           , "            )"
          ]
        leftUnitAxiom :: [String]
        leftUnitAxiom = [
            ":assumption (forall (?x BitVec[32]) (= (uninterpreted_flOp uninterpreted_u ?x) ?x))"
          ]

-- | Prove the generic problem for powerlists of given sizes. Note that
-- this only works with Yices-1 currently.
--
-- We have:
--
-- >>> prefixSum 2
-- Q.E.D.
--
-- >>> prefixSum 4
-- Q.E.D.
--
-- Note that these proofs tend to run long. Also, Yices ran out of memory
-- and crashed on my box when I tried for size @8@, after running for about 2.5 minutes..
prefixSum :: Int -> IO ThmResult
prefixSum i
  -- Fast way of checking whether a number is a power of two, see: <http://graphics.stanford.edu/~seander/bithacks.html#DetermineIfPowerOf2>
  | i <= 1 || (i .&. (i-1)) /= 0
  = error $ "prefixSum: input must be a power of 2 larger than 2, received: " ++ show i
  | True
  = proveWith yices1029 $ genPrefixSumInstance i

-- | Old version of Yices that supports quantified axioms in SMT-Lib1
yices1029 :: SMTConfig
yices1029 = yices {solver = yices'}
  where yices' = Yices.yices { options    = ["-tc", "-smt", "-e"]
                             , executable = "yices-1.0.29"
                             }

-- | Another old version of yices, suitable for the non-axiom based problem
yicesSMT09 :: SMTConfig
yicesSMT09 = yices {solver = yices'}
  where yices' = Yices.yices { options    = ["-m"]
                             , executable = "yices-SMT09"
                             }

----------------------------------------------------------------------
-- * Inspecting symbolic traces
----------------------------------------------------------------------

-- | A symbolic trace can help illustrate the action of Ladner-Fischer. This
-- generator produces the actions of Ladner-Fischer for addition, showing how
-- the computation proceeds:
--
-- >>> ladnerFischerTrace 8
-- INPUTS
--   s0 :: SWord8
--   s1 :: SWord8
--   s2 :: SWord8
--   s3 :: SWord8
--   s4 :: SWord8
--   s5 :: SWord8
--   s6 :: SWord8
--   s7 :: SWord8
-- CONSTANTS
--   s_2 = False
--   s_1 = True
-- TABLES
-- ARRAYS
-- UNINTERPRETED CONSTANTS
-- USER GIVEN CODE SEGMENTS
-- AXIOMS
-- DEFINE
--   s8 :: SWord8 = s0 + s1
--   s9 :: SWord8 = s2 + s8
--   s10 :: SWord8 = s2 + s3
--   s11 :: SWord8 = s8 + s10
--   s12 :: SWord8 = s4 + s11
--   s13 :: SWord8 = s4 + s5
--   s14 :: SWord8 = s11 + s13
--   s15 :: SWord8 = s6 + s14
--   s16 :: SWord8 = s6 + s7
--   s17 :: SWord8 = s13 + s16
--   s18 :: SWord8 = s11 + s17
-- CONSTRAINTS
-- OUTPUTS
--   s0
--   s8
--   s9
--   s11
--   s12
--   s14
--   s15
--   s18
ladnerFischerTrace :: Int -> IO ()
ladnerFischerTrace n = gen >>= print
  where gen = runSymbolic (True, Nothing) $ do args :: [SWord8] <- mkForallVars n
                                               mapM_ output $ lf (0, (+)) args

-- | Trace generator for the reference spec. It clearly demonstrates that the reference
-- implementation fewer operations, but is not parallelizable at all:
--
-- >>> scanlTrace 8
-- INPUTS
--   s0 :: SWord8
--   s1 :: SWord8
--   s2 :: SWord8
--   s3 :: SWord8
--   s4 :: SWord8
--   s5 :: SWord8
--   s6 :: SWord8
--   s7 :: SWord8
-- CONSTANTS
--   s_2 = False
--   s_1 = True
-- TABLES
-- ARRAYS
-- UNINTERPRETED CONSTANTS
-- USER GIVEN CODE SEGMENTS
-- AXIOMS
-- DEFINE
--   s8 :: SWord8 = s0 + s1
--   s9 :: SWord8 = s2 + s8
--   s10 :: SWord8 = s3 + s9
--   s11 :: SWord8 = s4 + s10
--   s12 :: SWord8 = s5 + s11
--   s13 :: SWord8 = s6 + s12
--   s14 :: SWord8 = s7 + s13
-- CONSTRAINTS
-- OUTPUTS
--   s0
--   s8
--   s9
--   s10
--   s11
--   s12
--   s13
--   s14
--
scanlTrace :: Int -> IO ()
scanlTrace n = gen >>= print
  where gen = runSymbolic (True, Nothing) $ do args :: [SWord8] <- mkForallVars n
                                               mapM_ output $ ps (0, (+)) args

{-# ANN module ("HLint: ignore Reduce duplication" :: String) #-}
