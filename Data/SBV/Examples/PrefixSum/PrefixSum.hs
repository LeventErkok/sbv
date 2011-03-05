-----------------------------------------------------------------------------
-- |
-- Module      :  Data.SBV.Examples.PrefixSum.PrefixSum
-- Copyright   :  (c) Levent Erkok
-- License     :  BSD3
-- Maintainer  :  erkokl@gmail.com
-- Stability   :  experimental
-- Portability :  portable
--
-- The PrefixSum algorithm over power-lists and proof of
-- the Ladner-Fischer implementation.
-- See <http://www.cs.utexas.edu/users/psp/powerlist.pdf>
-- and <http://www.cs.utexas.edu/~plaxton/c/337/05f/slides/ParallelRecursion-4.pdf>.
-----------------------------------------------------------------------------

{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Data.SBV.Examples.PrefixSum.PrefixSum where

import Data.SBV
import Data.SBV.Internals(runSymbolic)

----------------------------------------------------------------------
-- * Formalizing power-lists
----------------------------------------------------------------------

-- | A poor man's representation of powerlists and
-- basic operations on them: <http://www.cs.utexas.edu/users/psp/powerlist.pdf>.
-- We merely represent power-lists by ordinary lists.
type PowerList a = [a]

-- | The tie operator, concatenation
tiePL :: PowerList a -> PowerList a -> PowerList a
tiePL = (++)

-- | The zip operator, zips the power-lists of the same size, returns
-- a powerlist of double the size.
zipPL :: PowerList a -> PowerList a -> PowerList a
zipPL []     []     = []
zipPL (x:xs) (y:ys) = x : y : zipPL xs ys
zipPL _      _      = error "zipPL: nonsimilar powerlists received"

-- | Inverse of zipping
unzipPL :: PowerList a -> (PowerList a, PowerList a)
unzipPL = unzip . chunk2
  where chunk2 []       = []
        chunk2 (x:y:xs) = (x,y) : chunk2 xs
        chunk2 _        = error "unzipPL: malformed powerlist"

----------------------------------------------------------------------
-- * Reference prefix-sum implementation
----------------------------------------------------------------------

-- | Reference prefix sum (@ps@) is simply Haskell's @scanl1@ function
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

-- | Correctness theorem, for a powerlist of given size, an associative operator, and its left-unit element
flIsCorrect :: Int -> (forall a. (OrdSymbolic a, Bits a) => (a, a -> a -> a)) -> Symbolic SBool
flIsCorrect n zf = do
        args :: PowerList SWord32 <- mkFreeVars n
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
-- SMT solver does not know that the operator associative and has the given left-unit element
--
-- >>> thm3
-- Falsifiable. Counter-example:
--   s0 = 0 :: SWord32
--   s1 = 0 :: SWord32
--   s2 = 0 :: SWord32
--   s3 = 0 :: SWord32
--   s4 = 0 :: SWord32
--   s5 = 0 :: SWord32
--   s6 = 0 :: SWord32
--   s7 = 3221225472 :: SWord32
--   -- uninterpreted: u
--        u  = 0
--   -- uninterpreted: flOp
--        flOp 0 3221225472 = 2147483648
--        flOp 0 2147483648 = 3758096384
--        flOp _ _          = 0
--
-- You can verify that the above function for @flOp@ is not associative:
--
-- @
--   ghci> flOp 3221225472 (flOp 2147483648 3221225472)
--   0
--   ghci> flOp (flOp 3221225472 2147483648) 3221225472
--   2147483648
-- @
--
-- Also, the unit @0@ is clearly not a left-unit for @flOp@, as the third
-- equation for @flOp@ will simply map many elements to @0@.
thm3 :: IO ThmResult
thm3 = prove $ do args :: PowerList SWord32 <- mkFreeVars 8
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
     args :: PowerList SWord32 <- mkFreeVars n
     addAxiom "flOp is associative"     $ assocAxiom (sbvUFName opH)
     addAxiom "u is left-unit for flOp" $ leftUnitAxiom (sbvUFName opH) (sbvUFName uH)
     return $ ps (u, op) args .== lf (u, op) args
  where op :: SWord32 -> SWord32 -> SWord32
        opH :: SBVUF
        (opH, op) = uninterpretWithHandle "flOp"
        u  :: SWord32
        uH :: SBVUF
        (uH, u)  = uninterpretWithHandle "u"
        -- this is the brittle part; but it'll have to do until we get a proper
        -- DSL for expressing SMT-axioms..
        mkCall :: String -> String -> String -> String
        mkCall o x y = "(" ++ o ++ " " ++ x ++ " " ++ y ++ ")"
        assocAxiom :: String -> [String]
        assocAxiom o = [
             ":assumption (forall (?x BitVec[32]) (?y BitVec[32]) (?z BitVec[32])"
           , "                    (= " ++ lhs
           , "                       " ++ rhs
           , "                    )"
           , "            )"
          ]
          where lhs = mkCall o (mkCall o "?x" "?y") "?z"
                rhs = mkCall o "?x" (mkCall o "?y" "?z")
        leftUnitAxiom :: String -> String -> [String]
        leftUnitAxiom o ue = [
            ":assumption (forall (?x BitVec[32])"
          , "                    (= " ++ lhs
          , "                       " ++ rhs
          , "                    )"
          , "            )"
          ]
          where lhs = "(" ++ o ++ " " ++ ue ++ " " ++ "?x" ++ ")"
                rhs = "?x"

-- | Prove the generic problem for powerlists of given sizes. Note that
-- this will only work for Yices-1. This is due to the fact that Yices-2
-- follows the SMT-Lib standard and does not accept bit-vector problems with
-- quantified axioms in them, while Yices-1 did allow for that. The crux of
-- the problem is that there are no SMT-Lib logics that combine BV's and
-- quantifiers, see: <http://goedel.cs.uiowa.edu/smtlib/logics.html>. So we
-- are stuck until new powerful logics are added to SMT-Lib.
--
-- Here, we explicitly tell SBV to use Yices-1 that did not have that limitation.
-- Tweak the executable location accordingly below for your platform..
--
-- We have:
--
-- >>> prefixSum 2
-- Q.E.D.
--
-- >>> prefixSum 4
-- Q.E.D.
--
-- Note that these proofs tend to run long. Also, Yices-1.0.28 ran out of memory
-- and crashed on my box when I tried for size @8@, after running for about 2.5 minutes..
prefixSum :: Int -> IO ThmResult
prefixSum i
  -- Fast way of checking whether a number is a power of two, see: <http://graphics.stanford.edu/~seander/bithacks.html#DetermineIfPowerOf2>
  | i <= 1 || (i .&. (i-1)) /= 0
  = error $ "prefixSum: input must be a power of 2 larger than 2, received: " ++ show i
  | True
  = proveWith cfg $ genPrefixSumInstance i
  where cfg = defaultSMTCfg { solver = yices' }
        yices' = yices { options    = ["-tc", "-smt", "-e"]
                       , executable = "/usr/local/yices-1.0.28/bin/yices"
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
  where gen = runSymbolic $ do args :: [SWord8] <- mkFreeVars n
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
-- AXIOMS
-- DEFINE
--   s8 :: SWord8 = s0 + s1
--   s9 :: SWord8 = s2 + s8
--   s10 :: SWord8 = s3 + s9
--   s11 :: SWord8 = s4 + s10
--   s12 :: SWord8 = s5 + s11
--   s13 :: SWord8 = s6 + s12
--   s14 :: SWord8 = s7 + s13
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
  where gen = runSymbolic $ do args :: [SWord8] <- mkFreeVars n
                               mapM_ output $ ps (0, (+)) args
