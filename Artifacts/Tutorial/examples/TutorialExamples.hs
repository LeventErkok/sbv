{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE FlexibleInstances   #-}
{-# LANGUAGE OverloadedLists     #-}
{-# LANGUAGE QuasiQuotes         #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell     #-}
{-# LANGUAGE TypeApplications    #-}

-- Executable companion for the SBV tutorial. Every listing in the manuscript
-- that is delimited by BEGIN/END markers below is extracted from this file by
-- prepare.py, so the text and the checked code cannot drift apart.
module Main (main) where

import Control.Exception (SomeException, try)
import Control.Monad (unless, void)
import Data.List (sort)
import System.Environment (getArgs)
import qualified System.Timeout as Timeout

import Data.SBV
import Data.SBV.Control
import qualified Data.SBV.List as SL
import Data.SBV.TP
import Data.SBV.Tools.CodeGen
import qualified Documentation.SBV.Examples.TP.TautologyChecker as Taut

-------------------------------------------------------------------------------
-- Section: Writing specifications
-------------------------------------------------------------------------------

-- BEGIN saturating
satAdd :: SWord8 -> SWord8 -> SWord8
satAdd x y = ite (x .> 255 - y) 255 (x + y)

satAddSpec :: SWord8 -> SWord8 -> SBool
satAddSpec x y = sFromIntegral (satAdd x y) .== ite (total .> 255) 255 total
  where total = sFromIntegral x + sFromIntegral y :: SInteger
-- END saturating

-- BEGIN wrongAdd
wrongAdd :: SWord8 -> SWord8 -> SWord8
wrongAdd x y = ite (x + y .> 255) 255 (x + y)

wrongAddSpec :: SWord8 -> SWord8 -> SBool
wrongAddSpec x y = sFromIntegral (wrongAdd x y) .== ite (total .> 255) 255 total
  where total = sFromIntegral x + sFromIntegral y :: SInteger
-- END wrongAdd

-- The counterexample to wrongAddSpec must fail an ordinary Haskell oracle.
wrongAddRefuted :: IO Bool
wrongAddRefuted = do
  result <- prove $ do x <- sWord8 "x"
                       y <- sWord8 "y"
                       pure $ wrongAddSpec x y
  print result
  pure $ case (getModelValue "x" result, getModelValue "y" result) of
    (Just (x :: Word8), Just (y :: Word8)) ->
      toInteger (x + y) /= min 255 (toInteger x + toInteger y)
    _ -> False

-------------------------------------------------------------------------------
-- Section: Finding values
-------------------------------------------------------------------------------

-- BEGIN idempotent
idempotentBytes :: IO AllSatResult
idempotentBytes = allSat $ \(x :: SWord8) -> x * x .== x
-- END idempotent

-- BEGIN production
production :: IO OptimizeResult
production = optimize Lexicographic $ do
  x <- sInteger "x"
  y <- sInteger "y"
  constrain $ x .>= 0 .&& y .>= 0
  constrain $ x + 2 * y .<= 10
  constrain $ 3 * x + y .<= 15
  maximize "profit" (2 * x + 3 * y)
-- END production

productionOptimal :: IO Bool
productionOptimal = do
  r <- production
  print r
  pure $ case r of
    LexicographicResult m -> getModelValue "profit" m == Just (17 :: Integer)
    _                     -> False

-------------------------------------------------------------------------------
-- Section: Host structure versus symbolic structure
-------------------------------------------------------------------------------

-- BEGIN hostSum
nonNegSum :: Int -> Predicate
nonNegSum n = do
  xs <- mapM (\i -> sInteger ("x" ++ show i)) [1 .. n]
  pure $ sAll (.>= 0) xs .=> sum xs .>= 0
-- END hostSum

-- BEGIN sumL
sumL :: SList Integer -> SInteger
sumL = smtFunction "sumL" $ \xs -> [sCase| xs of
          []     -> 0
          y : ys -> y + sumL ys
       |]
-- END sumL

-------------------------------------------------------------------------------
-- Section: Programming the solver
-------------------------------------------------------------------------------

-- BEGIN descent
smallest :: IO Integer
smallest = runSMT $ do
  x <- sInteger "x"
  constrain $ x .> 10
  constrain $ x `sMod` 7 .== 3
  constrain $ x `sMod` 5 .== 4
  query $ let descend best = do
                r <- checkSat
                case r of
                  Sat   -> do v <- getValue x
                              constrain $ x .< literal v
                              descend (Just v)
                  Unsat -> maybe (io $ fail "no solution") pure best
                  _     -> io $ fail "inconclusive"
          in descend Nothing
-- END descent

-- Exercise 2 solution: the largest such value below 100.
largestBelow100 :: IO Integer
largestBelow100 = runSMT $ do
  x <- sInteger "x"
  constrain $ x .> 10 .&& x .< 100
  constrain $ x `sMod` 7 .== 3
  constrain $ x `sMod` 5 .== 4
  query $ let ascend best = do
                r <- checkSat
                case r of
                  Sat   -> do v <- getValue x
                              constrain $ x .> literal v
                              ascend (Just v)
                  Unsat -> maybe (io $ fail "no solution") pure best
                  _     -> io $ fail "inconclusive"
          in ascend Nothing

-------------------------------------------------------------------------------
-- Section: Symbolic datatypes
-------------------------------------------------------------------------------

-- BEGIN expr
data Expr = Num Integer
          | Add Expr Expr
          | Mul Expr Expr
          deriving Show
mkSymbolic [''Expr]

eval :: SExpr -> SInteger
eval = smtFunction "eval" $ \e -> [sCase| e of
          Num n   -> n
          Add a b -> eval a + eval b
          Mul a b -> eval a * eval b
       |]

puzzle :: IO SatResult
puzzle = sat $ \e -> eval e .== 42 .&& isMul e .&& sNot (isNum (getMul_1 e))
-- END expr

-- Concrete re-evaluation of the model, independent of the solver.
evalC :: Expr -> Integer
evalC (Num n)   = n
evalC (Add a b) = evalC a + evalC b
evalC (Mul a b) = evalC a * evalC b

puzzleChecked :: IO Bool
puzzleChecked = do
  r <- puzzle
  print r
  pure $ case getModelValue "s0" r of
    Just e@(Mul a _) | not (isNumC a) -> evalC e == 42
    _                                 -> False
  where isNumC Num{} = True
        isNumC _     = False

-- Datatype introduced only inside a query: registration must follow use.
newtype Box a = Box a deriving (Eq, Ord, Show)
mkSymbolic [''Box]

lateDatatype :: IO CheckSatResult
lateDatatype = runSMT $ query $ do
  x <- freshVar @(Box Word8) "x"
  y <- freshVar @(Box Word8) "y"
  constrain $ x ./= y
  checkSat

-------------------------------------------------------------------------------
-- Section: Proofs by induction
-------------------------------------------------------------------------------

-- BEGIN sumNonNeg
sumNonNeg :: TP (Proof (Forall "xs" [Integer] -> SBool))
sumNonNeg = induct "sumNonNeg"
  (\(Forall xs) -> SL.all (.>= 0) xs .=> sumL xs .>= 0) $
  \ih (x, xs) -> [SL.all (.>= 0) (x .: xs)]
              |- sumL (x .: xs) .>= 0
              =: x + sumL xs .>= 0
              ?? ih
              =: sTrue
              =: qed
-- END sumNonNeg

-- BEGIN revAcc
revAcc :: SList Integer -> SList Integer -> SList Integer
revAcc = smtFunction "revAcc" $ \acc xs -> [sCase| xs of
            []     -> acc
            x : xt -> revAcc (x .: acc) xt
         |]
-- END revAcc

-- BEGIN revWeak
revWeak :: TP (Proof (Forall "xs" [Integer] -> SBool))
revWeak = induct "revWeak"
  (\(Forall xs) -> revAcc [] xs .== SL.reverse xs) $
  \ih (x, xs) -> [] |- revAcc [] (x .: xs)
                    =: revAcc [x] xs
                    ?? ih
                    =: SL.reverse xs SL.++ [x]
                    =: SL.reverse (x .: xs)
                    =: qed
-- END revWeak

-- The weak attempt must fail; we bound each solver call so the failure is prompt.
revWeakFails :: IO Bool
revWeakFails = do
  let cfg = z3 { solverSetOptions = solverSetOptions z3 ++ [SetTimeOut 5000] }
  r <- tryTP (runTPWith cfg revWeak)
  pure (not r)

-- BEGIN revAccCorrect
revAccCorrect :: TP (Proof (Forall "xs" [Integer] -> Forall "acc" [Integer] -> SBool))
revAccCorrect = induct "revAccCorrect"
  (\(Forall xs) (Forall acc) -> revAcc acc xs .== SL.reverse xs SL.++ acc) $
  \ih (x, xs) acc -> [] |- revAcc acc (x .: xs)
                        =: revAcc (x .: acc) xs
                        ?? ih
                        =: SL.reverse xs SL.++ (x .: acc)
                        =: (SL.reverse xs SL.++ [x]) SL.++ acc
                        =: SL.reverse (x .: xs) SL.++ acc
                        =: qed
-- END revAccCorrect

-- Exercise 3 solution.
revAccLength :: TP (Proof (Forall "xs" [Integer] -> Forall "acc" [Integer] -> SBool))
revAccLength = induct "revAccLength"
  (\(Forall xs) (Forall acc) -> SL.length (revAcc acc xs) .== SL.length xs + SL.length acc) $
  \ih (x, xs) acc -> [] |- SL.length (revAcc acc (x .: xs))
                        =: SL.length (revAcc (x .: acc) xs)
                        ?? ih
                        =: SL.length xs + SL.length (x .: acc)
                        =: SL.length (x .: xs) + SL.length acc
                        =: qed

-------------------------------------------------------------------------------
-- Section: Kadane's algorithm
-------------------------------------------------------------------------------

-- BEGIN mss
mss :: SList Integer -> SInteger
mss = smtFunction "mss" $ \xs -> [sCase| xs of
         []    -> 0
         _ : t -> mssBegin xs `smax` mss t
      |]

mssBegin :: SList Integer -> SInteger
mssBegin = smtFunction "mssBegin" $ \xs -> [sCase| xs of
              []    -> 0
              h : t -> 0 `smax` (h `smax` (h + mssBegin t))
           |]
-- END mss

-- BEGIN kadane
kadane :: SList Integer -> SInteger
kadane xs = kadaneHelper xs 0 0

kadaneHelper :: SList Integer -> SInteger -> SInteger -> SInteger
kadaneHelper = smtFunction "kadaneHelper" $ \xs meh msf -> [sCase| xs of
                  []    -> msf
                  h : t -> let meh' = 0 `smax` (h + meh)
                               msf' = msf `smax` meh'
                           in kadaneHelper t meh' msf'
               |]
-- END kadane

-- BEGIN kadaneCorrect
kadaneCorrect :: TP (Proof (Forall "xs" [Integer] -> SBool))
kadaneCorrect = do
  inv <- induct "kadaneInvariant"
           (\(Forall xs) (Forall meh) (Forall msf) ->
                    (meh .>= 0 .&& msf .>= meh)
                .=> kadaneHelper xs meh msf
                    .== msf `smax` mss xs `smax` (meh + mssBegin xs)) $
           \ih (a, as) meh msf ->
              [meh .>= 0, msf .>= meh]
           |- let meh' = 0 `smax` (a + meh)
                  msf' = msf `smax` meh'
              in kadaneHelper (a .: as) meh msf
              =: kadaneHelper as meh' msf'
              ?? ih `at` (Inst @"meh" meh', Inst @"msf" msf')
              =: msf' `smax` mss as `smax` (meh' + mssBegin as)
              =: qed

  calc "kadaneCorrect" (\(Forall xs) -> kadane xs .== mss xs) $
       \xs -> let z = 0 :: SInteger
             in [] |- kadane xs
                   =: kadaneHelper xs z z
                   ?? inv `at` (Inst @"xs" xs, Inst @"meh" z, Inst @"msf" z)
                   =: z `smax` mss xs `smax` (z + mssBegin xs)
                   =: mss xs `smax` mssBegin xs
                   =: mss xs
                   =: qed
-- END kadaneCorrect

-- Concrete sanity checks: symbolic functions evaluate on literal lists.
kadaneConcrete :: IO Bool
kadaneConcrete = pure $ and
  [ unliteral (f xs) == Just e
  | f <- [mss, kadane]
  , (xs, e) <- [([1, -2, 3, 4, -1, 2], 8), ([-2, -3, -1], 0), ([1, 2, 3], 6)]
  ]

-------------------------------------------------------------------------------
-- Section: Generating C
-------------------------------------------------------------------------------

-- BEGIN codegen
generateAdder :: FilePath -> IO ()
generateAdder dir = compileToC (Just dir) "sat_add" $ do
  cgOverwriteFiles True
  cgGenerateDriver False
  x <- cgInput "x"
  y <- cgInput "y"
  cgReturn $ satAdd x y
-- END codegen

-------------------------------------------------------------------------------
-- Exercise 1 solution: saturating subtraction.
-------------------------------------------------------------------------------

satSub :: SWord8 -> SWord8 -> SWord8
satSub x y = ite (y .> x) 0 (x - y)

satSubSpec :: SWord8 -> SWord8 -> SBool
satSubSpec x y = sFromIntegral (satSub x y) .== ite (diff .< 0) 0 diff
  where diff = sFromIntegral x - sFromIntegral y :: SInteger

-------------------------------------------------------------------------------
-- Driver
-------------------------------------------------------------------------------

-- Run a TP script, reporting failure as False rather than an exception.
tryTP :: forall a. IO a -> IO Bool
tryTP act = either (const False) (const True) <$> (try act :: IO (Either SomeException a))

check :: String -> IO Bool -> IO ()
check name action = do
  result <- Timeout.timeout (120 * 1000000) action
  unless (result == Just True) $ fail (name ++ ": failed or timed out")
  putStrLn $ "PASS " ++ name

main :: IO ()
main = do
  args <- getArgs
  case args of
    ["--generate", dir] -> generateAdder dir
    ["--tautology"] -> do
      check "tautology checker soundness"    $ void (runTP Taut.soundness)              >> pure True
      check "tautology checker completeness" $ void (runTPWith cvc5 Taut.completeness)  >> pure True
    [] -> do
      check "integer absolute value is nonnegative" $
        isTheorem $ \x -> abs (x :: SInteger) .>= 0
      check "Int8 absolute value counterexample is -128" $ do
        r <- prove $ \x -> abs (x :: SInt8) .>= 0
        print r
        pure $ getModelValue "s0" r == Just (-128 :: Int8)
      check "float reflexivity counterexample is NaN" $ do
        r <- prove $ \(x :: SFloat) -> x .== x
        print r
        pure $ maybe False isNaN (getModelValue "s0" r :: Maybe Float)
      check "saturating addition theorem" $ isTheorem satAddSpec
      check "incorrect overflow guard is refuted, checked by an oracle" wrongAddRefuted
      check "idempotent bytes are exactly 0 and 1" $ do
        r <- idempotentBytes
        print r
        pure $ sort (extractModels r) == ([0, 1] :: [Word8])
      check "production plan optimum is 17" productionOptimal
      check "host-list sum of five nonnegatives" $ isTheorem (nonNegSum 5)
      check "query descent finds 24" $ (== 24) <$> smallest
      check "datatype puzzle model re-evaluates to 42" puzzleChecked
      check "datatype first introduced during query" $ (== Sat) <$> lateDatatype
      check "sum of nonnegatives, by induction" $ void (runTP sumNonNeg) >> pure True
      check "non-generalized reversal proof fails" revWeakFails
      check "generalized accumulator reversal" $ void (runTP revAccCorrect) >> pure True
      check "Kadane on literal lists" kadaneConcrete
      check "Kadane correctness" $ void (runTP kadaneCorrect) >> pure True
      check "exercise 1: saturating subtraction" $ isTheorem satSubSpec
      check "exercise 2: largest below 100 is 94" $ (== 94) <$> largestBelow100
      check "exercise 3: revAcc length" $ void (runTP revAccLength) >> pure True
    _ -> fail "Usage: tutorial-examples [--tautology | --generate DIR]"
