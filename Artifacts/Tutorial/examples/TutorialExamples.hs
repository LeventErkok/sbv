-- BEGIN extensions
{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE FlexibleInstances   #-}
{-# LANGUAGE OverloadedLists     #-}
{-# LANGUAGE QuasiQuotes         #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell     #-}
{-# LANGUAGE TypeApplications    #-}
-- END extensions

-- Executable companion for the SBV tutorial. Every listing in the manuscript
-- that is delimited by BEGIN/END markers below is extracted from this file by
-- prepare.py, so the text and the checked code cannot drift apart.
module Main (main) where

import Control.Exception (ErrorCall, displayException, try)
import Control.Monad (replicateM, unless, void)
import Data.List (inits, isInfixOf, sort, tails)
import System.Environment (getArgs)
import qualified System.Timeout as Timeout

-- BEGIN imports
import Data.SBV
import Data.SBV.Control
import qualified Data.SBV.List as SL
import Data.SBV.TP
import Data.SBV.Tools.CodeGen
-- END imports
-- BEGIN listProofImports
import qualified Documentation.SBV.Examples.TP.Lists as ListProofs
-- END listProofImports
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

-- BEGIN randomSatAdd
testSatAdd :: IO Bool
testSatAdd = sbvQuickCheck $ satAddSpec <$> sWord8 "x" <*> sWord8 "y"
-- END randomSatAdd

-- BEGIN inspectSatAdd
inspectSatAdd :: FilePath -> IO ThmResult
inspectSatAdd path = proveWith
  z3{verbose = True, transcript = Just path} satAddSpec
-- END inspectSatAdd

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

-------------------------------------------------------------------------------
-- Section: Optimization
-------------------------------------------------------------------------------

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
  -- Independently enumerate all feasible plans within the resource bounds.
  let plans = [(x, y) | x <- [0 .. 5], y <- [0 .. 5],
                       x + 2 * y <= 10, 3 * x + y <= (15 :: Integer)]
  pure $ case r of
    LexicographicResult m ->
      case (getModelValue "x" m, getModelValue "y" m, getModelValue "profit" m) of
        (Just x, Just y, Just p) -> (x, y) `elem` plans && p == 2 * x + 3 * y
                                 && p == maximum [2 * a + 3 * b | (a, b) <- plans]
        _ -> False
    _ -> False

-- BEGIN realBounds
realBounds :: IO OptimizeResult
realBounds = optimize Independent $ do
  x <- sReal "x"
  constrain $ x .> 0
  minimize "lower" x
  maximize "upper" x
-- END realBounds

realBoundsChecked :: IO Bool
realBoundsChecked = do
  r <- realBounds
  print r
  pure $ case r of
    IndependentResult rs -> sort (map fst rs) == ["lower", "upper"]
                         && all (boundsMatch . snd) rs
    _ -> False
  where boundsMatch m = case (getModelObjectiveValue "lower" m,
                             getModelObjectiveValue "upper" m) of
          (Just (ExtendedCV Epsilon{}), Just (ExtendedCV Infinite{})) -> True
          _ -> False

-------------------------------------------------------------------------------
-- Section: Host structure versus symbolic structure
-------------------------------------------------------------------------------

-- BEGIN hostSum
nonNegSum :: Int -> Predicate
nonNegSum n = do
  xs <- mapM (\i -> sInteger ("x" ++ show i)) [1 .. n]
  pure $ sAll (.>= 0) xs .=> sum xs .>= 0
-- END hostSum

-- The integer premise is feasible; the byte premise is contradictory.
assumptionsChecked :: IO Bool
assumptionsChecked = do
  feasible <- isSatisfiable $ \(x :: SInteger) -> x + 1 .> x
  impossible <- isSatisfiable $ \(x :: SWord8) -> x .> 255
  vacuous <- isTheorem $ \(x :: SWord8) -> x .> 255 .=> x .== 0
  pure $ feasible && not impossible && vacuous

-- BEGIN sumL
sumL :: SList Integer -> SInteger
sumL = smtFunction "sumL" $ \xs -> [sCase| xs of
          []     -> 0
          y : ys -> y + sumL ys
       |]
-- END sumL

-- BEGIN sumWithoutInduction
z3Timeout5 :: SMTConfig
z3Timeout5 = z3 { solverSetOptions = solverSetOptions z3 ++ [SetTimeOut 5000] }

sumWithoutInduction :: IO ThmResult
sumWithoutInduction =
  proveWith z3Timeout5 $
    \xs -> SL.all (.>= 0) xs .=> sumL xs .>= 0
-- END sumWithoutInduction

-------------------------------------------------------------------------------
-- Section: Arrays and symbolic memory
-------------------------------------------------------------------------------

-- BEGIN writesCommute
writesCommute :: SArray Integer Integer
              -> SInteger -> SInteger -> SInteger -> SInteger -> SBool
writesCommute a i j x y =
  i ./= j .=>
    writeArray (writeArray a i x) j y .==
    writeArray (writeArray a j y) i x
-- END writesCommute

arrayAliasingRefuted :: IO Bool
arrayAliasingRefuted = do
  result <- prove $ do
    a <- sArray "a" :: Symbolic (SArray Integer Integer)
    i <- sInteger "i"
    j <- sInteger "j"
    x <- sInteger "x"
    y <- sInteger "y"
    pure $ writeArray (writeArray a i x) j y .==
           writeArray (writeArray a j y) i x
  print result
  pure $ case (getModelValue "i" result, getModelValue "j" result,
               getModelValue "x" result, getModelValue "y" result) of
    (Just i, Just j, Just x, Just (y :: Integer)) ->
      -- Newest binding first: lookup independently checks the last write wins.
      i == (j :: Integer) && x /= y &&
      lookup i [(j, y), (i, x)] /= lookup i [(i, x), (j, y)]
    _ -> False

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
  r <- try (void (runTPWith z3Timeout5 revWeak)) :: IO (Either ErrorCall ())
  case r of
    Left err -> do putStrLn (displayException err)
                   pure $ takeWhile (/= '\n') (displayException err) == "Failed"
    Right () -> pure False

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

-- BEGIN reverseCorrect
reverseCorrect :: TP (Proof (Forall "xs" [Integer] -> SBool))
reverseCorrect = do
  generalized <- recall revAccCorrect
  lemma "reverseCorrect"
    (\(Forall xs) -> revAcc [] xs .== SL.reverse xs)
    [proofOf generalized]
-- END reverseCorrect

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

-- BEGIN reverseLength
reverseLength :: forall a. SymVal a => TP (Proof (Forall "xs" [a] -> SBool))
reverseLength = induct "reverseLength"
  (\(Forall xs) -> SL.length (SL.reverse xs) .== SL.length xs) $
  \ih (x, xs) -> [] |- SL.length (SL.reverse (x .: xs))
                    =: SL.length (SL.reverse xs SL.++ [x])
                    =: SL.length (SL.reverse xs) + 1
                    ?? ih
                    =: SL.length xs + 1
                    =: SL.length (x .: xs)
                    =: qed
-- END reverseLength

-------------------------------------------------------------------------------
-- Section: Higher-order proofs
-- Adapted from Documentation.SBV.Examples.TP.Lists.bookKeeping.
-------------------------------------------------------------------------------

-- The helper is proved here; foldr-over-append is reused from the library.
foldBase :: forall a. SymVal a
         => SBV a -> (SBV a -> SBV a -> SBV a)
         -> TP (Proof (Forall "xs" [a] -> Forall "y" a -> SBool))
foldBase e f = do
  let assoc = quantifiedBool $ \(Forall x) (Forall y) (Forall z) ->
                f x (f y z) .== f (f x y) z
      lUnit = quantifiedBool $ \(Forall x) -> f e x .== x
  induct "foldBase"
    (\(Forall xs) (Forall y) -> lUnit .&& assoc .=>
       SL.foldr f y xs .== f (SL.foldr f e xs) y) $
    \ih (x, xs) y -> [lUnit, assoc] |- SL.foldr f y (x .: xs)
                                    =: f x (SL.foldr f y xs)
                                    ?? ih
                                    =: f x (f (SL.foldr f e xs) y)
                                    =: f (f x (SL.foldr f e xs)) y
                                    =: f (SL.foldr f e (x .: xs)) y
                                    =: qed

-- BEGIN bookKeeping
bookKeeping :: forall a. SymVal a
            => SBV a -> (SBV a -> SBV a -> SBV a)
            -> TP (Proof (Forall "xss" [[a]] -> SBool))
bookKeeping e f = do
  let assoc = quantifiedBool $ \(Forall x) (Forall y) (Forall z) ->
                f x (f y z) .== f (f x y) z
      rUnit = quantifiedBool $ \(Forall x) -> f x e .== x
      lUnit = quantifiedBool $ \(Forall x) -> f e x .== x
      reduce = SL.foldr f e
  base <- foldBase e f
  over <- ListProofs.foldrOverAppend e f
  induct "bookKeeping"
    (\(Forall xss) -> assoc .&& rUnit .&& lUnit .=>
       reduce (SL.concat xss) .== reduce (SL.map reduce xss)) $
    \ih (xs, xss) -> [assoc, rUnit, lUnit] |- reduce (SL.concat (xs .: xss))
      =: reduce (xs SL.++ SL.concat xss)
      ?? over
      =: SL.foldr f (reduce (SL.concat xss)) xs
      ?? ih
      =: SL.foldr f (reduce (SL.map reduce xss)) xs
      ?? base `at` (Inst @"xs" xs, Inst @"y" (reduce (SL.map reduce xss)))
      =: f (reduce xs) (reduce (SL.map reduce xss))
      =: reduce (reduce xs .: SL.map reduce xss)
      =: reduce (SL.map reduce (xs .: xss))
      =: qed
-- END bookKeeping

-- BEGIN bookKeepingRun
bookKeepingAbstract :: IO (Proof (Forall "xss" [[Integer]] -> SBool))
bookKeepingAbstract = runTP $
  bookKeeping @Integer (uninterpret "unit") (uninterpret "combine")
-- END bookKeepingRun

-- A concrete instance, with no algebraic assumptions left in the conclusion.
bookKeepingSum :: TP (Proof (Forall "xss" [[Integer]] -> SBool))
bookKeepingSum = do
  law <- bookKeeping @Integer 0 (+)
  lemma "bookKeepingSum"
    (\(Forall xss) -> SL.sum (SL.concat xss) .== SL.sum (SL.map SL.sum xss))
    [proofOf law]

-- Dropping the left-unit premise is unsound, even for an associative operator
-- with a right unit: left projection, with unit 0 and input [[], [1]].
bookKeepingNeedsLeftUnit :: IO Bool
bookKeepingNeedsLeftUnit = pure $
  let f :: SInteger -> SInteger -> SInteger
      f x _ = x
      xss = literal [[], [1 :: Integer]]
      reduce = SL.foldr f 0
  in unliteral (reduce (SL.concat xss)) == Just 1
     && unliteral (reduce (SL.map reduce xss)) == Just 0

-- BEGIN closure
shiftEach :: SInteger -> SList Integer -> SList Integer
shiftEach k = SL.map Closure { closureEnv = k
                            , closureFun = \env x -> x + env
                            }
-- END closure

shiftLength :: TP (Proof (Forall "xs" [Integer] -> Forall "k" Integer -> SBool))
shiftLength = induct "shiftLength"
  (\(Forall xs) (Forall k) -> SL.length (shiftEach k xs) .== SL.length xs) $
  \ih (x, xs) k -> [] |- SL.length (shiftEach k (x .: xs))
                      =: 1 + SL.length (shiftEach k xs)
                      ?? ih
                      =: 1 + SL.length xs
                      =: SL.length (x .: xs)
                      =: qed

-------------------------------------------------------------------------------
-- Termination: a non-decreasing recursive call must be rejected before proving.
-------------------------------------------------------------------------------

badRecursion :: SInteger -> SInteger
badRecursion = smtFunction "badRecursion" $ \n -> badRecursion n + 1

badRecursionRejected :: IO Bool
badRecursionRejected = do
  let property :: Forall "n" Integer -> SBool
      property (Forall n) = badRecursion n .== 0
  r <- try (void (runTP $ lemma "badRecursionRejected"
                     property []))
         :: IO (Either ErrorCall ())
  case r of
    Left err -> do putStrLn (displayException err)
                   pure $ "Cannot determine a termination measure" `isInfixOf` displayException err
    Right () -> pure False

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

-- BEGIN segmentOracle
segmentOracle :: [Integer] -> Integer
segmentOracle xs = maximum [sum segment | suffix <- tails xs, segment <- inits suffix]
-- END segmentOracle

-- Every contiguous segment is a prefix of a suffix, including the empty one.
-- This oracle does not use either symbolic recurrence.
kadaneConcrete :: IO Bool
kadaneConcrete = pure $ and
  [ unliteral (f (literal xs)) == Just (segmentOracle xs)
  | xs <- concatMap (\n -> replicateM n [-2 .. 2]) ([0 .. 5] :: [Int])
          ++ [[1, -2, 3, 4, -1, 2], [-2, -3, -1], [1, 2, 3]]
  , f <- [mss, kadane]
  ]

-------------------------------------------------------------------------------
-- Section: Induction over datatypes
-------------------------------------------------------------------------------

-- BEGIN exprMirror
mirror :: SExpr -> SExpr
mirror = smtFunction "mirror" $ \e -> [sCase| e of
  Num n   -> sNum n
  Add a b -> sAdd (mirror b) (mirror a)
  Mul a b -> sMul (mirror b) (mirror a)
  |]
-- END exprMirror

exprSize :: SExpr -> SInteger
exprSize = smtFunction "exprSize" $ \e -> [sCase| e of
  Num _   -> 0
  Add a b -> 1 + exprSize a + exprSize b
  Mul a b -> 1 + exprSize a + exprSize b
  |]

exprSizePos :: TP (Proof (Forall "e" Expr -> SBool))
exprSizePos = inductiveLemma "exprSizePos"
  (\(Forall e) -> exprSize e .>= 0) []

exprSizeSmaller :: TP (Proof (Forall "a" Expr -> Forall "b" Expr -> SBool))
exprSizeSmaller = do
  pos <- recall exprSizePos
  lemma "exprSizeSmaller"
    (\(Forall a) (Forall b) ->
      let smaller parent = exprSize a .< exprSize parent .&&
                           exprSize b .< exprSize parent
      in smaller (sAdd a b) .&& smaller (sMul a b)) [proofOf pos]

-- BEGIN mirrorCorrect
mirrorCorrect :: TP (Proof (Forall "e" Expr -> SBool))
mirrorCorrect = do
  pos <- recall exprSizePos
  smaller <- recall exprSizeSmaller
  sInduct "mirrorCorrect" (\(Forall e) -> eval (mirror e) .== eval e)
    (exprSize, [proofOf pos]) $ \ih e -> [] |- [pCase| e of
      Num n -> eval (mirror (sNum n)) =: eval (sNum n) =: qed
      Add a b -> eval (mirror (sAdd a b))
              =: eval (mirror b) + eval (mirror a)
              ?? smaller `at` (Inst @"a" a, Inst @"b" b)
              ?? ih `at` Inst @"e" a
              ?? ih `at` Inst @"e" b
              =: eval b + eval a
              =: eval a + eval b
              =: eval (sAdd a b)
              =: eval e
              =: qed
      -- PAPER-ELIDE-BEGIN Mul a b -> -- as for Add, with (*) in place of (+)
      Mul a b -> eval (mirror (sMul a b))
              =: eval (mirror b) * eval (mirror a)
              ?? smaller `at` (Inst @"a" a, Inst @"b" b)
              ?? ih `at` Inst @"e" a
              ?? ih `at` Inst @"e" b
              =: eval b * eval a
              =: eval a * eval b
              =: eval (sMul a b)
              =: eval e
              =: qed
      -- PAPER-ELIDE-END
      |]
-- END mirrorCorrect

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
    ["--diagnostics", path] ->
      check "verbose proof with replayable transcript" $ do
        result <- inspectSatAdd path
        pure $ case result of
          ThmResult Unsatisfiable{} -> True
          _                        -> False
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
      check "random testing of saturating addition" testSatAdd
      check "saturating addition theorem" $ isTheorem satAddSpec
      check "incorrect overflow guard is refuted, checked by an oracle" wrongAddRefuted
      check "idempotent bytes are exactly 0 and 1" $ do
        r <- idempotentBytes
        print r
        pure $ sort (extractModels r) == ([0, 1] :: [Word8])
      check "production plan optimum is 17" productionOptimal
      check "real bounds report epsilon and infinity (version-specific)" realBoundsChecked
      check "host-list sum of five nonnegatives" $ isTheorem (nonNegSum 5)
      check "feasible assumptions and vacuous byte property" assumptionsChecked
      check "bounded automatic sum attempt: unknown or proved, never refuted" $ do
        r <- sumWithoutInduction
        print r
        pure $ case r of
          ThmResult Unknown{}       -> True
          ThmResult Unsatisfiable{} -> True
          _                         -> False
      check "query descent finds 24" $ (== 24) <$> smallest
      check "array writes commute at distinct addresses" $ isTheorem writesCommute
      check "array aliasing counterexample checked with Haskell lookup" arrayAliasingRefuted
      check "datatype puzzle model re-evaluates to 42" puzzleChecked
      check "datatype first introduced during query" $ (== Sat) <$> lateDatatype
      check "sum of nonnegatives, by induction" $ void (runTP sumNonNeg) >> pure True
      check "non-generalized reversal proof fails" revWeakFails
      check "generalized accumulator reversal" $ void (runTP revAccCorrect) >> pure True
      check "reversal with empty initial accumulator" $ void (runTP reverseCorrect) >> pure True
      check "polymorphic reverseLength at Integer" $ void (runTP (reverseLength @Integer)) >> pure True
      check "polymorphic reverseLength at Word8" $ void (runTP (reverseLength @Word8)) >> pure True
      check "bookkeeping for an uninterpreted integer operation" $ void bookKeepingAbstract >> pure True
      check "bookkeeping specialized to integer sum" $ void (runTP bookKeepingSum) >> pure True
      check "bookkeeping needs the left-unit premise" bookKeepingNeedsLeftUnit
      check "closure environment preserves mapped list length" $ void (runTP shiftLength) >> pure True
      check "non-decreasing recursion is rejected" badRecursionRejected
      check "Kadane and specification against enumerated segments (3906 lists plus 3 cases)" kadaneConcrete
      check "Kadane correctness" $ void (runTP kadaneCorrect) >> pure True
      check "mirroring Expr preserves evaluation" $ void (runTP mirrorCorrect) >> pure True
      check "exercise 1: saturating subtraction" $ isTheorem satSubSpec
      check "exercise 2: largest below 100 is 94" $ (== 94) <$> largestBelow100
      check "exercise 3: revAcc length" $ void (runTP revAccLength) >> pure True
    _ -> fail "Usage: tutorial-examples [--tautology | --generate DIR | --diagnostics FILE]"

{- HLint ignore shiftEach "Avoid lambda" -}
