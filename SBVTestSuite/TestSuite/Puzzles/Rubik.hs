-----------------------------------------------------------------------------
-- |
-- Module    : TestSuite.Puzzles.Rubik
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Tests for the concrete geometry, symbolic lifting, and bounded shortest
-- and two-phase search.
-----------------------------------------------------------------------------

{-# OPTIONS_GHC -Wall -Werror #-}

module TestSuite.Puzzles.Rubik(tests) where

import Control.Exception (ErrorCall, try)
import Control.Monad     (forM_, replicateM)
import Data.List         (isInfixOf, sort, sortOn)
import qualified Data.List       as List (foldl')
import qualified Data.Map.Strict as Map
import qualified Data.Set        as Set

import Documentation.SBV.Examples.Puzzles.Rubik
import Utils.SBVTestFramework

tests :: TestTree
tests = testGroup "Puzzles.Rubik"
  [ testCase "permutations and identities" concrete
  , testCase "Kociemba fixtures" fixtures
  , testCase "canonical coverage through depth 3" canonicalCoverage
  , testCase "notation" notation
  , testCase "symbolic transitions, all 18 moves" symbolicTransitions
  , testCase "symbolic lifting identities" symbolicIdentities
  , testCase "solved and zero bound" zeroBounds
  , testCase "negative depth bound" invalidOptions
  , testCase "all one-move scrambles" singleMoves
  , testCase "shortest distances with and without pruning" shortest
  , testCase "phase-one target and projection" phaseOneTarget
  , testCase "two-phase solutions and bounds" twoPhaseSearch
  , testCase "bounded search with inactive suffix" boundedSearch
  ]

labels :: [Int]
labels = [0..53]

turnLabels :: [Move] -> [Int]
turnLabels = List.foldl' (\xs m -> permute (movePerm m) xs) labels

concrete :: Assertion
concrete = do
  forM_ allMoves $ \m -> do
    let p = permute (movePerm m) labels
    assert (sort p == labels)
    assert (all (\i -> p !! i == i) [4,13,22,31,40,49])
    assert (turnLabels [m, inverseMove m] == labels)
  forM_ [U,D,L,R,F,B] $ \f -> do
    assert (turnLabels (replicate 4 (Move f Clockwise)) == labels)
    assert (turnLabels (replicate 2 (Move f HalfTurn)) == labels)
  forM_ [(U,D),(L,R),(F,B)] $ \(f,g) ->
    forM_ [(t,u) | t <- [Clockwise,HalfTurn,Counterclockwise], u <- [Clockwise,HalfTurn,Counterclockwise]] $ \(t,u) ->
      assert (turnLabels [Move f t, Move g u] == turnLabels [Move g u, Move f t])
  let scramble = [Move R Clockwise, Move B HalfTurn, Move D Counterclockwise, Move L Clockwise, Move F HalfTurn]
  assert (isSolved (applyMoves (invertMoves scramble) (applyMoves scramble solvedCube)))
  assert (turnLabels (scramble ++ invertMoves scramble) == labels)

-- Independently published source-to-destination tables, transcribed from
-- https://kociemba.org/math/CubeDefs.htm (FaceletMove). Convert explicitly to
-- our destination-to-source convention. These expected values do not call
-- the geometry generator, and distinguish every sticker, including centers.
fixtures :: Assertion
fixtures = forM_ tables $ \(face, rows) -> do
  let names = [f : show i | f <- "URFDLB", i <- [1::Int ..9]]
      indexes = Map.fromList (zip names labels)
      destinations = map (indexes Map.!) (words (unwords rows))
      sources = map fst (sortOn snd (zip labels destinations))
  assert (sort destinations == labels)
  assert (turnLabels [Move face Clockwise] == sources)
  where tables =
          [ (U, [ "U3 U6 U9 U2 U5 U8 U1 U4 U7", "F1 F2 F3 R4 R5 R6 R7 R8 R9"
                , "L1 L2 L3 F4 F5 F6 F7 F8 F9", "D1 D2 D3 D4 D5 D6 D7 D8 D9"
                , "B1 B2 B3 L4 L5 L6 L7 L8 L9", "R1 R2 R3 B4 B5 B6 B7 B8 B9" ])
          , (R, [ "U1 U2 B7 U4 U5 B4 U7 U8 B1", "R3 R6 R9 R2 R5 R8 R1 R4 R7"
                , "F1 F2 U3 F4 F5 U6 F7 F8 U9", "D1 D2 F3 D4 D5 F6 D7 D8 F9"
                , "L1 L2 L3 L4 L5 L6 L7 L8 L9", "D9 B2 B3 D6 B5 B6 D3 B8 B9" ])
          , (F, [ "U1 U2 U3 U4 U5 U6 R1 R4 R7", "D3 R2 R3 D2 R5 R6 D1 R8 R9"
                , "F3 F6 F9 F2 F5 F8 F1 F4 F7", "L3 L6 L9 D4 D5 D6 D7 D8 D9"
                , "L1 L2 U9 L4 L5 U8 L7 L8 U7", "B1 B2 B3 B4 B5 B6 B7 B8 B9" ])
          , (D, [ "U1 U2 U3 U4 U5 U6 U7 U8 U9", "R1 R2 R3 R4 R5 R6 B7 B8 B9"
                , "F1 F2 F3 F4 F5 F6 R7 R8 R9", "D3 D6 D9 D2 D5 D8 D1 D4 D7"
                , "L1 L2 L3 L4 L5 L6 F7 F8 F9", "B1 B2 B3 B4 B5 B6 L7 L8 L9" ])
          , (L, [ "F1 U2 U3 F4 U5 U6 F7 U8 U9", "R1 R2 R3 R4 R5 R6 R7 R8 R9"
                , "D1 F2 F3 D4 F5 F6 D7 F8 F9", "B9 D2 D3 B6 D5 D6 B3 D8 D9"
                , "L3 L6 L9 L2 L5 L8 L1 L4 L7", "B1 B2 U7 B4 B5 U4 B7 B8 U1" ])
          , (B, [ "L7 L4 L1 U4 U5 U6 U7 U8 U9", "R1 R2 U1 R4 R5 U2 R7 R8 U3"
                , "F1 F2 F3 F4 F5 F6 F7 F8 F9", "D1 D2 D3 D4 D5 D6 R9 R6 R3"
                , "D7 L2 L3 D8 L5 L6 D9 L8 L9", "B3 B6 B9 B2 B5 B8 B1 B4 B7" ])
          ]

canonicalCoverage :: Assertion
canonicalCoverage = forM_ [0..3] $ \n -> do
  let sequences = concatMap (`replicateM` allMoves) [0..n]
      canonical ms = and [f /= g && (f,g) `notElem` [(D,U),(R,L),(B,F)]
                         | (Move f _, Move g _) <- zip ms (drop 1 ms)]
      reachable = Set.fromList . map turnLabels
  assert (reachable sequences == reachable (filter canonical sequences))
  -- Also tie the concrete reference predicate to the symbolic pruning rule.
  forM_ [(a,b) | a <- allMoves, b <- allMoves] $ \(a,b) ->
    assert (unliteral (canonicalPair (symbolicMove a) (symbolicMove b)) == Just (canonical [a,b]))

notation :: Assertion
notation = do
  assert (parseMoves (renderMoves allMoves) == Right allMoves)
  assert (parseMoves " \t\n " == Right [])
  assert (parseMoves " R\t U2\nF' " == Right [Move R Clockwise, Move U HalfTurn, Move F Counterclockwise])
  forM_ [("r", "wide"), ("M2", "slice"), ("E", "slice"), ("S'", "slice")
        ,("x", "rotation"), ("y2", "rotation"), ("z'", "rotation"), ("Rw", "wide"), ("Fw2", "wide")
        ,("R2'", "use R2"), ("R,U", "whitespace"), ("R;U", "whitespace")
        ,("Q", "expected"), ("R3", "expected"), ("R''", "expected"), ("W", "expected"), ("white", "expected")] $ \(token, hint) ->
    case parseMoves ("U " ++ token) of
      Left err -> assert (all (`isInfixOf` err) ["Token 2", show token, hint])
      Right ms -> assertFailure ("Unexpected parse: " ++ show ms)
  assert (renderMoves [] == "")
  -- A solved net is a deterministic formatting fixture; no solver model golden.
  assert (renderCube solvedCube == unlines
    ["       U", "       w w w", "       w w w", "       w w w", "L      F      R      B"
    ,"o o o  g g g  r r r  b b b", "o o o  g g g  r r r  b b b", "o o o  g g g  r r r  b b b"
    ,"       D", "       y y y", "       y y y", "       y y y"
    ,"w=white r=red g=green y=yellow o=orange b=blue"])

symbolicMove :: Move -> SMove
symbolicMove (Move f t) = SMove (literal f) (literal t)

symbolicTransitions :: Assertion
symbolicTransitions = assertIsThm $ do
  cs <- mapM (free . ("color_" ++) . show) [0::Int ..53]
  f <- free "face"
  t <- free "turn"
  let m = SMove f t
  -- Arbitrary symbolic colors make this stronger than fixing a sample cube.
  pure $ sAnd [(f .== literal face .&& t .== literal turn)
               .=> (step m cs .== permute (movePerm move) cs)
              | move@(Move face turn) <- allMoves]

symbolicIdentities :: Assertion
symbolicIdentities = assertIsThm $ do
  cs <- mapM (free . ("color_" ++) . show) [0::Int ..53]
  -- These can simplify before reaching the solver: they check the lifting.
  pure $ sAnd [step (symbolicMove (inverseMove m)) (step (symbolicMove m) cs) .== cs | m <- allMoves]

zeroBounds :: Assertion
zeroBounds = do
  solved <- solveScramble (defaultOptions 0) []
  assert (solved == Solved [])
  unsolved <- solveScramble (defaultOptions 0) [Move F Clockwise]
  assert (unsolved == NoSolutionWithin 0)

invalidOptions :: Assertion
invalidOptions = do
  result <- try (solveScramble (defaultOptions (-1)) []) :: IO (Either ErrorCall SolveResult)
  case result of
    Left _  -> pure ()
    Right r -> assertFailure ("Accepted invalid options: " ++ show r)

singleMoves :: Assertion
singleMoves = forM_ allMoves $ \m -> do
  result <- solveScramble (defaultOptions 1) [m]
  assert (result == Solved [inverseMove m])

-- Independent, unpruned breadth-first search on concrete color states. Its
-- expected distances come from visited layers, never from scramble lengths.
bfs :: Int -> Map.Map Cube Int
bfs limit = go 0 (Set.singleton solvedCube) (Map.singleton solvedCube 0)
  where go depth frontier seen
          | depth == limit = seen
          | True =
              let next = Set.fromList [applyMove m c | c <- Set.toList frontier, m <- allMoves]
                           `Set.difference` Map.keysSet seen
                  seen' = Map.union seen (Map.fromSet (const (depth+1)) next)
              in go (depth+1) next seen'

shortest :: Assertion
shortest = do
  let distances = bfs 3
      scrambles = [[], [Move R Clockwise, Move R Counterclockwise]
                  ,[Move R Clockwise, Move R Clockwise]
                  ,[Move R Clockwise, Move L Clockwise, Move R Clockwise]
                  ,[Move U Clockwise, Move F HalfTurn]
                  ,[Move R Clockwise, Move U Clockwise, Move F HalfTurn]]
  forM_ scrambles $ \scramble -> do
    let initial = applyMoves scramble solvedCube
        distance = distances Map.! initial
    forM_ [False,True] $ \pruning -> do
      let opts = (defaultOptions distance) {usePruning = pruning}
      result <- solveWith z3 opts initial
      case result of
        Solved ms -> assert (length ms == distance && isSolved (applyMoves ms initial))
        other     -> assertFailure (show other)
      if distance == 0 then pure () else do
        below <- solveWith z3 opts {maxDepth = distance-1} initial
        assert (below == NoSolutionWithin (distance-1))

-- The reference uses Kociemba's corner/edge facelet groups, checking the
-- orientations and slice membership separately on full colors. In particular,
-- orienting just the corners or just the U/D edges is insufficient.
phaseOneTarget :: Assertion
phaseOneTarget = do
  let corners :: [(Int, Int, Int)]
      corners = [(8,9,20), (6,18,38), (0,36,47), (2,45,11)
                ,(29,26,15), (27,44,24), (33,53,42), (35,17,51)]
      edges = [(5,10), (7,19), (3,37), (1,46), (32,16), (28,25)
              ,(30,43), (34,52), (23,12), (21,41), (50,39), (48,14)]
      ud c = c `elem` [White,Yellow]
      fb c = c `elem` [Green,Blue]
      reference (Cube cs) = all (\(i,_,_) -> ud (cs !! i)) corners
                        && all (\(i,j) -> ud (cs !! i) || (fb (cs !! i) && not (ud (cs !! j)))) edges
                        && not (any (\(i,j) -> ud (cs !! i) || ud (cs !! j)) (drop 8 edges))
      ready = unliteral . phaseOneGoal . map literal . cubeColors . phaseOneCube
      states = solvedCube : map (`applyMove` solvedCube) allMoves
  forM_ states $ \cube -> do
    assert (ready cube == Just (reference cube))
    forM_ allMoves $ \m ->
      assert (phaseOneCube (applyMove m cube) == applyMove m (phaseOneCube cube))
  -- Check every restricted move preserves the target, including on a state
  -- with the correct orientations but permuted pieces.
  let permuted = applyMoves [Move U Clockwise, Move F HalfTurn, Move D Counterclockwise] solvedCube
  forM_ [solvedCube, permuted] $ \cube ->
    forM_ phaseTwoMoves $ \m -> assert (ready (applyMove m cube) == Just True)
  assert (ready (applyMove (Move R Clockwise) solvedCube) == Just False)
  assert (ready (applyMove (Move F Clockwise) solvedCube) == Just False)

twoPhaseSearch :: Assertion
twoPhaseSearch = do
  -- One tiny scramble exercises both phases. Hard cubes are manual examples,
  -- not regression tests; keep these bounds at one and two moves.
  let initial = applyMoves [Move U Clockwise, Move R Clockwise] solvedCube
  result <- solveTwoPhase (defaultOptions 1) (defaultOptions 2) initial
  case result of
    TwoPhaseSolved first second -> do
      assert (length first <= 1 && length second <= 2)
      assert (all (`elem` phaseTwoMoves) second)
      assert (unliteral (phaseOneGoal (map literal (cubeColors (phaseOneCube (applyMoves first initial))))) == Just True)
      assert (isSolved (applyMoves (first ++ second) initial))
    other -> assertFailure (show other)
  solved <- solveTwoPhaseWith z3 (defaultOptions 0) (defaultOptions 0) solvedCube
  assert (solved == TwoPhaseSolved [] [])
  firstFailed <- solveTwoPhaseWith z3 (defaultOptions 0) (defaultOptions 2) (applyMove (Move R Clockwise) solvedCube)
  assert (firstFailed == PhaseOneExhausted 0)
  secondFailed <- solveTwoPhaseWith z3 (defaultOptions 0) (defaultOptions 0) (applyMove (Move U Clockwise) solvedCube)
  assert (secondFailed == PhaseTwoExhausted [] 0)
  forM_ [(-1,0), (0,-1)] $ \(a,b) -> do
    invalid <- try (solveTwoPhaseWith z3 (defaultOptions a) (defaultOptions b) solvedCube) :: IO (Either ErrorCall TwoPhaseResult)
    case invalid of
      Left _  -> pure ()
      Right r -> assertFailure ("Accepted invalid phase bounds: " ++ show r)

-- A one-move solution must fit a larger bound even when canonical pruning
-- prevents extending the active sequence with the only permitted move.
boundedSearch :: Assertion
boundedSearch = do
  let goal cs = cs .== map literal (cubeColors solvedCube)
      move = Move R Clockwise
      initial = applyMove (inverseMove move) solvedCube
  result <- solveWithinWith z3 (defaultOptions 3) [move] goal initial
  assert (result == Solved [move])
  impossible <- solveWithinWith z3 (defaultOptions 3) [] goal initial
  assert (impossible == NoSolutionWithin 3)

