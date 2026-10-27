-----------------------------------------------------------------------------
-- |
-- Module    : Documentation.SBV.Examples.Puzzles.Rubik
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Bounded shortest and two-phase solutions for a 3x3 Rubik's Cube. The face-turn metric
-- counts each quarter-turn, inverse quarter-turn, and half-turn as one move.
-- Centers stay fixed; slice moves, wide turns, and whole-cube rotations are
-- unsupported. Inputs can be scrambles of the solved cube or facelets
-- transcribed from a physical cube; see 'physicalCube'.
-- Inputs are assumed legal; transcription errors are not diagnosed and may
-- instead exhaust a search bound.
--
-- Facelets use Kociemba's order U1..U9, R1..R9, F1..F9, D1..D9, L1..L9,
-- B1..B9, with this net (each face is viewed from outside):
--
-- @
--             U1 U2 U3
--             U4 U5 U6
--             U7 U8 U9
--   L1 L2 L3  F1 F2 F3  R1 R2 R3  B1 B2 B3
--   L4 L5 L6  F4 F5 F6  R4 R5 R6  B4 B5 B6
--   L7 L8 L9  F7 F8 F9  R7 R8 R9  B7 B8 B9
--             D1 D2 D3
--             D4 D5 D6
--             D7 D8 D9
-- @
--
-- The coordinates are right-handed: +x = R, +y = U, +z = F. Clockwise,
-- looking at a face, means -90 degrees about its outward normal, including
-- the negative-axis faces D, L, and B. See
-- <https://kociemba.org/math/faceletlevel.htm> for the facelet convention.
--
-- With fixed centers, every cubie has a unique set of colors, so colors
-- determine a legal cube's state. We ignore invisible center-piece rotations.
-- 'isSolved' therefore compares colors with the original solved coloring.
--
-- A successful 'solveWith' result is shortest: every smaller positive depth was
-- unsatisfiable, and depth zero was checked concretely. The depth bound is
-- only a limit; the search stops as soon as it finds a solution. A bound
-- failure says nothing about greater depths.
-- 'solveTwoPhaseWith' instead supplies an intermediate target and restricted
-- moves for the second phase, accepting a solution without proving optimality.
-----------------------------------------------------------------------------

{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TemplateHaskell   #-}
{-# LANGUAGE TypeApplications  #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module Documentation.SBV.Examples.Puzzles.Rubik where

import Control.Monad (foldM, when)
import Data.List     (elemIndex, intercalate, sortOn)

import qualified Data.List as List (foldl')

import Data.SBV
import Data.SBV.Control

-- | The six faces of the cube. This enumeration is separate from facelet
-- storage order, which follows U R F D L B.
data Face = U | D | L | R | F | B
          deriving (Eq, Ord, Show, Enum, Bounded)

-- | The three nonidentity turns of a face: clockwise and counterclockwise
-- quarter-turns rotate by 90 degrees; a half-turn rotates by 180 degrees.
data Turn = Clockwise | HalfTurn | Counterclockwise
          deriving (Eq, Ord, Show, Enum, Bounded)

-- | One move in the face-turn metric.
data Move = Move Face Turn
          deriving (Eq, Ord, Show)

-- | Solved colors: U white, R red, F green, D yellow, L orange, B blue.
data Color = White | Red | Green | Yellow | Orange | Blue
           deriving (Eq, Ord, Show)

-- | Symbolic faces, turns, and colors are SMT enumerations with named values.
mkSymbolic [''Face, ''Turn, ''Color]

-- | A cube represented by 54 facelet colors in U R F D L B order.
-- Start with 'solvedCube' and use 'applyMove' or 'applyMoves' to obtain
-- reachable positions.
newtype Cube = Cube [Color]
             deriving (Eq, Ord, Show)

-- | Facelets in U R F D L B order.
cubeColors :: Cube -> [Color]
cubeColors (Cube cs) = cs

-- | Original solved coloring.
solvedCube :: Cube
solvedCube = Cube (concatMap (replicate 9) [White, Red, Green, Yellow, Orange, Blue])

-- | A scrambled physical cube, transcribed face by face. Hold it with the
-- white center on top and the green center facing you when applying moves.
-- The six grids below follow the U R F D L B storage order.
-- See 'solveTwoPhase' for the manual search example and 'physicalSolution'
-- for a recorded solution. Shortest-path search with 'solveWith' is impractical
-- for this scramble.
--
-- >>> putStr (renderCube physicalCube)
--        U
--        b g w
--        r w g
--        b y g
-- L      F      R      B
-- y w o  w b y  r w o  g r r
-- y o b  r g w  o r r  y b g
-- r y y  b b o  g w w  r g b
--        D
--        o o y
--        o y b
--        w o g
-- w=white r=red g=green y=yellow o=orange b=blue
physicalCube :: Cube
physicalCube = Cube $ concat
  [ -- UP
    [ Blue,   Green,  White
    , Red,    White,  Green
    , Blue,   Yellow, Green
    ]
  , -- RIGHT
    [ Red,    White,  Orange
    , Orange, Red,    Red
    , Green,  White,  White
    ]
  , -- FRONT
    [ White,  Blue,   Yellow
    , Red,    Green,  White
    , Blue,   Blue,   Orange
    ]
  , -- DOWN
    [ Orange, Orange, Yellow
    , Orange, Yellow, Blue
    , White,  Orange, Green
    ]
  , -- LEFT
    [ Yellow, White,  Orange
    , Yellow, Orange, Blue
    , Red,    Yellow, Yellow
    ]
  , -- BACK
    [ Green,  Red,    Red
    , Yellow, Blue,   Green
    , Red,    Green,  Blue
    ]
  ]

-- | A solution for 'physicalCube', found by a manual two-phase Z3 run.
-- The first line has the twelve phase-one moves; the second has the eighteen
-- phase-two moves. Hold the cube with white up and green front throughout.
-- This is not claimed to be shortest. The doctest only replays the recorded
-- moves, so it does not repeat the expensive search.
--
-- >>> isSolved (applyMoves physicalSolution physicalCube)
-- True
physicalSolution :: [Move]
physicalSolution = either error id $ parseMoves $ unwords
  [ "L2 F L U F R' B R2 D2 R F2 R'"
  , "F2 B2 U2 F2 R2 U B2 D' F2 D' R2 D2 B2 U2 L2 B2 D2 L2"
  ]

-- | Compare the facelets with the fixed solved coloring.
--
-- >>> isSolved solvedCube
-- True
-- >>> isSolved (applyMove (Move R Clockwise) solvedCube)
-- False
isSolved :: Cube -> Bool
isSolved = (== solvedCube)

-- | A destination-to-source permutation: new[i] = old[p[i]].
newtype Perm = Perm [Int]

-- | Apply a permutation to exactly 54 values, including distinct test labels.
--
-- >>> take 3 (permute (Perm [53,52..0]) [0..53 :: Int])
-- [53,52,51]
permute :: Perm -> [a] -> [a]
permute (Perm p) xs
  | length xs == 54 = map (xs !!) p
  | True            = error "Rubik.permute: expected exactly 54 facelets"

-- | Integer vector @(x, y, z)@ for facelet positions and directions.
-- Positive axes point right, up, and front, respectively.
type Vec = (Int, Int, Int)

-- | Add two vectors componentwise.
add :: Vec -> Vec -> Vec
add (a, b, c) (x, y, z) = (a+x, b+y, c+z)

-- | Multiply each component of a vector by an integer.
scale :: Int -> Vec -> Vec
scale k (x, y, z) = (k*x, k*y, k*z)

-- | Dot product, used to select the layer belonging to a face.
dot :: Vec -> Vec -> Int
dot (a, b, c) (x, y, z) = a*x + b*y + c*z

-- | Cross product in the right-handed cube coordinate system.
cross :: Vec -> Vec -> Vec
cross (a, b, c) (x, y, z) = (b*z-c*y, c*x-a*z, a*y-b*x)

-- | Outward normal, screen-right, and screen-up unit vectors, viewed from
-- outside the face. These orient each face's grid in the documented net.
--
-- >>> basis B
-- ((0,0,-1),(-1,0,0),(0,1,0))
basis :: Face -> (Vec, Vec, Vec)
basis U = (( 0, 1, 0), ( 1, 0, 0), ( 0, 0,-1))
basis D = (( 0,-1, 0), ( 1, 0, 0), ( 0, 0, 1))
basis L = ((-1, 0, 0), ( 0, 0, 1), ( 0, 1, 0))
basis R = (( 1, 0, 0), ( 0, 0,-1), ( 0, 1, 0))
basis F = (( 0, 0, 1), ( 1, 0, 0), ( 0, 1, 0))
basis B = (( 0, 0,-1), (-1, 0, 0), ( 0, 1, 0))

-- | Positions and outward normals of the 54 facelets, in U R F D L B order.
-- Position and normal together distinguish stickers on the same cubie.
--
-- NB. Keep the explicit U R F D L B storage order: [minBound .. maxBound] follows
-- the different Face constructor order U D L R F B. Solved colors, rendering,
-- and the reference fixtures all depend on this storage order.
--
-- For example, U9 and R1 share a corner but face in different directions:
--
-- >>> facelets !! 8
-- ((1,1,1),(0,1,0))
-- >>> facelets !! 9
-- ((1,1,1),(1,0,0))
facelets :: [(Vec, Vec)]
facelets = [(n `add` scale (c-1) r `add` scale (1-row) u, n) | f <- [U, R, F, D, L, B], let (n, r, u) = basis f, row <- [0..2], c <- [0..2]]

-- | Generate a clockwise quarter-turn from integer geometry, rotating both
-- sticker positions and normals in the selected layer. The face's own grid
-- rotates clockwise; these are the source indexes for F1 through F9:
--
-- >>> take 9 (drop 18 (permute (quarterTurn F) [0..53 :: Int]))
-- [24,21,18,25,22,19,26,23,20]
quarterTurn :: Face -> Perm
quarterTurn f = Perm (map snd (sortOn fst destinations))
  where (axis, _, _) = basis f

        -- Rodrigues' formula for -90 degrees about a unit coordinate axis.
        rotateVector v = scale (dot axis v) axis `add` cross v axis
        turn (p,n) | dot axis p == 1 = (rotateVector p, rotateVector n)
                   | True            = (p,n)

        destination sticker = case elemIndex (turn sticker) facelets of
                                Just i  -> i
                                Nothing -> error "Rubik.quarterTurn: invalid geometry"

        destinations = [(destination sticker, i) | (i, sticker) <- zip [0..] facelets]

-- | All eighteen moves, enumerating each face and its three turns.
--
-- >>> renderMoves allMoves
-- "U U2 U' D D2 D' L L2 L' R R2 R' F F2 F' B B2 B'"
allMoves :: [Move]
allMoves = [Move f t | f <- [minBound .. maxBound], t <- [minBound .. maxBound]]

-- | Shared permutations for all eighteen moves. Half-turns and inverse
-- quarter-turns are obtained by composing the generated quarter-turns.
moveTables :: [(Move, Perm)]
moveTables = [(m, Perm (iterate (permute (quarterTurn f)) [0..53] !! count t)) | m@(Move f t) <- allMoves]
  where count Clockwise        = 1
        count HalfTurn         = 2
        count Counterclockwise = 3

-- | Permutation for a move, derived from integer geometry.
-- A U half-turn reverses the order of the nine stickers on that face:
--
-- >>> take 9 (permute (movePerm (Move U HalfTurn)) [0..53 :: Int])
-- [8,7,6,5,4,3,2,1,0]
movePerm :: Move -> Perm
movePerm m = case lookup m moveTables of
               Just p  -> p
               Nothing -> error "Rubik.movePerm: missing move"

-- | Turn one face.
--
-- A right quarter-turn brings green stickers to the right column of U:
--
-- >>> take 9 (cubeColors (applyMove (Move R Clockwise) solvedCube))
-- [White,White,Green,White,White,Green,White,White,Green]
applyMove :: Move -> Cube -> Cube
applyMove m (Cube cs) = Cube (permute (movePerm m) cs)

-- | Apply moves from left to right.
--
-- >>> let scramble = [Move R Clockwise, Move U HalfTurn]
-- >>> isSolved (applyMoves (scramble ++ invertMoves scramble) solvedCube)
-- True
applyMoves :: [Move] -> Cube -> Cube
applyMoves ms c = List.foldl' (flip applyMove) c ms

-- | Undo one move.
--
-- A half-turn is its own inverse:
--
-- >>> inverseMove (Move R HalfTurn)
-- Move R HalfTurn
inverseMove :: Move -> Move
inverseMove (Move f t) = Move f $ case t of
                                    Clockwise        -> Counterclockwise
                                    HalfTurn         -> HalfTurn
                                    Counterclockwise -> Clockwise

-- | Undo a sequence, reversing its order as well as its turns.
--
-- >>> renderMoves (invertMoves [Move R Clockwise, Move U HalfTurn])
-- "U2 R'"
invertMoves :: [Move] -> [Move]
invertMoves = reverse . map inverseMove

-- | A symbolic cube uses ordinary lists: all facelet indexes are static;
-- only the choice of move is symbolic.
type SCube = [SColor]

-- | A symbolic move chooses a face and a turn directly. Their datatypes
-- admit only valid choices, so no numeric codes or domain constraints are needed.
data SMove = SMove { moveFace :: SFace -- ^ Face to turn.
                   , moveTurn :: STurn -- ^ Direction and amount of rotation.
                   }

-- | Adjacent equal faces combine or cancel. Opposite faces commute, so keep
-- U before D, L before R, and F before B. These rules preserve a shortest
-- solution and also exclude R L R, which reduces to R2 L and then L R2.
--
-- Opposite faces L and R are allowed only in that order:
--
-- >>> import Data.SBV (unliteral)
-- >>> unliteral (canonicalPair (SMove sL sClockwise) (SMove sR sClockwise))
-- Just True
-- >>> unliteral (canonicalPair (SMove sR sClockwise) (SMove sL sClockwise))
-- Just False
canonicalPair :: SMove -> SMove -> SBool
canonicalPair (SMove f _) (SMove g _) = f ./= g .&& sNot (sOr reversedOpposites)
  where reversedOpposites = [f .== literal a .&& g .== literal b | (a,b) <- [(D,U), (R,L), (B,F)]]

-- | Lift the concrete permutations by selecting the named face and turn.
--
-- With concrete choices, the symbolic expressions evaluate to colors.
-- Here we select R clockwise:
--
-- >>> import Data.SBV (literal, unliteral)
-- >>> let initial = map literal (cubeColors solvedCube)
-- >>> map unliteral (take 9 (step (SMove sR sClockwise) initial))
-- [Just White,Just White,Just Green,Just White,Just White,Just Green,Just White,Just White,Just Green]
step :: SMove -> SCube -> SCube
step (SMove f t) cs = choose f [(face, choose t [(turn, permute (movePerm (Move face turn)) cs)
                                              | turn <- [minBound .. maxBound]])
                             | face <- [minBound .. maxBound]]
  where choose :: SymVal a => SBV a -> [(a, SCube)] -> SCube
        choose _ []          = error "Rubik.step: empty choice"
        choose v ((_, x):xs) = foldr (\(value, ys) zs -> zipWith (ite (v .== literal value)) ys zs) x xs

-- | Depth bound, progress reporting, and canonical pruning.
-- Disable pruning to compare searches in small tests.
data SearchOptions = SearchOptions
  { maxDepth     :: Int  -- ^ Maximum solution length in the face-turn metric.
  , showProgress :: Bool -- ^ Print the depth before each satisfiability check.
  , usePruning   :: Bool -- ^ Restrict adjacent moves using 'canonicalPair'.
  } deriving Show

-- | Quiet search with pruning.
defaultOptions :: Int -> SearchOptions
defaultOptions n = SearchOptions n False True

-- | A solution, or exhaustion of the supplied depth bound. 'solveWith'
-- guarantees a shortest solution; 'solveWithinWith' accepts any solution.
data SolveResult = Solved [Move] | NoSolutionWithin Int deriving (Eq, Show)

-- | Solve a legal cube with the chosen solver.
-- A negative depth bound raises an error.
--
-- Each iteration extends the previous state by one symbolic move, then pushes
-- a temporary goal asserting the solved coloring. On unsat we pop only that
-- goal and extend again. Move declarations and pruning constraints stay
-- outside the temporary context. On sat we extract the moves; any other solver result
-- is an error, as in the other puzzle examples.
--
-- >>> import Data.SBV (z3)
-- >>> solveWith z3 (defaultOptions 1) (applyMove (Move F HalfTurn) solvedCube)
-- Solved [Move F HalfTurn]
solveWith :: SMTConfig -> SearchOptions -> Cube -> IO SolveResult
solveWith cfg opts initial
  | maxDepth opts < 0  = error "Rubik.solveWith: negative depth bound"
  | isSolved initial   = pure (Solved [])
  | maxDepth opts == 0 = pure (NoSolutionWithin 0)
  | True               = runSMTWith cfg $ query $ extend 1 [] (map literal (cubeColors initial))
  where extend depth previous cs = do
          f <- freshVar ("face_" ++ show depth)
          t <- freshVar ("turn_" ++ show depth)
          let m = SMove f t
              moves = m : previous  -- Most recent move first; reverse only for extraction.
              next = step m cs
          when (usePruning opts) $ case previous of
                                    p:_ -> constrain (canonicalPair p m)
                                    []  -> pure ()
          when (showProgress opts) $ io $ putStrLn $ "Checking depth " ++ show depth
          push 1
          constrain (sAnd (zipWith (.==) next (map literal (cubeColors solvedCube))))
          status <- checkSat
          case status of
            Unsat | depth == maxDepth opts -> pure (NoSolutionWithin depth)
                  | True                   -> pop 1 >> extend (depth+1) moves next
            Sat   -> Solved <$> mapM extract (reverse moves)
            other -> error $ "Rubik.solveWith: unexpected solver result: " ++ show other
        extract (SMove mf mt) = Move <$> getValue mf <*> getValue mt

-- | Solve a scramble using Z3.
--
-- >>> solveScramble (defaultOptions 0) []
-- Solved []
-- >>> solveScramble (defaultOptions 1) [Move R Clockwise]
-- Solved [Move R Counterclockwise]
-- >>> solveScramble (defaultOptions 1) [Move R Clockwise, Move U Clockwise]
-- NoSolutionWithin 1
-- >>> solveScramble (defaultOptions 2) [Move R Clockwise, Move U Clockwise]
-- Solved [Move U Counterclockwise,Move R Counterclockwise]
solveScramble :: SearchOptions -> [Move] -> IO SolveResult
solveScramble opts ms = solveWith z3 opts (applyMoves ms solvedCube)

-- | Forget which of two opposite colors a sticker has. The three remaining
-- colors identify the U/D, F/B, and L/R axes. Phase one needs only these
-- classes; replaying its moves on the original cube restores full information.
--
-- >>> take 9 (cubeColors (phaseOneCube solvedCube))
-- [White,White,White,White,White,White,White,White,White]
-- >>> phaseOneCube (applyMove (Move U HalfTurn) solvedCube) == phaseOneCube solvedCube
-- True
phaseOneCube :: Cube -> Cube
phaseOneCube = Cube . map axisColor . cubeColors
  where axisColor Yellow = White
        axisColor Orange = Red
        axisColor Blue   = Green
        axisColor c      = c

-- | Phase-one target on a cube projected by 'phaseOneCube'. All U/D stickers
-- must have the U/D color class. This orients the corners and the eight U/D
-- edges and excludes middle-layer edges from those layers. The four remaining
-- edges must present their F/B stickers toward F/B, orienting them as well.
-- Centers are omitted because moves never change them.
--
-- These are precisely the conditions for the subgroup generated by
-- 'phaseTwoMoves'; see <https://kociemba.org/math/twophase.htm>.
--
-- >>> import Data.SBV (literal, unliteral)
-- >>> let ready = unliteral . phaseOneGoal . map literal . cubeColors . phaseOneCube
-- >>> ready solvedCube
-- Just True
-- >>> ready (applyMove (Move R Clockwise) solvedCube)
-- Just False
-- >>> ready (applyMove (Move R HalfTurn) solvedCube)
-- Just True
--
-- The recorded physical solution reaches this target after twelve moves:
--
-- >>> ready (applyMoves (take 12 physicalSolution) physicalCube)
-- Just True
phaseOneGoal :: SCube -> SBool
phaseOneGoal cs = sAnd ([cs !! i .== sWhite | i <- [0,1,2,3,5,6,7,8,27,28,29,30,32,33,34,35]]
                   ++ [cs !! i .== sGreen | i <- [21,23,48,50]])

-- | Moves preserving the phase-one target: arbitrary U/D turns and half-turns
-- of the four side faces. Together they can solve every legal phase-one state.
--
-- >>> renderMoves phaseTwoMoves
-- "U U2 U' D D2 D' L2 R2 F2 B2"
phaseTwoMoves :: [Move]
phaseTwoMoves = [m | m@(Move f t) <- allMoves, f `elem` [U,D] || t == HalfTurn]

-- | Find any sequence within the bound using the supplied moves and target.
-- One query allows up to the bound's number of moves, followed by inactive
-- slots that leave the cube unchanged. Active slots form a prefix; extracting
-- only those slots gives the solution without proving shorter lengths
-- impossible. Pruning applies only between active moves.
-- A negative bound is an error; non-sat/unsat solver results also raise errors.
--
-- >>> import Data.SBV (z3)
-- >>> solveWithinWith z3 (defaultOptions 1) phaseTwoMoves phaseOneGoal (phaseOneCube solvedCube)
-- Solved []
solveWithinWith :: SMTConfig -> SearchOptions -> [Move] -> (SCube -> SBool) -> Cube -> IO SolveResult
solveWithinWith cfg opts allowed goal initial
  | maxDepth opts < 0                   = error "Rubik.solveWithinWith: negative depth bound"
  | unliteral (goal start) == Just True = pure (Solved [])
  | maxDepth opts == 0                  = pure (NoSolutionWithin 0)
  | True                                = runSMTWith cfg $ do
      (revMoves, final) <- foldM extend ([], start) [1 .. maxDepth opts]
      let moves = reverse revMoves
      constrain (goal final)
      query $ do
        when (showProgress opts) $ io $ putStrLn $ "Checking up to " ++ show (maxDepth opts) ++ " moves"
        status <- checkSat
        case status of
          Unsat -> pure (NoSolutionWithin (maxDepth opts))
          Sat   -> do active <- mapM (getValue . fst) moves
                      let n = length (takeWhile id active)
                      Solved <$> mapM (extract . snd) (take n moves)
          other -> error $ "Rubik.solveWithinWith: unexpected solver result: " ++ show other
  where start = map literal (cubeColors initial)
        extend (previous, cs) depth = do
          f <- free ("face_" ++ show depth)
          t <- free ("turn_" ++ show depth)
          active <- free ("active_" ++ show depth)
          let m = SMove f t
          constrain (active .=> sOr [f .== literal face .&& t .== literal turn | Move face turn <- allowed])
          case previous of
            (wasActive, p):_ -> do
              constrain (active .=> wasActive)
              when (usePruning opts) $ constrain (active .=> canonicalPair p m)
            [] -> pure ()
          pure ((active, m) : previous, zipWith (ite active) (step m cs) cs)
        extract (SMove f t) = Move <$> getValue f <*> getValue t

-- | Two sequences forming a solution, or the phase whose bound was exhausted.
-- A phase-two failure retains the phase-one sequence so that the intermediate
-- cube can be retried with a larger bound. It does not rule out solutions
-- through other intermediate cubes, nor solutions within the combined bounds.
data TwoPhaseResult = TwoPhaseSolved [Move] [Move]
                    | PhaseOneExhausted Int
                    | PhaseTwoExhausted [Move] Int
                    deriving (Eq, Show)

-- | Let Z3 choose every move, using a human-supplied intermediate target.
-- First orient all pieces and put middle-layer edges in the middle layer;
-- then solve using 'phaseTwoMoves'. The first phase's result is applied to the
-- full-color input before starting the second phase. No shortest-path claim
-- is made, either for the individual phases or their concatenation.
--
-- The example crosses both phases. Check the resulting cube rather than a
-- particular sequence, since Z3 may choose different valid solutions.
--
-- >>> import Data.SBV (z3)
-- >>> let cube = applyMoves [Move U Clockwise, Move R Clockwise] solvedCube
-- >>> TwoPhaseSolved first second <- solveTwoPhaseWith z3 (defaultOptions 1) (defaultOptions 2) cube
-- >>> isSolved (applyMoves (first ++ second) cube)
-- True
solveTwoPhaseWith :: SMTConfig -> SearchOptions -> SearchOptions -> Cube -> IO TwoPhaseResult
solveTwoPhaseWith cfg firstOpts secondOpts initial
  | maxDepth firstOpts < 0 || maxDepth secondOpts < 0 = error "Rubik.solveTwoPhaseWith: negative depth bound"
  | True                                              = do
      when (showProgress firstOpts) $ putStrLn "Phase 1: orientations and middle-layer edges"
      first <- solveWithinWith cfg firstOpts allMoves phaseOneGoal (phaseOneCube initial)
      case first of
        NoSolutionWithin n -> pure (PhaseOneExhausted n)
        Solved ms -> do
          when (showProgress firstOpts) $ putStrLn $ "Phase 1: " ++ renderMoves ms
          when (showProgress secondOpts) $ putStrLn "Phase 2: solve with U/D turns and side half-turns"
          let middle = applyMoves ms initial
              goal cs = sAnd (zipWith (.==) cs (map literal (cubeColors solvedCube)))
          second <- solveWithinWith cfg secondOpts phaseTwoMoves goal middle
          pure $ case second of
                   NoSolutionWithin n -> PhaseTwoExhausted ms n
                   Solved ns          -> TwoPhaseSolved ms ns

-- | Two-phase search using Z3's SAT engine. The tactic simplifies the formula,
-- eliminates conditionals over colors, and translates finite enumerations to
-- bit-vectors before bit-blasting. Haskell still uses named faces, turns, and
-- colors; this is only a choice of Z3's solving machinery, not a source of
-- cube-solving move sequences.
--
-- To run a fresh search for 'physicalCube', with separate bounds for the two
-- phases and progress reporting:
--
-- @
-- solveTwoPhase
--   (defaultOptions 12) {showProgress = True}
--   (defaultOptions 18) {showProgress = True}
--   physicalCube
-- @
--
-- Success returns @TwoPhaseSolved first second@; apply @first ++ second@ to
-- solve the input cube. Use 'solveTwoPhaseWith' to supply a solver configuration.
-- 'physicalSolution' holds a recorded solution from a previous run.
-- The physical-cube search can take minutes, so the call above is a manual
-- example, not a doctest. Doctests use tiny searches or replay recorded moves.
--
-- >>> solveTwoPhase (defaultOptions 0) (defaultOptions 0) solvedCube
-- TwoPhaseSolved [] []
solveTwoPhase :: SearchOptions -> SearchOptions -> Cube -> IO TwoPhaseResult
solveTwoPhase = solveTwoPhaseWith z3 {satCmd = "(check-sat-using (then simplify elim-term-ite solve-eqs dt2bv simplify bit-blast sat))"}

-- | Parse whitespace-separated uppercase face turns, optionally followed by
-- ASCII apostrophe or 2. Empty input is accepted; lowercase, R2', and commas
-- are rejected with a token and its one-based position in the message.
--
-- >>> parseMoves "R U R' U' F2"
-- Right [Move R Clockwise,Move U Clockwise,Move R Counterclockwise,Move U Counterclockwise,Move F HalfTurn]
-- >>> parseMoves "R2'"
-- Left "Token 1 \"R2'\": use R2 for a half-turn"
parseMoves :: String -> Either String [Move]
parseMoves = traverse parse . zip [(1::Int)..] . words
  where parse (i, token) = case token of
          c:suffix | Just f <- lookup c [('U',U),('D',D),('L',L),('R',R),('F',F),('B',B)]
                   , Just t <- lookup suffix [("",Clockwise),("2",HalfTurn),("'",Counterclockwise)]
                     -> Right (Move f t)
          _ -> Left ("Token " ++ show i ++ " " ++ show token ++ ": " ++ reason token)

        reason token
          | any (`elem` ",;:/|") token                                    = "use whitespace between moves, not punctuation separators"
          | c:_ <- token,          c `elem` "MES"                         = "unsupported slice move (M, E, S)"
          | c:_ <- token,          c `elem` "xyzXYZ"                      = "unsupported whole-cube rotation (x, y, z)"
          | c:w:_ <- token,        c `elem` "UDLRFBudlrfb", w `elem` "wW" = "unsupported wide turn"
          | c:_ <- token,          c `elem` "udlrfb"                      = "lowercase notation is unsupported; lowercase faces denote wide turns"
          | [c,'2','\''] <- token, c `elem` "UDLRFB"                      = "use " ++ [c,'2'] ++ " for a half-turn"
          | True                                                          = "expected U, D, L, R, F, or B with optional ' or 2; separate moves with whitespace"

-- | Canonical notation, separated by single spaces.
--
-- >>> renderMoves [Move R Clockwise, Move U HalfTurn, Move F Counterclockwise]
-- "R U2 F'"
renderMoves :: [Move] -> String
renderMoves = unwords . map render
  where render (Move f t) = show f ++ case t of
                                       Clockwise        -> ""
                                       HalfTurn         -> "2"
                                       Counterclockwise -> "'"

-- | ASCII net in the documented orientation, with a color legend.
--
-- >>> putStr (renderCube solvedCube)
--        U
--        w w w
--        w w w
--        w w w
-- L      F      R      B
-- o o o  g g g  r r r  b b b
-- o o o  g g g  r r r  b b b
-- o o o  g g g  r r r  b b b
--        D
--        y y y
--        y y y
--        y y y
-- w=white r=red g=green y=yellow o=orange b=blue
renderCube :: Cube -> String
renderCube (Cube cs) = unlines $
    ["       U"] ++ map ("       " ++) (rows 0)
 ++ ["L      F      R      B"]
 ++ [intercalate "  " [rows f !! r | f <- [4,2,1,5]] | r <- [0..2]]
 ++ ["       D"] ++ map ("       " ++) (rows 3)
 ++ ["w=white r=red g=green y=yellow o=orange b=blue"]
  where rows f = [unwords [[colorChar (cs !! (9*f+3*r+c))] | c <- [0..2]] | r <- [0..2]]
        colorChar White  = 'w'
        colorChar Red    = 'r'
        colorChar Green  = 'g'
        colorChar Yellow = 'y'
        colorChar Orange = 'o'
        colorChar Blue   = 'b'

-- | Print a scramble, its cube, search progress, and the solution.
-- This scramble turns three different faces, including a half-turn. Although
-- the depth bound is ten, the search stops when it finds a solution at three.
--
-- >>> demo 10 "R U F2"
-- Scramble: R U F2
--        U
--        w w w
--        w w w
--        b y y
-- L      F      R      B
-- g g r  y g g  o b b  o o o
-- o o r  y g g  o r r  w b b
-- o o w  r r r  y r r  w b b
--        D
--        g g g
--        y y b
--        y y b
-- w=white r=red g=green y=yellow o=orange b=blue
-- Checking depth 1
-- Checking depth 2
-- Checking depth 3
-- Solution (3 moves): F2 U' R'
demo :: Int -> String -> IO ()
demo bound input = case parseMoves input of
  Left err -> error err
  Right ms -> do
    let initial = applyMoves ms solvedCube
    putStrLn $ "Scramble: " ++ renderMoves ms
    putStr (renderCube initial)
    result <- solveWith z3 (defaultOptions bound) {showProgress = True} initial
    case result of
      Solved solution -> do let n = length solution
                                unit = if n == 1 then " move" else " moves"
                            putStrLn $ "Solution (" ++ show n ++ unit ++ "): " ++ renderMoves solution
      other           -> print other
