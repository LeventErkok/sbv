-----------------------------------------------------------------------------
-- |
-- Module    : Data.SBV.Compilers.C.RegExp
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Bounded derivative automata for dependency-free, exact C regex operations.
-----------------------------------------------------------------------------

{-# OPTIONS_GHC -Wall -Werror #-}

module Data.SBV.Compilers.C.RegExp (regexExpr) where

import Control.Monad (foldM, when)
import Control.Monad.State.Strict (StateT, evalStateT, get, put, lift)
import Data.Char (ord)
import Data.List (intercalate)
import Data.Maybe (fromMaybe)
import qualified Data.Map.Strict as Map
import qualified Data.Sequence as Seq
import qualified Data.Set as Set
import Text.PrettyPrint.HughesPJ (Doc, render, text)

import Data.SBV.Compilers.CodeGen (CgConfig(..))
import Data.SBV.Compilers.C.Lowering (CLowering(..), CRequirement(..), expressionLowering)
import qualified Data.SBV.Core.Data as S
import Data.SBV.Core.Symbolic (validateRegExp)

-- | A normalized residual language, caching nullability and tree size so
-- nullable concatenation and budget checks need no uncharged recursive walks.
data Regex = Regex { nullable  :: !Bool      -- ^ Whether this residual accepts the empty string.
                   , nodeCount :: !Integer   -- ^ Nodes in its normalized expression tree.
                   , form      :: !RegexForm -- ^ Canonical constructor and children.
                   }
           deriving (Eq, Ord)

-- | Union and intersection operands are sorted and duplicate-free;
-- concatenations are flattened. Complement is relative to the SBV alphabet.
data RegexForm = Empty
               | Epsilon
               | Character Int Int
               | Concatenate [Regex]
               | Unite [Regex]
               | Intersect [Regex]
               | Complement Regex
               | Star Regex
               deriving (Eq, Ord)

-- | Per-operation budgets. Work counts visited/constructed nodes and a
-- conservative allowance for normalization and automaton-state comparisons.
data Budget = Budget { configuration :: CgConfig  -- ^ User-selected limits for this operation.
                     , remainingWork :: !Integer -- ^ Work still available before generation fails.
                     }

-- | Pure compilation with explicit, recoverable internal budget failures.
type Build = StateT Budget (Either String)

-- | The empty language.
emptyRegex :: Regex
emptyRegex = Regex False 1 Empty

-- | The language containing only the empty string.
epsilonRegex :: Regex
epsilonRegex = Regex True 1 Epsilon

-- | All strings over SBV's character domain.
allRegex :: Regex
allRegex = Regex True 2 (Complement emptyRegex)

-- | One past the largest SBV character, including numeric surrogate values.
alphabetEnd :: Int
alphabetEnd = 0x30000

-- | Turn a compiler-budget failure into the usual generation diagnostic.
runCompiler :: CgConfig -> Build a -> a
runCompiler cfg action
  | any (<= 0) [cgRegexMaxStates cfg, cgRegexMaxNodes cfg, cgRegexMaxWork cfg]
  = error "SBV->C: Regex compilation is disabled by cgRegexLimits; all three limits must be positive."
  | True
  = either (error . ("SBV->C: " ++)) id $ evalStateT action (Budget cfg (cgRegexMaxWork cfg))

-- | Fail without printing a potentially huge input or derivative expression.
exceeded :: String -> Integer -> Build a
exceeded dimension limit = lift $ Left $ "Regex generation exceeds the " ++ dimension ++ " limit (" ++ show limit
                                      ++ "). Raise cgRegexLimits explicitly to permit more generation work."

-- | Charge work before performing the associated allocation or traversal.
charge :: Integer -> Build ()
charge amount = do
  budget <- get
  when (amount > remainingWork budget) $ exceeded "work" (cgRegexMaxWork (configuration budget))
  put budget { remainingWork = remainingWork budget - amount }

-- | Check a normalized expression or bounded expansion before allocating it.
checkNodes :: Integer -> Build ()
checkNodes count = do
  budget <- get
  let limit = cgRegexMaxNodes (configuration budget)
  when (count > limit) $ exceeded "expression-node" limit

-- | Construct a bounded node. Children are shared, not copied; charge the
-- immediate traversal while retaining the full expression-size bound.
node :: Bool -> RegexForm -> [Regex] -> Build Regex
node accepts shape children = do
  let count = 1 + sum (map nodeCount children)
  checkNodes count
  charge (1 + toInteger (length children))
  pure (Regex accepts count shape)

-- | Traverse a source list without first allocating an unbounded converted
-- list. This also bounds literals and concatenations before normalization.
boundedTraverse :: (a -> Build b) -> [a] -> Build [b]
boundedTraverse convert values = reverse . snd <$> foldM step (0, []) values
 where step (count, results) value = do
         checkNodes (count + 1)
         charge 1
         result <- convert value
         pure (count + 1, result : results)

-- | Flatten an associative operation after charging its input traversal.
flatten :: (RegexForm -> Maybe [Regex]) -> [Regex] -> Build [Regex]
flatten children rs = do
  let result = concatMap (\r -> fromMaybe [r] (children (form r))) rs
  charge (1 + toInteger (length rs + length result))
  pure result

-- | Canonicalize a Boolean operation without distributing it over other
-- operators. The comparison allowance is deliberately conservative.
boolean :: Bool -> [Regex] -> Build Regex
boolean intersection rs = do
  flat <- flatten children rs
  charge (comparisonDepth (length flat) * (1 + sum (map nodeCount flat)))
  let absorbing = if intersection then emptyRegex else allRegex
      identity  = if intersection then allRegex else emptyRegex
      members   = Set.fromList (filter (/= identity) flat)
      opposite r = case form r of
                     Complement value -> value `Set.member` members
                     _                -> False
  if absorbing `Set.member` members || any opposite members
    then pure absorbing
    else case Set.toAscList members of
           []  -> pure identity
           [r] -> pure r
           xs  -> node (if intersection then all nullable xs else any nullable xs)
                       (if intersection then Intersect xs else Unite xs) xs
 where children (Intersect xs) | intersection     = Just xs
       children (Unite xs)     | not intersection = Just xs
       children _                                = Nothing

-- | Flatten concatenation, eliminate epsilon, and propagate the empty language.
concatenate :: [Regex] -> Build Regex
concatenate rs = do
  flat <- flatten children rs
  if any ((== Empty) . form) flat
    then pure emptyRegex
    else case filter ((/= Epsilon) . form) flat of
           []  -> pure epsilonRegex
           [r] -> pure r
           xs  -> node (all nullable xs) (Concatenate xs) xs
 where children (Concatenate xs) = Just xs
       children _                = Nothing

-- | Cancel double complements; no language approximation is performed.
complement :: Regex -> Build Regex
complement r = case form r of
                 Complement value -> charge 1 >> pure value
                 _                -> node (not (nullable r)) (Complement r) [r]

-- | Normalize trivial and nested stars without unrolling any repetition.
star :: Regex -> Build Regex
star r = case form r of
           Empty   -> pure epsilonRegex
           Epsilon -> pure epsilonRegex
           Star _  -> pure r
           _       -> node True (Star r) [r]

-- | Translate every SBV regex constructor. Bounded repetitions are expanded
-- only after checking their size; invalid bounds retain the frontend diagnostic.
convertRegex :: S.RegExp -> Build Regex
convertRegex regex = do
  charge 1
  result <- case regex of
    S.Literal value -> boundedTraverse character value >>= concatenate
    S.All           -> pure allRegex
    S.AllChar       -> node False (Character 0 (alphabetEnd - 1)) []
    S.None          -> pure emptyRegex
    S.Range lo hi   -> do
      a <- code lo
      b <- code hi
      if a > b then pure emptyRegex else node False (Character a b) []
    S.Conc rs       -> boundedTraverse convertRegex rs >>= concatenate
    S.Union rs      -> boundedTraverse convertRegex rs >>= boolean False
    S.Inter a b     -> pair a b >>= boolean True
    S.Diff a b      -> do
      left  <- convertRegex a
      right <- convertRegex b >>= complement
      boolean True [left, right]
    S.Comp r        -> convertRegex r >>= complement
    S.KStar r       -> convertRegex r >>= star
    S.KPlus r       -> do
      body <- convertRegex r
      rest <- star body
      concatenate [body, rest]
    S.Opt r         -> convertRegex r >>= \body -> boolean False [epsilonRegex, body]
    S.Loop lo hi r  -> validateRegExp (S.Loop lo hi (S.Literal "")) `seq` repeatRegex lo hi r
    S.Power n r     -> validateRegExp (S.Power n (S.Literal "")) `seq` repeatRegex n n r
  checkNodes (nodeCount result)
  pure result
 where code c
         | ord c < alphabetEnd = pure (ord c)
         | True                = lift $ Left "Regex character is outside SBV's domain 0..0x2ffff."

       character c = do
         value <- code c
         node False (Character value value) []

       pair a b = sequence [convertRegex a, convertRegex b]

       repeatRegex lo hi r = do
         checkNodes (1 + toInteger hi)
         charge (toInteger hi)
         body <- convertRegex r
         optional <- boolean False [epsilonRegex, body]
         checkNodes (1 + toInteger lo * nodeCount body + toInteger (hi - lo) * nodeCount optional)
         concatenate (replicate lo body ++ replicate (hi - lo) optional)

-- | Compute the left derivative by a single representative character.
-- Nullability of the result states whether the consumed input is accepted.
derivative :: Int -> Regex -> Build Regex
derivative c regex = do
  charge 1
  case form regex of
    Empty             -> pure emptyRegex
    Epsilon           -> pure emptyRegex
    Character lo hi   -> pure $ if lo <= c && c <= hi then epsilonRegex else emptyRegex
    Unite rs          -> mapM (derivative c) rs >>= boolean False
    Intersect rs      -> mapM (derivative c) rs >>= boolean True
    Complement r      -> derivative c r >>= complement
    Star r            -> derivative c r >>= \first -> concatenate [first, regex]
    Concatenate []    -> pure emptyRegex
    Concatenate (r:rs) -> do
      first <- derivative c r >>= \value -> concatenate (value : rs)
      if nullable r
        then do rest <- concatenate rs >>= derivative c
                boolean False [first, rest]
        else pure first

-- | Partition the complete character domain at every literal/range boundary.
-- Derivatives cannot introduce new boundaries, so representatives are exact.
alphabet :: [Regex] -> Build [(Int, Int)]
alphabet regexes = do
  cuts <- foldM visit (Set.fromList [0, alphabetEnd]) regexes
  let points = Set.toAscList cuts
  pure [(lo, end - 1) | (lo, end) <- zip points (drop 1 points)]
 where visit cuts r = do
         charge 1
         case form r of
           Character lo hi -> pure $ Set.insert lo (Set.insert (hi + 1) cuts)
           Concatenate rs  -> foldM visit cuts rs
           Unite rs        -> foldM visit cuts rs
           Intersect rs    -> foldM visit cuts rs
           Complement x    -> visit cuts x
           Star x          -> visit cuts x
           _               -> pure cuts

-- | A complete automaton or an early language-inequality witness. An accepting
-- state in a membership automaton is not itself an inequality witness.
data Exploration = CompleteAutomaton [(Bool, [Int])] -- ^ All reachable states and transitions.
                 | InequalityWitness                -- ^ A reachable pair differs in acceptance.

-- | Explore states breadth-first, assigning deterministic integer indices.
-- Language comparison stops at the first accepting product state (a witness
-- of inequality); membership builds all reachable rows. State limits apply
-- before insertion, including to pairs explored for language comparison.
explore :: Ord a => Bool -> (a -> Bool) -> (a -> Integer) -> (Int -> a -> Build a)
        -> [(Int, Int)] -> a -> Build Exploration
explore stop accepts size step classes initial = go (Map.singleton initial 0) (Seq.singleton initial) []
 where go known pending rows = case Seq.viewl pending of
         Seq.EmptyL -> pure (CompleteAutomaton (reverse rows))
         r Seq.:< rest -> do
           charge 1
           if stop && accepts r
             then pure InequalityWitness
             else do
               (known', pending', reversed) <- foldM (transition r) (known, rest, []) classes
               go known' pending' ((accepts r, reverse reversed) : rows)

       transition r (known, pending, indices) (c, _) = do
         next <- step c r
         charge (comparisonDepth (Map.size known) * size next)
         case Map.lookup next known of
           Just index -> pure (known, pending, index : indices)
           Nothing -> do
             budget <- get
             let index = Map.size known
                 limit = cgRegexMaxStates (configuration budget)
             when (toInteger index >= limit) $ exceeded "state" limit
             pure (Map.insert next index known, pending Seq.|> next, index : indices)

-- | Conservative logarithmic comparison allowance for balanced maps and sets.
comparisonDepth :: Int -> Integer
comparisonDepth count
  | count <= 1 = 1
  | True       = 1 + comparisonDepth (count `quot` 2)

-- | Compile exact membership into function-local static tables and a guarded
-- loop. Locally scoped names work unchanged in definitions, callbacks, and
-- library components; dead operations are never compiled by the scheduler.
regexExpr :: CgConfig -> S.Op -> S.SV -> [Doc] -> Maybe CLowering
regexExpr cfg (S.StrOp (S.StrInRe regex)) result [value] = Just $ runCompiler cfg $ do
  initial <- convertRegex regex
  classes <- alphabet [initial]
  automaton <- explore False nullable nodeCount derivative classes initial
  case automaton of
    CompleteAutomaton rows -> pure $ membership result value classes rows
    InequalityWitness      -> lift $ Left "Unexpected inequality witness during regex membership compilation."
regexExpr cfg (S.RegExOp operation) _ [] = Just $ runCompiler cfg $ do
  let (left, right, negateResult) = case operation of
        S.RegExEq  a b -> (a, b, False)
        S.RegExNEq a b -> (a, b, True)
  a <- convertRegex left
  b <- convertRegex right
  classes <- alphabet [a, b]
  comparison <- explore True (\(x, y) -> nullable x /= nullable y) (\(x, y) -> nodeCount x + nodeCount y)
                       (\c (x, y) -> (,) <$> derivative c x <*> derivative c y) classes (a, b)
  let equal = case comparison of
                CompleteAutomaton{} -> True
                InequalityWitness   -> False
  pure $ expressionLowering [] (text (if equal /= negateResult then "true" else "false"))
regexExpr _ _ _ _ = Nothing

-- | Render an allocation-free matcher over canonical SBV text, preserving
-- embedded NULs and surrogate character codes. Use compact transition entries
-- when all actual state indices fit, falling back to size_t for larger custom
-- budgets. Input size is independent of the generation budgets.
membership :: S.SV -> Doc -> [(Int, Int)] -> [(Bool, [Int])] -> CLowering
membership result value classes rows = (expressionLowering [CRequiresText] (text answer))
  { loweringDeclarations = map text
      [ "static const uint32_t " ++ bounds ++ "[] = {" ++ intercalate ", " (map (show . snd) classes) ++ "};"
      , "static const uint8_t " ++ accepting ++ "[] = {" ++ intercalate ", " [if yes then "1" else "0" | (yes, _) <- rows] ++ "};"
      , "static const " ++ transitionType ++ " " ++ transitions ++ "[][" ++ show (length classes) ++ "] = {\n"
          ++ intercalate ",\n" ["  {" ++ intercalate ", " (map show indices) ++ "}" | (_, indices) <- rows] ++ "\n};"
      , "SBool " ++ answer ++ ";"
      ]
  , loweringSetup = [text $ unlines
      [ "{"
      , "  const SString input = " ++ render value ++ ";"
      , "  size_t state = 0;"
      , "  for (size_t offset = 0; offset < input.byte_length;) {"
      , "    const SChar character = sbv_text_decode(input.data + offset);"
      , "    if (character > UINT32_C(0x2ffff)) abort();"
      , "    offset += sbv_text_width(input.data[offset]);"
      , "    size_t column = 0;"
      , "    while (column + 1 < " ++ show (length classes) ++ " && character > " ++ bounds ++ "[column]) ++column;"
      , "    state = " ++ transitions ++ "[state][column];"
      , "  }"
      , "  " ++ answer ++ " = " ++ accepting ++ "[state];"
      , "}"
      ]]
  }
 where prefix      = "sbv_regex_" ++ show result
       transitionType | toInteger (length rows) <= 65536 = "uint16_t"
                      | True                            = "size_t"
       answer      = prefix ++ "_result"
       bounds      = prefix ++ "_bounds"
       accepting   = prefix ++ "_accept"
       transitions = prefix ++ "_step"
