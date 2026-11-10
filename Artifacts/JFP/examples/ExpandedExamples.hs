{-# LANGUAGE DataKinds #-}
{-# LANGUAGE OverloadedLists #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}

-- Worked examples for the semantic-domain, representation, and audit sections.
module ExpandedExamples
  ( lowNibble, highNibble, packNibbles, fieldRoundTrip
  , narrowExact, powerOfTwo, powerOfTwoSpec, powerOfTwoCorrect
  , exactThird, positiveSquareRoot, roundingExample, finiteAssociativity
  , softPreferences, ripple, rippleByte, circuitEquivalence
  , scopedQuery, coreExample
  , Key, SKey, keyCode, keyCongruence, advance, advanceContract, twoAdvances
  , headOption, divOption, headOptionSpec
  , integerZeroDivision, unspecifiedPayload, guardedPayload, checkedFromJust
  , identifierPattern, validIdentifier, identifierSpec
  , activate, activationPreserves, oneOffset, offsetPerInput
  , byteAdditionBridge, auditProofs, expandedChecks
  ) where

import Data.Char (isAsciiLower)
import Data.List (isInfixOf)
import Data.SBV
import Data.SBV.Control
import Data.SBV.TP
import qualified Data.SBV.List as SL
import qualified Data.SBV.Maybe as SM
-- BEGIN regexImport
import qualified Data.SBV.RegExp as RE
-- END regexImport
-- BEGIN setImport
import qualified Data.SBV.Set as SS
-- END setImport
-- BEGIN addersImport
import qualified Documentation.SBV.Examples.BitPrecise.Adders as Adders
-- END addersImport

-- BEGIN byteFields
lowNibble, highNibble :: SWord8 -> SWord8
lowNibble x = x .&. 15
highNibble x = x `shiftR` 4

packNibbles :: SWord8 -> SWord8 -> SWord8
packNibbles hi lo = (lowNibble hi `shiftL` 4) .|. lowNibble lo

fieldRoundTrip :: SWord8 -> SBool
fieldRoundTrip x = packNibbles (highNibble x) (lowNibble x) .== x
-- END byteFields

-- BEGIN narrowExact
narrowExact :: SInteger -> SBool
narrowExact n = (0 .<= n .&& n .<= 255) .=>
  sFromIntegral (sFromIntegral n :: SWord8) .== n
-- END narrowExact

-- BEGIN powerOfTwo
powerOfTwo :: SWord8 -> SBool
powerOfTwo x = x ./= 0 .&& (x .&. (x - 1)) .== 0

powerOfTwoSpec :: SWord8 -> SBool
powerOfTwoSpec x = sOr [x .== literal (2 ^ k) | k <- [0 .. 7 :: Int]]

powerOfTwoCorrect :: SWord8 -> SBool
powerOfTwoCorrect x = powerOfTwo x .== powerOfTwoSpec x
-- END powerOfTwo

-- BEGIN exactReal
exactThird :: SReal -> SBool
exactThird x = x / 3 + x / 3 + x / 3 .== x

positiveSquareRoot :: IO SatResult
positiveSquareRoot = sat $ do
  x <- sReal "root"
  pure $ x .> 0 .&& x * x .== 2
-- END exactReal

-- Check the algebraic model in the exact symbolic domain, never through Double.
rootChecked :: IO Bool
rootChecked = do
  r <- positiveSquareRoot
  print r
  case getModelValue "root" r of
    Just (v :: AlgReal) -> isTheorem $ do
      x <- sReal "x"
      pure $ x .== literal v .=> x .> 0 .&& x * x .== 2
    Nothing -> pure False

-- BEGIN floatRounding
roundingExample :: SBool
roundingExample =
  let x = 16777216 :: SFloat
  in fpAdd sRNE x 1 .== x .&&
     fpAdd sRTP x 1 .== 16777218

finiteAssociativity :: SFloat -> SFloat -> SFloat -> SBool
finiteAssociativity x y z =
  let left  = (x + y) + z
      right = x + (y + z)
  in sAnd (map fpIsPoint [x, y, z, x+y, y+z, left, right])
     .=> left .== right
-- END floatRounding

floatCounterexample :: IO Bool
floatCounterexample = do
  -- Fix an exactly representable example so the printed lesson is reproducible.
  r <- prove $ do
    z <- sFloat "z"
    constrain $ z .== -16777216
    pure $ finiteAssociativity 16777216 1 z
  print r
  let x = 16777216 :: Float
      z = -16777216 :: Float
  pure $ getModelValue "z" r == Just z &&
         (x+1)+z == 0 && x+(1+z) == 1

-- BEGIN softPreferences
softPreferences :: IO OptimizeResult
softPreferences = optimize Lexicographic $ do
  x <- sInteger "choice"
  constrain $ 0 .<= x .&& x .<= 2
  assertWithPenalty "prefer-zero" (x .== 0) (Penalty 2 Nothing)
  assertWithPenalty "prefer-two"  (x .== 2) (Penalty 3 Nothing)
-- END softPreferences

softChecked :: IO Bool
softChecked = do
  r <- softPreferences
  print r
  let cost :: Integer -> Integer
      cost x = (if x == 0 then 0 else 2) + (if x == 2 then 0 else 3) :: Integer
  pure $ case r of
    LexicographicResult m -> case getModelValue "choice" m of
      Just (x :: Integer) -> x `elem` ([0,1,2] :: [Integer]) && cost x == minimum (map cost [0,1,2])
      Nothing -> False
    _ -> False

-- BEGIN rippleCircuit
ripple :: SBool -> [(SBool, SBool)] -> ([SBool], SBool)
ripple carry [] = ([], carry)
ripple carry ((a,b):rest) = (sumBit : bits, finalCarry)
  where sumBit = a .<+> b .<+> carry
        next = (a .&& b) .|| (carry .&& (a .<+> b))
        (bits, finalCarry) = ripple next rest

rippleByte :: SWord8 -> SWord8 -> SWord8
rippleByte x y = fromBitsLE bits
  where (bits, _) = ripple sFalse (zip (blastLE x) (blastLE y))

circuitEquivalence :: SWord8 -> SWord8 -> SBool
circuitEquivalence x y =
  rippleByte x y .== x + y .&&
  rippleByte x y .== fromBitsLE lookaheadBits
  where (lookaheadBits, _) = Adders.lookaheadAdd sFalse (zip (blastLE x) (blastLE y))
-- END rippleCircuit

-- BEGIN scopedQuery
scopedQuery :: IO [CheckSatResult]
scopedQuery = runSMT $ do
  x <- sInteger "x"
  constrain $ x .>= 0
  query $ do
    push 1
    constrain $ x .< 0
    impossible <- checkSat
    pop 1
    temporary <- checkSatAssuming [x .== 3]
    restored <- checkSatAssuming [x .== 4]
    pure [impossible, temporary, restored]
-- END scopedQuery

-- BEGIN coreExample
coreExample :: IO [String]
coreExample = runSMT $ do
  setOption $ ProduceUnsatCores True
  x <- sInteger "x"
  namedConstraint "nonnegative" $ x .>= 0
  namedConstraint "negative"    $ x .< 0
  namedConstraint "upper"       $ x .< 100
  query $ do
    answer <- checkSat
    case answer of
      Unsat -> getUnsatCore
      _     -> io $ fail "expected contradictory bounds"
-- END coreExample

coreChecked :: IO Bool
coreChecked = do
  names <- coreExample
  print names
  -- Re-check the returned subset; do not demand a particular order or minimal core.
  let facts x = [("nonnegative", x .>= 0), ("negative", x .< 0), ("upper", x .< 100)]
  if null names || any (`notElem` map fst (facts (0 :: SInteger))) names
    then pure False
    else isTheorem $ \(x :: SInteger) -> sNot $ sAnd [p | (n,p) <- facts x, n `elem` names]

-- BEGIN keySymbolic
data Key
mkSymbolic [''Key]
-- END keySymbolic

-- BEGIN abstractKeys
keyCode :: SKey -> SInteger
keyCode = uninterpret "keyCode"

keyCongruence :: SKey -> SKey -> SBool
keyCongruence x y = x .== y .=> keyCode x .== keyCode y
-- END abstractKeys

-- BEGIN advanceContract
advance :: SInteger -> SInteger
advance = uninterpret "advance"

advanceContract :: (SInteger -> SInteger) -> SBool
advanceContract f = quantifiedBool $ \(Forall n) -> f n .> n

twoAdvances :: SInteger -> SBool
twoAdvances n = advanceContract advance .=> advance (advance n) .>= n + 2
-- END advanceContract

contractContradiction :: IO Bool
contractContradiction = isTheorem $
  advanceContract advance .&& advance 0 .== 0 .=> sFalse

-- BEGIN optionalOperations
headOption :: SList Integer -> SMaybe Integer
headOption xs = ite (SL.null xs) SM.sNothing (SM.sJust (SL.head xs))

divOption :: SInteger -> SInteger -> SMaybe Integer
divOption x y = ite (y .== 0) SM.sNothing (SM.sJust (x `sDiv` y))

headOptionSpec :: SList Integer -> SBool
headOptionSpec xs = SM.isJust (headOption xs) .== sNot (SL.null xs)
-- END optionalOperations

integerZeroDivision :: SInteger -> SBool
integerZeroDivision x =
  x `sDiv` 0 .== 0 .&& x `sQuot` 0 .== 0 .&&
  x `sMod` 0 .== x .&& x `sRem` 0 .== x

-- BEGIN maybePayload
unspecifiedPayload :: Integer -> IO SatResult
unspecifiedPayload n = sat $
  (SM.fromJust SM.sNothing :: SInteger) .== literal n

guardedPayload :: SMaybe Integer -> SBool
guardedPayload m = SM.isJust m .=> SM.sJust (SM.fromJust m) .== m
-- END maybePayload

-- BEGIN checkedPayload
checkedFromJust :: SMaybe Integer -> SInteger
checkedFromJust m =
  sAssert Nothing "fromJust requires Just" (SM.isJust m) (SM.fromJust m)
-- END checkedPayload

safeFromJust :: IO [SafeResult]
safeFromJust =
-- BEGIN safePayload
  safe $ do
    m <- free "m" :: Symbolic (SMaybe Integer)
    constrain $ SM.isJust m
    output $ sAssert Nothing "fromJust requires Just"
               (SM.isJust m) (SM.fromJust m)
-- END safePayload

payloadSafetyChecked :: IO Bool
payloadSafetyChecked = do
  unchecked <- safe (SM.fromJust SM.sNothing :: SInteger)
  bad <- safe checkedFromJust
  good <- safeFromJust
  print unchecked
  print bad
  print good
  pure $ null unchecked && case (bad, good) of
    ([SafeResult (_, _, r@Satisfiable{})], [SafeResult (_, _, Unsatisfiable{})]) ->
      getModelValue "s0" (SatResult r) == Just (Nothing :: Maybe Integer)
    _ -> False

-- Separate satisfiability checks deliberately permit different interpretations.
unspecifiedPayloadChecked :: IO Bool
unspecifiedPayloadChecked = do
  zeroResult <- unspecifiedPayload 0
  oneResult  <- unspecifiedPayload 1
  print zeroResult
  print oneResult
  consistent <- isTheorem $
    let payload = SM.fromJust SM.sNothing :: SInteger
    in sNot (payload .== 0 .&& payload .== 1)
  pure $ isSat zeroResult && isSat oneResult && consistent
  where isSat (SatResult Satisfiable{}) = True
        isSat _                       = False

-- Empty-sequence selectors also admit different interpretations.
unspecifiedSelectorsChecked :: IO Bool
unspecifiedSelectorsChecked = and <$> mapM permits ([0,1] :: [Integer])
  where permits n = do
          r <- sat $ SL.head (literal [] :: SList Integer) .== literal n
          pure $ case r of SatResult Satisfiable{} -> True; _ -> False

euclideanZeroChecked :: IO Bool
euclideanZeroChecked = and <$> mapM permits ([0,1] :: [Integer])
  where permits n = do
          r <- sat $ do
            x <- sInteger "x"
            y <- sInteger "y"
            constrain $ x .== 5 .&& y .== 0
            pure $ x `sEDiv` y .== literal n .&& x `sEMod` y .== literal n
          pure $ case r of SatResult Satisfiable{} -> True; _ -> False

-- BEGIN regexValidator
identifierPattern :: RE.RegExp
identifierPattern = RE.Loop 3 3 (RE.Range 'a' 'z')

validIdentifier :: SString -> SBool
validIdentifier s = SL.length s .== 3 .&&
  sAnd [lower (s SL.!! literal i) | i <- [0 .. 2 :: Integer]]
  where lower c = literal 'a' .<= c .&& c .<= literal 'z'

identifierSpec :: SString -> SBool
identifierSpec s = validIdentifier s .== RE.match s identifierPattern
-- END regexValidator

-- BEGIN setInvariant
activate :: SInteger -> SSet Integer -> SSet Integer
activate = SS.insert

activationPreserves :: SInteger -> SSet Integer -> SSet Integer -> SBool
activationPreserves user active allowed =
  active `SS.isSubsetOf` allowed .&& user `SS.member` allowed
  .=> activate user active `SS.isSubsetOf` allowed
-- END setInvariant

-- BEGIN quantifierOrder
oneOffset :: IO SatResult
oneOffset = sat $ \(Exists offset :: Exists "offset" Integer)
                    (Forall x :: Forall "x" Integer) -> offset .== x + 1

offsetPerInput :: IO SatResult
offsetPerInput = sat $ \(Forall x :: Forall "x" Integer)
                         (Exists offset :: Exists "offset" Integer) -> offset .== x + 1
-- END quantifierOrder

-- BEGIN encodingBridge
byteAdditionBridge :: SWord8 -> SWord8 -> SBool
byteAdditionBridge x y =
  sFromIntegral (x+y) .== (a+b) `sMod` 256
  where a = sFromIntegral x :: SInteger
        b = sFromIntegral y :: SInteger
-- END encodingBridge

-- BEGIN auditProofs
auditProofs :: IO Bool
auditProofs = do
  clean <- runTP $ lemma "checkedIdentity"
    (\(Forall n :: Forall "n" Integer) -> n+n .== 2*n) []
  draft <- runTP $ lemma "draftIdentity"
    (\(Forall n :: Forall "n" Integer) -> n+n .== 2*n) [sorry]
  putStrLn $ showProofTree True draft
  print $ rootOfTrust draft
  pure $ case (rootOfTrust clean, rootOfTrust draft) of
    (RootOfTrust Nothing, RootOfTrust (Just _)) ->
      "Modulo" `isInfixOf` show draft
    _ -> False
-- END auditProofs

expandedChecks :: (String -> IO Bool -> IO ()) -> IO ()
expandedChecks check = do
  check "byte field round trip" $ isTheorem fieldRoundTrip
  check "byte field round trip with CVC5" $ do
    r <- proveWith cvc5 fieldRoundTrip
    pure $ case r of ThmResult Unsatisfiable{} -> True; _ -> False
  check "nibble masking and arithmetic oracle (all 256 bytes)" $ pure $ and
    [ unliteral (lowNibble (literal x)) == Just (x `mod` 16)
      && unliteral (highNibble (literal x)) == Just (x `div` 16)
    | x <- [0 .. 255 :: Word8]]
  check "rotation inverse and signed versus unsigned shifts" $ do
    p <- isTheorem $ \(x :: SWord8) -> rotateR (rotateL x 3) 3 .== x
    pure $ p && unliteral ((128 :: SWord8) `shiftR` 1) == Just 64 &&
                unliteral ((-128 :: SInt8) `shiftR` 1) == Just (-64)
  check "narrowing with a range contract" $ isTheorem narrowExact
  check "power-of-two bit trick" $ isTheorem powerOfTwoCorrect
  check "power-of-two against concrete popcount (all 256 bytes)" $ pure $ and
    [unliteral (powerOfTwo (literal x)) == Just (popCount x == 1) | x <- [0 .. 255 :: Word8]]
  check "symbolic rational construction" $ isTheorem $
    ((1 .% 3) + (1 .% 3) + (1 .% 3)) .== 1
  check "exact rational arithmetic" $ isTheorem exactThird
  check "exact algebraic root model" rootChecked
  check "explicit floating-point rounding" $ isTheorem roundingExample
  check "finite floating-point associativity counterexample" floatCounterexample
  check "weighted soft constraints versus enumerated costs" softChecked
  check "ripple, lookahead, and machine addition agree at eight bits" $ isTheorem circuitEquivalence
  check "query scope is restored" $ (== [Unsat, Sat, Sat]) <$> scopedQuery
  check "unsat core replay" coreChecked
  check "uninterpreted function congruence" $ isTheorem keyCongruence
  check "contract implies progress after two calls" $ isTheorem twoAdvances
  check "contract has a concrete implementation" $ isTheorem (advanceContract (+1))
  check "contradictory contract detected" contractContradiction
  check "integer division by zero uses quotient zero and remainder dividend" $
    isTheorem integerZeroDivision
  check "unsigned and signed byte division by zero follows the same convention" $ do
    u <- isTheorem $ \(x :: SWord8) ->
      x `sDiv` 0 .== 0 .&& x `sQuot` 0 .== 0 .&&
      x `sMod` 0 .== x .&& x `sRem` 0 .== x
    s <- isTheorem $ \(x :: SInt8) ->
      x `sDiv` 0 .== 0 .&& x `sQuot` 0 .== 0 .&&
      x `sMod` 0 .== x .&& x `sRem` 0 .== x
    pure $ u && s
  check "real and rational division by zero returns zero" $ do
    r <- isTheorem $ \(x :: SReal) -> x / 0 .== 0
    q <- isTheorem $ \(x :: SRational) -> x / 0 .== 0
    pure $ r && q
  check "IEEE zero-divisor examples yield infinities and NaN" $ isTheorem $
    fpIsPositive (1/0 :: SFloat) .&& fpIsInfinite (1/0 :: SFloat) .&&
    fpIsNegative ((-1)/0 :: SFloat) .&& fpIsInfinite ((-1)/0 :: SFloat) .&&
    fpIsNaN (0/0 :: SFloat) .&&
    fpIsInfinite (1/0 :: SDouble) .&& fpIsNaN (0/0 :: SDouble)
  check "Nothing payload admits different models but is consistent within each" unspecifiedPayloadChecked
  check "safe checks explicit payload assertions and reports Nothing" payloadSafetyChecked
  check "empty-list head admits different results" unspecifiedSelectorsChecked
  check "Euclidean zero division and modulus admit different results" euclideanZeroChecked
  check "Just precondition justifies payload reconstruction" $ isTheorem guardedPayload
  check "explicit Maybe defaults cover both constructors" $ isTheorem $ \(d :: SInteger) x ->
    SM.fromMaybe d SM.sNothing .== d .&& SM.fromMaybe d (SM.sJust x) .== x
  check "optional list head constructor contract" $ isTheorem headOptionSpec
  check "optional division constructor and value" $ isTheorem $ \(x :: SInteger) y ->
    (SM.isNothing (divOption x y) .== (y .== 0)) .&&
    (y ./= 0 .=> SM.fromJust (divOption x y) .== x `sDiv` y)
  check "identifier validator agrees with regex" $ isTheorem identifierSpec
  check "identifier validator concrete oracle" $ pure $ and
    [unliteral (validIdentifier (literal s)) == Just (length s == 3 && all isAsciiLower s)
    | s <- ["", "a", "abc", "ABC", "a0", "a_b", "é", "\n"]]
  check "activation preserves allowed-set invariant" $ isTheorem activationPreserves
  check "set operation concrete membership oracle" $ pure $
    unliteral (3 `SS.member` activate 3 (SS.fromList [1,2])) == Just True &&
    unliteral (4 `SS.member` activate 3 (SS.fromList [1,2])) == Just False
  check "existential before universal has no offset" $ do
    r <- oneOffset
    print r
    pure $ case r of SatResult Unsatisfiable{} -> True; _ -> False
  check "existential after universal permits input-dependent offset" $ do
    r <- offsetPerInput
    print r
    pure $ case r of SatResult Satisfiable{} -> True; _ -> False
  check "bit-vector/integer encoding bridge" $ isTheorem byteAdditionBridge
  check "auditing a checked proof versus a draft" auditProofs
