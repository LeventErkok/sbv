-----------------------------------------------------------------------------
-- |
-- Module    : TestSuite.Queries.Registration
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Registration and function discovery during incremental solver interaction.
-----------------------------------------------------------------------------

{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE FlexibleInstances   #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell     #-}
{-# LANGUAGE TypeApplications    #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module TestSuite.Queries.Registration (tests) where

import Control.Monad (when)
import Control.Monad.Reader (ReaderT(..), runReaderT)
import qualified Control.Exception as C
import Data.List (isInfixOf, isPrefixOf)
import Data.Maybe (fromMaybe)
import Data.Proxy
import System.FilePath ((</>))
import System.IO.Temp (withSystemTempDirectory)

import Data.SBV.Control
import Data.SBV.Internals (QueryT(..), SMTModel(..), SExpr(..), parseSExpr, formatFunctionResponse)
import Utils.SBVTestFramework

-- | A rational field must be declared before the containing datatype.
newtype RationalBox = RationalBox Rational deriving (Eq, Show)

-- | An empty datatype represents an uninterpreted solver sort.
data RegistrationSort

mkSymbolic [''RationalBox, ''RegistrationSort]

tests :: TestTree
tests = testGroup "Queries.Registration"
  [ testGroup "rationals"
      [ rationalTest "automatic"                 False False
      , rationalTest "registered before query"   True  False
      , rationalTest "registered inside query"   False True
      , rationalTest "registered in both phases" True  True
      ]
  , testCase "rational function first used in query" $ do
      let half :: SInteger -> SRational
          half = smtFunction "registration.half" $ \n -> ite (n .== 1) (1/2) (2/3)
      result <- runSMT $ query $ do
        n <- freshVar @Integer "n"
        constrain $ n .== 1
        getValue (half n)
      result == 1 % 2 @? "Expected a rational result from a query-mode definition"
  , testCase "nested rational types first used in query" $ do
      result <- runSMT $ query $ do
        x <- freshVar @(RationalBox, [Rational]) "x"
        let expected = (RationalBox (1 % 2), [2 % 3])
        constrain $ x .== literal expected
        getValue x
      result == (RationalBox (1 % 2), [2 % 3]) @? "Expected nested rational values"
  , testCase "explicit nested type registration inside query" $ do
      result <- runSMT $ query $ do
        registerType (Proxy @(RationalBox, [Rational]))
        registerType (Proxy @(RationalBox, [Rational]))
        ensureSat
        x <- freshVar @(RationalBox, [Rational]) "x"
        constrain $ x .== literal (RationalBox (1 % 2), [2 % 3])
        getValue x
      result == (RationalBox (1 % 2), [2 % 3]) @? "Explicit registration must reach the solver"
  , testCase "explicit uninterpreted sort registration inside query" $ do
      result <- runSMT $ query $ do
        registerType (Proxy @RegistrationSort)
        registerType (Proxy @RegistrationSort)
        ensureSat
        x <- freshVar @RegistrationSort "x"
        y <- freshVar_ @RegistrationSort
        constrain $ x ./= y
        checkSat
      result == Sat @? "Explicit registration must declare an uninterpreted sort exactly once"
  , testCase "quantified function first used in query" $ do
      result <- runSMT $ query $ do
        let f = uninterpret "registration.quantified" :: SInteger -> SInteger
        constrain $ \(Forall (x :: SInteger)) -> f x .== f x
        checkSat
      result == Sat @? "Quantified uses must register their functions automatically"
  , testGroup "function discovery" $ map discoveryTests [("z3", z3), ("cvc5", cvc5)]
  , fallbackTests
  ]

-- | Discovery must support sorts without concrete defaults and preserve the
-- model produced by checkSatAssuming, including when discovery fails.
discoveryTests :: (String, SMTConfig) -> TestTree
discoveryTests (solverName, cfg) = testGroup solverName
  [ testCase "quoted function expression formatting" $ do
      let f = uninterpret "|quotedPretty|" :: SInteger -> SInteger
      result <- runSMTWith cfg $ do
        setupFunctionModels solverName
        constrain $ \(Forall x) -> f x .== 3 * x
        query $ ensureSat >> getFunction f
      case result of
        Left (rendered, _) -> do
          "quotedPretty " `isPrefixOf` rendered @? "Expected the function name in the formatted interpretation"
          not ("fromSMTLib" `isInfixOf` rendered) @? "Expected the lambda to be formatted despite optional name quoting"
        Right{} -> assertFailure "Expected an expression for the nonconstant integer function"
  , testGroup "registered calling convention"
      [ testCase (if registeredCurried then "curried" else "uncurried") $ do
          let curried   = uninterpret "registeredShape" :: SInteger -> SInteger -> SInteger
              uncurried = uninterpret "registeredShape" :: (SInteger, SInteger) -> SInteger
              f x y | registeredCurried = curried x y
                    | True             = uncurried (x, y)
          result <- runSMTWith cfg $ do
            setupFunctionModels solverName
            constrain $ \(Forall x) (Forall y) -> f x y .== 3 * x + y
            query $ do
              ensureSat
              if registeredCurried then getFunction uncurried else getFunction curried
          case result of
            Left (_, (isCurried, _, _)) -> isCurried == registeredCurried @? "Reading through an alias must preserve the registered display convention"
            Right{} -> assertFailure "Expected an expression for the nonconstant integer function"
      | registeredCurried <- [True, False]
      ]
  , testCase "uninterpreted argument sort" $ do
      let f = uninterpret "discovery.sort" :: SBV RegistrationSort -> SInteger
      result <- runSMTWith cfg $ do
        registerFunction f
        query $ ensureSat >> getFunction f
      case result of
        Right{} -> pure ()
        Left{}  -> assertFailure "Expected an interpretation of the unused function"
  , testCase "uncurried function with an uninterpreted argument sort" $ do
      let f = uninterpret "discovery.uncurried" :: (SBV RegistrationSort, SBool) -> SInteger
      result <- runSMTWith cfg $ do
        registerFunction f
        query $ ensureSat >> getFunction f
      case result of
        Right{} -> pure ()
        Left{}  -> assertFailure "Expected an interpretation of the unused uncurried function"
  , testCase "function first used in a query" $ do
      let f = uninterpret "discovery.used" :: SInteger -> SInteger
      result <- runSMTWith cfg $ query $ do
        constrain $ f 5 .== 17
        ensureSat
        getFunction f
      case result of
        Right (table, def) -> fromMaybe def (lookup 5 table) == 17 @? "The interpretation must satisfy the constraint"
        Left{}            -> assertFailure "Expected a value association for the constrained function"
  , testGroup "quoted names"
      [ testCase nm $ withSystemTempDirectory "sbv-quoted-function" $ \dir -> do
          let logFile = dir </> "solver.smt2"
              f = uninterpret nm :: SInteger -> SInteger
          result <- runSMTWith cfg{transcript = Just logFile} $ do
            constrain $ f 5 .== 17
            query $ ensureSat >> getFunction f
          case result of
            Right (table, def) -> fromMaybe def (lookup 5 table) == 17 @? "The quoted function must satisfy its constraint"
            Left{}            -> assertFailure "Expected a value association for the quoted function"
          logText <- readFile logFile
          ("(get-value (" ++ nm ++ "))") `isInfixOf` logText @? "Expected an explicitly quoted function lookup"
      | nm <- ["|quotedFunction|", "|function with spaces|"]
      ]
  , testGroup "quoted names in models"
      [ testCase (nm ++ if constrained then " constrained" else " unused") $ do
          let f = uninterpret nm :: SInteger -> SInteger
          model <- runSMTWith cfg $ do
            if constrained then constrain $ f 5 .== 17 else registerFunction f
            query $ ensureSat >> getModel
          case modelUIFuns model of
            [(modelName, (_, _, Right (table, def)))] -> do
              modelName == filter (/= '|') nm @? "Expected the quoted function in the model"
              when constrained $ do
                let values = [(map (fromCV @Integer) args, fromCV @Integer value) | (args, value) <- table]
                fromMaybe (fromCV @Integer def) (lookup [5] values) == 17 @? "The model interpretation must satisfy the constraint"
            other -> assertFailure $ "Expected a function interpretation in the model, received: " ++ show other
      | nm <- ["|quotedFunction|", "|function with spaces|"], constrained <- [False, True]
      ]
  , testCase "discovery preserves the current model" $
      withSystemTempDirectory "sbv-discovery" $ \dir -> do
        let logFile = dir </> "solver.smt2"
            f = uninterpret "discovery.binary" :: SBool -> SBool -> SBool
        runSMTWith cfg{transcript = Just logFile} $ do
          x <- sBool "x"
          registerFunction f
          query $ do
            cs <- checkSatAssuming [x]
            io $ cs == Sat @? "Expected satisfiable assumptions"
            before <- getValue x
            _ <- getFunction f
            _ <- getFunction f
            after <- getValue x
            io $ before && after @? "Function discovery must preserve the assumed model"
        logText <- readFile logFile
        let commands = filter ("(" `isPrefixOf`) $ lines logText
            afterCheck = drop 1 $ dropWhile (not . ("(check-sat" `isPrefixOf`)) commands
        length (filter ("(check-sat-assuming" `isPrefixOf`) commands) == 1
          @? "Expected exactly one check with assumptions in the transcript"
        all (\cmd -> not $ any (`isPrefixOf` cmd) ["(declare-", "(define-", "(assert", "(check-sat"]) afterCheck
          @? "Model inspection must not emit declarations, assertions, or another satisfiability check"
  , testCase "failed discovery leaves the query usable" $ do
      let f = uninterpret "discovery.missing" :: SInteger -> SInteger
          wrongType = uninterpret "discovery.existing" :: SBool -> SBool
          existing  = uninterpret "discovery.existing" :: SInteger -> SInteger
      runSMTWith cfg $ do
        x <- sBool "x"
        registerFunction existing
        query $ do
          cs <- checkSatAssuming [x]
          io $ cs == Sat @? "Expected satisfiable assumptions"
          expectQueryError "is not registered in this context" $ getFunction f
          expectQueryError "used at incompatible SMT signatures" $ getFunction wrongType
          expectQueryError "Must be called on an uninterpreted function" $ getFunction ((+1) :: SInteger -> SInteger)
          value <- getValue x
          io $ value @? "Failed discovery must preserve the assumed model"
          -- A failed lookup must not poison the registry and prevent a later
          -- ordinary use from declaring the function to the solver.
          constrain $ f 0 .== 42
          ensureSat
          result <- getValue (f 0)
          io $ result == 42 @? "The function must remain usable after failed discovery"
  ]

-- | CVC5 needs first-order ALL (rather than SBV's default HO_ALL) and macro
-- expansion to produce models of these quantified function definitions.
setupFunctionModels :: String -> Symbolic ()
setupFunctionModels solverName = when (solverName == "cvc5") $ do
  setLogic $ CustomLogic "ALL"
  setOption $ OptionKeyword ":macros-quant" ["true"]
  setOption $ OptionKeyword ":macros-quant-mode" ["all"]

-- | Assert the positive raw fallback exactly, including whitespace and literal
-- spelling. Let-wrapped lambdas and as-array values bypass lambda formatting.
fallbackTests :: TestTree
fallbackTests = testGroup "raw function rendering"
  [ testGroup quotingCase
      [ testCase bodyName $ do
          let response = " \n ( ( " ++ actual ++ " ; before value )\n " ++ body ++ " ) ; after value\n ) \n"
          case parseSExpr response of
            Right (EApp [EApp [ECon _, value]]) -> do
              let rendered = formatFunctionResponse value response wanted True Nothing
              rendered == wanted ++ " = fromSMTLib " ++ body @? "Raw fallback changed the function value: " ++ show rendered
            other -> assertFailure $ "Expected a function response, received: " ++ show other
      | (bodyName, body) <-
          [ ("as-array", "(_ as-array helper)")
          , ("let-wrapped lambda", "(let ((offset 3))\n  (lambda ((x!1 Int)) (+ offset (* 2 x!1))))")
          , ("comments and spacing", "(let  ((offset 3)) ; keep this ) comment\n\t(lambda ((x!1 Int))  (+ offset x!1)))")
          , ("quoted literals", "(let ((|text )| \"he said \"\"hi\"\"; )))\")) (lambda ((x String)) |text )|))")
          , ("bit-vector spelling", "(let ((mask #x0f) (wide (_ bv7 16))) (lambda ((x (_ BitVec 8))) (bvand x mask)))")
          ]
      ]
  | (quotingCase, wanted, actual) <-
      [ ("unquoted",        "f",                  "f")
      , ("solver unquotes", "|f|",                "f")
      , ("solver quotes",   "f",                  "|f|")
      , ("quoted",          "|f|",                "|f|")
      , ("spaces in name",  "|name with spaces|", "|name with spaces|")
      ]
  ]

-- | Catch an error inside the same query so subsequent solver interactions
-- verify that discovery has not corrupted either side of the connection.
expectQueryError :: String -> Query a -> Query ()
expectQueryError expected (QueryT action) = QueryT $ ReaderT $ \st -> do
  result <- C.try $ runReaderT action st
  case result of
    Left (err :: C.ErrorCall) -> expected `isInfixOf` C.displayException err @? "Unexpected diagnostic: " ++ C.displayException err
    Right _                  -> assertFailure $ "Expected diagnostic containing: " ++ expected

-- | Exercise both rational equality helpers, repeated declarations, named and
-- unnamed fresh variables, and declarations surviving assertion-stack changes.
rationalTest :: String -> Bool -> Bool -> TestTree
rationalTest testName before inside = testCase testName $ do
  result <- runSMT $ do
    when before $ registerType (Proxy @Rational)
    query $ do
      when inside $ do registerType (Proxy @Rational)
                       registerType (Proxy @Rational)
      push 1
      x <- freshVar @Rational "x"
      constrain $ x .== 1/2
      first <- getValue x
      pop 1
      y <- freshVar_ @Rational
      constrain $ y .== 1/3
      constrain $ y ./= 0
      later <- getValue y
      pure (first, later)
  result == (1 % 2, 1 % 3) @? "Expected rational values across incremental contexts, received: " ++ show result
