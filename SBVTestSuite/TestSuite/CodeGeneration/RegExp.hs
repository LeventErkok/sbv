-----------------------------------------------------------------------------
-- |
-- Module    : TestSuite.CodeGeneration.RegExp
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Execute bounded, dependency-free C regex automata against solver results.
-----------------------------------------------------------------------------

{-# LANGUAGE OverloadedStrings #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module TestSuite.CodeGeneration.RegExp (tests) where

import Control.Exception (ErrorCall, displayException, evaluate, try)
import Control.Monad (forM, forM_, replicateM, void)
import Data.Char (ord)
import Data.List (intercalate, isInfixOf, nub)
import System.Directory (listDirectory)
import System.Environment (lookupEnv)
import System.Exit (ExitCode(..))
import System.FilePath ((</>))
import System.IO.Temp (withSystemTempDirectory)
import System.Process (readProcessWithExitCode)
import Test.Tasty.HUnit (assertBool, assertEqual)

import Data.SBV.Control
import Data.SBV.Internals (compileToC', compileToCLib', renderCgPgmBundle)
import Data.SBV.Tools.CodeGen
import qualified Data.SBV.List as SL
import qualified Data.SBV.RegExp as R
import Utils.SBVTestFramework

-- | Full-operator matching, language comparisons, scope integration, and
-- generation budgets, including absence of overhead for non-regex code.
tests :: TestTree
tests = testGroup "CodeGeneration.RegExp"
  [ testCase "regex membership agrees with Z3 and literal folding" membershipAgreement
  , testCase "regex language equality and inequality" languageAgreement
  , testCase "regex definitions and escaping array lambdas in a library" regexLibrary
  , testCase "regex generation limits fail before writing" regexLimits
  , testCase "default regex budgets accommodate ordinary bounded repetitions" calibratedRegexLimits
  , testCase "regex limits apply to comparisons, definitions, and library components" regexLimitScopes
  , testCase "regex character matching and dynamic tables" regexCharacterTable
  , testCase "regex state limits do not bound input length" longRegexInput
  , testCase "non-regex and dead-regex code require no regex support" noRegexOverhead
  ]

-- | Shared syntax and balanced-map lookup must not be charged as repeated
-- whole-tree copies and linear scans of the entire state set.
calibratedRegexLimits :: Assertion
calibratedRegexLimits = do
  mapM_ generate [R.Loop 0 30 "a", R.Power 510 "a"]
  result <- try (generate (R.Power 1023 "a")) :: IO (Either ErrorCall ())
  case result of
    Left err -> assertBool (displayException err) ("state limit (1024)" `isInfixOf` displayException err)
    Right () -> assertFailure "Expected the default state cap to reject 1025 states"
 where generate regex = do
         (_, _, bundle) <- compileToC' "calibratedRegex" $ do
           cgGenerateDriver False
           input <- cgInput "input" :: SBVCodeGen SString
           cgReturn (input `R.match` regex)
         void $ evaluate (length (show bundle))
         assertBool "Default-sized automata use compact transition entries"
           (any (\line -> "static const uint16_t sbv_regex_" `isInfixOf` line && "_step" `isInfixOf` line) (lines (show bundle)))

-- | Ordinary and Boolean operators, empty languages/concatenations, and
-- nullable repetitions; include boundaries of every supported encoding width.
regexes :: [R.RegExp]
regexes = nub $ atoms
            ++ [op r | op <- [R.Comp, R.KStar, R.KPlus, R.Opt, R.Loop 0 2, R.Power 2], r <- atoms]
            ++ [op a b | op <- [R.Inter, R.Diff, \a b -> R.Union [a, b], \a b -> R.Conc [a, b]], a <- atoms, b <- atoms]
            ++ [ R.Conc [R.Inter "a" "ab", R.All]
               , R.Conc [R.Diff "ab" "a", R.Opt "b"]
               , R.Conc [R.Comp "a", "b"]
               , R.KStar (R.Inter (R.Opt "a") (R.Comp "b"))
               , R.KStar (R.Comp "a")
               , R.Loop 2 3 (R.Opt "a")
               , R.Conc [R.All, "b"]
               , R.Range '\0' '\x2ffff'
               , R.Range '\xd800' '\xdfff'
               , R.Range '\x7f' '\x800'
               , R.Literal "\0\955\xd800\x2ffff"
               ]
 where atoms = [R.All, R.AllChar, R.None, R.Conc [], "a", "ab", R.Range 'a' 'b', R.Range 'b' 'a']

-- | Query a genuinely symbolic string for each sample, then feed the same
-- code points to compiled C. Literal folding is checked as a third evaluator.
membershipAgreement :: Assertion
membershipAgreement = withSystemTempDirectory "sbv-c-regex-agreement" $ \dir -> do
  expected <- runSMT $ do
    input <- sString "input"
    query $ forM samples $ \sample -> inNewAssertionStack $ do
      constrain (input .== literal sample)
      status <- checkSat
      case status of
        Sat -> getValue (SL.implode [input `R.match` r | r <- regexes])
        _   -> error $ "Unexpected regex reference status: " ++ show status
  forM_ (zip samples expected) $ \(sample, values) ->
    assertEqual ("Literal regex agreement: " ++ show sample) (map Just values)
                [unliteral (literal sample `R.match` r) | r <- regexes]
  let program = do
        cgGenerateDriver False
        cgAddDecl (membershipHarness "regexMembership" samples (length regexes))
        input <- cgInput "input" :: SBVCodeGen SString
        cgOutputArr "matches" [input `R.match` r | r <- regexes]
  (_, cfg, bundle) <- compileToC' "regexMembership" program
  renderCgPgmBundle (Just dir) (cfg, bundle)
  actual <- runC dir ["regexMembership"]
  assertEqual "C automata agree with Z3 for every regex/sample" (map (map bitChar) expected) (lines actual)
 where samples = nub $ concatMap (`replicateM` "ab") [0 .. 3]
                    ++ ["\0", "\955", "\x7f", "\x80", "\x7ff", "\x800", "\xd800", "\xdfff", "\xffff", "\x10000", "\x2ffff"
                       , "\0\955\xd800\x2ffff", "\955b", "a\0"]
       bitChar True  = '1'
       bitChar False = '0'

-- | Build strings from numeric code points instead of relying on C source
-- encoding or NUL termination. Every sample shares one generated matcher.
membershipHarness :: String -> [String] -> Int -> [String]
membershipHarness function samples count =
  [ "int main(void) {"
  , "  uint8_t bytes[" ++ show (max 1 (4 * maximum (map length samples))) ++ "];"
  , "  SBool matches[" ++ show count ++ "];"
  ] ++ concatMap sampleBlock samples ++ ["  return 0;", "}"]
 where sampleBlock sample =
         [ "  {"
         , "    const SChar points[] = {" ++ intercalate ", " (map (show . ord) sample ++ ["0"]) ++ "};"
         , "    size_t size = 0;"
         , "    for (size_t i = 1; i < sizeof(points) / sizeof(points[0]); ++i) size += sbv_char_encode(points[i - 1], bytes + size);"
         , "    " ++ function ++ "(sbv_string_borrow(bytes, size, sizeof(points) / sizeof(points[0]) - 1), matches);"
         , "    for (size_t i = 0; i < " ++ show count ++ "; ++i) putchar(matches[i] ? '1' : '0');"
         , "    putchar('\\n');"
         , "  }"
         ]

-- | Decide language equality at generation time, including equality expressed
-- by structurally different regexes and languages distinguished only by epsilon.
languageAgreement :: Assertion
languageAgreement = withSystemTempDirectory "sbv-c-regex-languages" $ \dir -> do
  expected <- runSMT $ query $ do
    status <- checkSat
    case status of
      Sat -> mapM (\(a, b) -> getValue (a .== b)) pairs
      _   -> error $ "Unexpected regex reference status: " ++ show status
  let program = do
        cgGenerateDriver False
        cgAddDecl ["int main(void) { SBool values[" ++ show (2 * length pairs) ++ "]; regexLanguages(values);"
                  , "for (size_t i = 0; i < " ++ show (2 * length pairs) ++ "; ++i) putchar(values[i] ? '1' : '0'); return 0; }"]
        cgOutputArr "values" (concat [[a .== b, a ./= b] | (a, b) <- pairs])
  (_, cfg, bundle) <- compileToC' "regexLanguages" program
  renderCgPgmBundle (Just dir) (cfg, bundle)
  actual <- runC dir ["regexLanguages"]
  assertEqual "Exact language comparisons" (concatMap (\equal -> if equal then "10" else "01") expected) actual
  source <- readFile (dir </> "regexLanguages.c")
  assertBool "Language comparisons need no runtime regex tables" (not ("sbv_regex_" `isInfixOf` source))
 where pairs = [ (R.Conc [], "")
               , (R.Union [], R.None)
               , (R.Comp R.None, R.All)
               , (R.Inter (R.Comp "a") (R.Comp "b"), R.Comp (R.Union ["a", "b"]))
               , (R.Diff R.All "a", R.Comp "a")
               , (R.KPlus "a", R.Conc ["a", R.KStar "a"])
               , (R.KStar (R.Opt "a"), R.KStar "a")
               , (R.Loop 0 0 "a", R.Conc [])
               , (R.Range '\0' '\x2ffff', R.AllChar)
               , (R.All, R.AllChar)
               , (R.KStar "a", R.KPlus "a")
               , (R.Power 3 "a", R.Loop 2 3 "a")
               , (R.Range 'a' 'b', R.Range 'a' 'c')
               ]

-- | Library components may use independent budgets, and regex tables remain
-- private even when definitions and escaping closed lambdas reuse node IDs.
regexLibrary :: Assertion
regexLibrary = withSystemTempDirectory "sbv-c-regex-library" $ \dir -> do
  let matcher = smtFunction "regex in a defined function" (\value -> value `R.match` R.Conc [R.All, "b"])
      component = do
        cgGenerateDriver False
        let array = lambdaArray matcher :: SArray String Bool
        cgReturn array
      direct = do
        cgGenerateDriver False
        input <- cgInput "input" :: SBVCodeGen SString
        cgReturn (matcher input)
      plain = do
        cgGenerateDriver False
        cgRegexLimits 0 0 0
        cgAddDecl ["int main(void) {"
                  , "  SBVArrayOutput_6_string_2_u1 array = regexClosure();"
                  , "  const SString ab = sbv_string_borrow_utf8(\"ab\"), a = sbv_string_borrow_utf8(\"a\");"
                  , "  const int ok = array.lookup(array.context, ab) && !array.lookup(array.context, a) && regexDirect(ab) && !regexDirect(a) && plainComponent();"
                  , "  sbv_array_output_release_6_string_2_u1(&array);"
                  , "  return ok ? 0 : 1;"
                  , "}"]
        cgReturn sTrue
  (_, cfg, bundle) <- compileToCLib' "regexLibrary" [("regexClosure", component), ("regexDirect", direct), ("plainComponent", plain)]
  renderCgPgmBundle (Just dir) (cfg, bundle)
  void $ runC dir ["regexClosure", "regexDirect", "plainComponent"]
  source <- readFile (dir </> "plainComponent.c")
  assertBool "Non-regex library component has no regex implementation" (not ("sbv_regex_" `isInfixOf` source))

-- | Exercise each independent budget and verify rejection precedes file
-- creation. Large repetition counts must fail without expanding them first.
regexLimits :: Assertion
regexLimits = do
  rejects "state" (cgRegexLimits 2 100 10000) "a"
  rejects "expression-node" (cgRegexLimits 100 4 10000) "abcdef"
  rejects "work" (cgRegexLimits 100 100 1) "a"
  rejects "disabled" (cgRegexLimits 0 100 10000) "a"
  rejects "expression-node" (pure ()) (R.Power maxBound "a")
  rejects "expression-node" (pure ()) (R.Loop 0 maxBound "a")
  rejects "state" (cgRegexLimits 8 4096 1000000) (R.Conc [R.All, "a", R.Power 8 R.AllChar])
  withSystemTempDirectory "sbv-c-regex-raised-limit" $ \dir -> do
    (_, cfg, bundle) <- compileToC' "raisedRegex" $ do
      cgRegexLimits 3 100 10000
      cgGenerateDriver False
      cgAddDecl ["int main(void) { return raisedRegex(sbv_string_borrow_utf8(\"a\")) ? 0 : 1; }"]
      input <- cgInput "input" :: SBVCodeGen SString
      cgReturn (input `R.match` R.Literal "a")
    renderCgPgmBundle (Just dir) (cfg, bundle)
    void $ runC dir ["raisedRegex"]
 where rejects :: String -> SBVCodeGen () -> R.RegExp -> Assertion
       rejects diagnostic limits regex = withSystemTempDirectory "sbv-c-regex-limit" $ \dir -> do
         result <- try (compileToC (Just dir) "limitedRegex" $ do
                     limits
                     input <- cgInput "input" :: SBVCodeGen SString
                     cgReturn (input `R.match` regex)) :: IO (Either ErrorCall ())
         case result of
           Left err -> assertBool (displayException err) (diagnostic `isInfixOf` displayException err && "cgRegexLimits" `isInfixOf` displayException err)
           Right () -> assertFailure "Expected regex budget rejection"
         assertEqual "Rejected regex must not create files" [] =<< listDirectory dir

-- | Successful bounded generation accepts strings far longer than any budget
-- dimension. The runtime matcher uses neither recursion nor heap allocation.
longRegexInput :: Assertion
longRegexInput = withSystemTempDirectory "sbv-c-regex-long-input" $ \dir -> do
  (_, cfg, bundle) <- compileToC' "longRegex" $ do
    cgRegexLimits 2 16 1000
    cgGenerateDriver False
    cgAddDecl ["int main(void) { uint8_t bytes[100000]; memset(bytes, 'a', sizeof bytes);"
              , "return longRegex(sbv_string_borrow(bytes, sizeof bytes, sizeof bytes)) ? 0 : 1; }"]
    input <- cgInput "input" :: SBVCodeGen SString
    cgReturn (input `R.match` R.KStar "a")
  renderCgPgmBundle (Just dir) (cfg, bundle)
  void $ runC dir ["longRegex"]

-- | Apply budgets to every lowering scope, not just entry-point membership.
-- Library preflight must not leave files from an earlier successful component.
regexLimitScopes :: Assertion
regexLimitScopes = do
  forM_ [(-1, 100, 10000), (100, -1, 10000), (100, 100, -1)] $ \(states, nodes, work) ->
    rejects "nonnegative" (cgRegexLimits states nodes work >> cgReturn sTrue)
  rejects "state" $ do
    cgRegexLimits 2 100 10000
    cgReturn (R.Literal "a" .== R.Literal "a")
  rejects "state" $ do
    cgRegexLimits 2 100 10000
    input <- cgInput "input" :: SBVCodeGen SString
    cgReturn (smtFunction "limited regex definition" (\s -> s `R.match` R.Literal "a") input)
  rejects "state" $ do
    cgRegexLimits 2 100 10000
    cgReturn (lambdaArray (\s -> s `R.match` R.Literal "a") :: SArray String Bool)
  rejects "domain" $ do
    input <- cgInput "input" :: SBVCodeGen SString
    cgReturn (input `R.match` R.Literal "\x30000")
  withSystemTempDirectory "sbv-c-regex-library-limit" $ \dir -> do
    let plain = cgGenerateDriver False >> cgRegexLimits 0 0 0 >> cgReturn sTrue
        limited = do cgGenerateDriver False
                     cgRegexLimits 2 100 10000
                     input <- cgInput "input" :: SBVCodeGen SString
                     cgReturn (input `R.match` R.Literal "a")
    result <- try (compileToCLib (Just dir) "limitedLibrary" [("plain", plain), ("limited", limited)]) :: IO (Either ErrorCall [()])
    case result of
      Left err -> assertBool (displayException err) ("state" `isInfixOf` displayException err)
      Right _  -> assertFailure "Expected library regex budget rejection"
    assertEqual "Library budget failure must not write any component" [] =<< listDirectory dir
 where rejects :: String -> SBVCodeGen () -> Assertion
       rejects diagnostic program = withSystemTempDirectory "sbv-c-regex-scoped-limit" $ \dir -> do
         result <- try (compileToC (Just dir) "scopedLimit" program) :: IO (Either ErrorCall ())
         case result of
           Left err -> assertBool (displayException err) (diagnostic `isInfixOf` displayException err)
           Right () -> assertFailure "Expected scoped regex budget rejection"
         assertEqual "Scoped budget failure must not write files" [] =<< listDirectory dir

-- | Character membership uses the existing singleton-string lowering. Regex
-- computations in a dynamic lookup table keep their function-local tables and
-- setup statements correctly scoped under demand-driven selection.
regexCharacterTable :: Assertion
regexCharacterTable = withSystemTempDirectory "sbv-c-regex-character-table" $ \dir -> do
  (_, cfg, bundle) <- compileToC' "regexCharacterTable" $ do
    cgGenerateDriver False
    cgPerformRTCs True
    cgAddDecl ["int main(void) {"
              , "  return regexCharacterTable(0xd800, 0) && !regexCharacterTable('a', 0)"
              , "      && regexCharacterTable('a', 1) && !regexCharacterTable('b', 1)"
              , "      && regexCharacterTable('b', 2) && !regexCharacterTable('a', 2)"
              , "      && !regexCharacterTable('a', 255) ? 0 : 1;"
              , "}"]
    input <- cgInput "input" :: SBVCodeGen SChar
    index <- cgInput "index" :: SBVCodeGen SWord8
    cgReturn $ select [input `R.match` r | r <- [R.Range '\xd800' '\xdfff', "a", R.Comp "a"]] sFalse index
  renderCgPgmBundle (Just dir) (cfg, bundle)
  void $ runC dir ["regexCharacterTable"]

-- | Disabled regex compilation leaves non-regex generation unchanged and
-- never examines a dead regex operation, including when regex compilation is disabled.
noRegexOverhead :: Assertion
noRegexOverhead = do
  baseline <- generated (pure ()) False
  disabled <- generated (cgRegexLimits 0 0 0) False
  assertEqual "Regex budgets do not alter non-regex C" baseline disabled
  dead <- generated (cgRegexLimits 0 0 0) True
  assertBool "Dead regex has no runtime code" (not ("sbv_regex_" `isInfixOf` dead))
 where generated :: SBVCodeGen () -> Bool -> IO String
       generated limits useDead = do
         (_, _, bundle) <- compileToC' "noRegex" $ do
           limits
           cgGenerateDriver False
           cgSetDriverValues [1]
           input <- cgInput "input" :: SBVCodeGen SBool
           if useDead
             then do string <- cgInput "string" :: SBVCodeGen SString
                     cgReturn (ite sTrue input (string `R.match` R.Power 100 "a"))
             else cgReturn input
         let source = show bundle
         void $ evaluate (length source)
         pure source

-- | Compile generated translation units with strict C warnings and optional
-- sanitizer flags. Regex support must need no nonstandard library or header.
runC :: FilePath -> [String] -> IO String
runC dir components = do
  flags <- maybe [] words <$> lookupEnv "SBV_C_TEST_FLAGS"
  let executablePath = dir </> "regex-test"
  (status, _, errors) <- readProcessWithExitCode "cc" (["-std=c11", "-Wall", "-Wextra", "-Werror", "-O2"] ++ flags
                                                 ++ [dir </> component ++ ".c" | component <- components]
                                                 ++ ["-o", executablePath]) ""
  assertEqual errors ExitSuccess status
  (runStatus, outputText, runError) <- readProcessWithExitCode executablePath [] ""
  assertEqual runError ExitSuccess runStatus
  pure outputText
