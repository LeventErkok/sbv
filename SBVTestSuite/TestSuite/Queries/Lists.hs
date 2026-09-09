-----------------------------------------------------------------------------
-- |
-- Module    : TestSuite.Queries.Lists
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Testing a few lists
-----------------------------------------------------------------------------

{-# LANGUAGE OverloadedLists     #-}
{-# LANGUAGE QuasiQuotes         #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications    #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module TestSuite.Queries.Lists (tests)  where

import Data.SBV
import Data.SBV.Control
import qualified Data.SBV.List as L
import qualified Data.SBV.Tuple as T

import Data.List (isInfixOf)

import qualified Control.Exception as C

import Utils.SBVTestFramework

-- | Test suite.
tests :: TestTree
tests =
  testGroup "Basics.QueryLists"
    [ goldenCapturedIO "query_Lists1" $ testQuery queryLists1
    , testCase "query_Lists2"              $ do result <- runSMT queryLists2
                                                result == 3 @? "Expected the filtered value 3, received: " ++ show result
    , testCase "query_function_dependency" $ do result <- runSMT queryFunctionDependency
                                                result == 11 @? "Expected the dependent function value 11, received: " ++ show result
    , testCase "query_function_reuse"      $ do result <- runSMT queryFunctionReuse
                                                result == (6, 7) @? "Expected the reused function values (6, 7), received: " ++ show result
    , testCase "query_function_body_kind"  $ do result <- runSMT queryFunctionBodyKind
                                                result == 11 @? "Expected the tuple-backed function value 11, received: " ++ show result
    , testCase "query_function_ui"         $ do result <- runSMT queryFunctionUI
                                                result == 11 @? "Expected the helper-backed function value 11, received: " ++ show result
    , testCase "query_mutual_functions"    $ do result <- runSMT queryMutualFunctions
                                                result @? "Expected the mutually recursive function to return true"
    , testCase "query_bad_termination"     $ do result <- C.try (runSMT queryBadTermination)
                                                case result of
                                                  Left (e :: C.SomeException) -> "does not strictly decrease" `isInfixOf` show e
                                                                                 @? "Expected a termination-check failure, received: " ++ show e
                                                  Right value                 -> assertFailure $ "Expected a termination-check failure, received: " ++ show value
    ]

-- | Run a query with its verbose transcript redirected to the given file.
testQuery :: Show a => Symbolic a -> FilePath -> IO ()
testQuery t rf = do r <- runSMTWith defaultSMTCfg{verbose=True, redirectVerbose=Just rf} t
                    appendFile rf ("\nFINAL OUTPUT:\n" ++ show r ++ "\n")

-- | Retrieve a concrete list from a solver query.
queryLists1 :: Symbolic [Integer]
queryLists1 = do a :: SList Integer <- sList "a"

                 constrain $ a .== [sEnum|1..5|]

                 query $ do _ <- checkSat

                            av <- getValue a

                            if av == [1..5]
                               then return av
                               else error $ "Didn't expect this: " ++ show av

-- | Exercise an SMT function first encountered after entering query mode.
queryLists2 :: Symbolic Integer
queryLists2 = query $ do x <- freshVar @Integer "x"
                         y <- freshVar @[Integer] "y"
                         constrain $ y .== literal [1 .. 20]
                         constrain $ x .== L.head (L.filter (.== literal 3) y)
                         getValue x

-- | Exercise dependency ordering between SMT functions first encountered in query mode.
queryFunctionDependency :: Symbolic Integer
queryFunctionDependency = query $ do n <- freshVar @Integer "n"
                                     x <- freshVar @Integer "x"
                                     constrain $ n .== 5
                                     constrain $ x .== outer n
                                     getValue x
  where inner :: SInteger -> SInteger
        inner = smtFunction "query.inner" (* 2)

        outer :: SInteger -> SInteger
        outer = smtFunction "query.outer" ((+ 1) . inner)

-- | Exercise repeated use of an SMT function after its query-mode definition has been sent.
queryFunctionReuse :: Symbolic (Integer, Integer)
queryFunctionReuse = query $ do n <- freshVar @Integer "n"
                                x <- freshVar @Integer "x"
                                y <- freshVar @Integer "y"
                                constrain $ n .== 5
                                constrain $ x .== increment n
                                constrain $ y .== increment x
                                (,) <$> getValue x <*> getValue y
  where increment :: SInteger -> SInteger
        increment = smtFunction "query.increment" (+ 1)

-- | Exercise a datatype used only inside an SMT function first encountered in query mode.
queryFunctionBodyKind :: Symbolic Integer
queryFunctionBodyKind = query $ do n <- freshVar @Integer "n"
                                   x <- freshVar @Integer "x"
                                   constrain $ n .== 5
                                   constrain $ x .== pairSum n
                                   getValue x
  where pairSum :: SInteger -> SInteger
        pairSum = smtFunction "query.pairSum" $ \n -> let p :: STuple Integer Integer
                                                          p = T.tuple (n, n + 1)
                                                      in T.fst p + T.snd p

-- | Exercise an uninterpreted helper used by an SMT function first encountered in query mode.
queryFunctionUI :: Symbolic Integer
queryFunctionUI = query $ do n <- freshVar @Integer "n"
                             x <- freshVar @Integer "x"
                             constrain $ n .== 5
                             constrain $ x .== applyHelper n
                             constrain $ helper n .== 10
                             getValue x
  where helper :: SInteger -> SInteger
        helper = uninterpret "query.helper"

        applyHelper :: SInteger -> SInteger
        applyHelper = smtFunction "query.applyHelper" ((+ 1) . helper)

-- | Exercise mutually recursive SMT functions first encountered in query mode.
queryMutualFunctions :: Symbolic Bool
queryMutualFunctions = query $ do n <- freshVar @Bool "n"
                                  x <- freshVar @Bool "x"
                                  constrain n
                                  constrain $ x .== isEven n
                                  getValue x
  where isEven :: SBool -> SBool
        isEven = smtFunctionNoTermination "query.even" $ \b -> ite b (isOdd sFalse) sFalse

        isOdd :: SBool -> SBool
        isOdd  = smtFunctionNoTermination "query.odd" $ \b -> ite b (isEven sFalse) sTrue

-- | Ensure query-mode definitions still undergo termination checking before reaching the solver.
queryBadTermination :: Symbolic Integer
queryBadTermination = query $ do n <- freshVar @Integer "n"
                                 x <- freshVar @Integer "x"
                                 constrain $ n .== 5
                                 constrain $ x .== diverges n
                                 getValue x
  where diverges :: SInteger -> SInteger
        diverges = smtFunctionWithMeasure "query.diverges" (abs, []) $ \n -> ite (n .<= 0) 0 (diverges (n + 1))
