-----------------------------------------------------------------------------
-- |
-- Module    : TestSuite.Basics.ModelValidate
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Few validate tests
-----------------------------------------------------------------------------

{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE FlexibleInstances   #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell     #-}
{-# LANGUAGE TypeApplications    #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module TestSuite.Basics.ModelValidate (testsABC, tests)  where

import qualified Control.Exception as C
import Data.List (isPrefixOf, isInfixOf)

import qualified Data.Set as Set

import qualified Data.SBV.List  as L
import qualified Data.SBV.Maybe as M
import qualified Data.SBV.Set   as S

import Data.SBV.Tools.Overflow

import Test.Tasty.HUnit (assertBool)

import Utils.SBVTestFramework

data T = Leaf | Node T Integer T deriving Show
mkSymbolic [''T]

data U
mkSymbolic [''U]

-- Nested recursive call, used to make sure termination checks don't trip validation
ack :: SInteger -> SInteger -> SInteger
ack = smtFunction "ack" $ \m n -> ite (m .<= 0) (n + 1) (ite (n .<= 0) (ack (m - 1) 1) (ack (m - 1) (ack m (n - 1))))

cnt :: SInteger -> SInteger
cnt = smtFunction "cnt" $ \n -> ite (n .<= 0) 0 (1 + cnt (n - 1))

-- Test suite, this needs ABC
testsABC :: TestTree
testsABC = testGroup "Basics.ModelValidate.ABC" [
             goldenCapturedIO "validate_0" testABC
           ]
    where testABC goldFile = do r <- satWith abc{verbose=True, redirectVerbose = Just goldFile, validateModel = True} (free "x" >>= \x -> pure $ x .< (10::SWord8))
                                appendFile goldFile ("\nFINAL OUTPUT:\n" ++ show r ++ "\n")

tests :: TestTree
tests = testGroup "Basics.ModelValidate" $ [
             goldenCapturedIO "validate_1" $ t  satWith    t1
           , goldenCapturedIO "validate_2" $ t  satWith    t2
           , goldenCapturedIO "validate_3" $ t  satWith    t3
           , goldenCapturedIO "validate_4" $ t  proveWith  t3
           , goldenCapturedIO "validate_5" $ t  satWith    t4
           , goldenCapturedIO "validate_6" $ t  proveWith  t4
           , goldenCapturedIO "validate_7" $ tE satWith    t5
           , testCase         "validate_8" t6
           ]
           ++ [testCase ("validate_ok_"   ++ n) (validates   p) | (n, p) <- okSat]
           ++ [testCase ("validate_cex_"  ++ n) (validatesP  p) | (n, p) <- okCex]
           ++ [testCase ("validate_cant_" ++ n) (cantValidate msg p) | (n, msg, p) <- cant]
           ++ [ testCase "validate_allSat_ui" $ validatesAll $ \(x :: SInteger) -> (uninterpret "g" :: SInteger -> SInteger) x .== 3 .&& x .>= 0
              , testCase "validate_nonModelVar_ui" $ do
                  r <- satWith z3{validateModel = True, isNonModelVar = (== "q")} $ \(x :: SInteger) -> (uninterpret "q" :: SInteger -> SInteger) x .== 3
                  checkSat (show r) r
              ]
           ++ [testCase ("validate_fp_concrete_"  ++ n) a | (n, a) <- fpConcrete]
           ++ [testCase ("validate_ovf_concrete_" ++ n) a | (n, a) <- ovfConcrete]
           ++ [testCase ("validate_set_concrete_" ++ n) (assertBool n b) | (n, b) <- setConcrete]
           ++ [testCase ("validate_arr_concrete_" ++ n) (assertBool n b) | (n, b) <- arrConcrete]
    where t f test goldFile = do r <- f defaultSMTCfg{verbose=True, redirectVerbose = Just goldFile, validateModel = True} test
                                 appendFile goldFile ("\nFINAL OUTPUT:\n" ++ show r ++ "\n")

          tE f test goldFile = do r <- f defaultSMTCfg{verbose=True, redirectVerbose = Just goldFile, validateModel = True} test
                                  appendFile goldFile ("\nFINAL OUTPUT:\n" ++ show r ++ "\n")
                               `C.catch` (\(e::C.SomeException) -> appendFile goldFile ("\nEXCEPTION RAISED:\n" ++ pick (show e) ++ "\n"))
              where pick s = unlines [l | l <- lines s, "***" `isPrefixOf` l]

          t1, t2 :: Predicate
          t1 = free "x" >>= \x -> pure $ fpAdd sRTZ x x   .== (x::SFloat)
          t2 = free "x" >>= \x -> pure $ fpFMA sRNE x x x .== (x::SFloat)

          t3 :: Predicate
          t3 = do x <- sInteger "x"
                  constrain $ x .> x   -- Constraining with False! i.e., any theorem will follow, and will be trivially unsat
                  pure sFalse

          t4 :: Predicate
          t4 = do x <- sInteger "x"
                  y <- sInteger "y"
                  constrain $ x .> y
                  constrain $ x .> 12
                  return $ x .== y+3

          t5 :: Predicate
          t5 = do x <- free "x"
                  pure $ quantifiedBool $ \(Forall y) -> fpIsPoint y .=> x .<= (y::SFloat)

          -- Problems whose models should validate
          okSat :: [(String, Predicate)]
          okSat = [ ("usort_neq",       do u <- free "u"; v <- free "v"; pure $ (u :: SU) ./= v)
                  , ("ack",             do m <- free "m"; n <- free "n"; pure $ m .== 1 .&& n .== 2 .&& ack m n .== 4)
                  , ("ui_const",        do x <- sInteger "x"; pure $ x .== uninterpret "c" + 1)
                  , ("ui_fun",          do x <- sInteger "x"; pure $ (uninterpret "f" :: SInteger -> SInteger) x .== 3)
                  , ("ui_fun2",         do x <- sInteger "x"; y <- sInteger "y"; pure $ (uninterpret "k" :: SInteger -> SInteger -> SInteger) x y .== x + y + 1 .&& x .> y)
                  , ("ui_uncurried",    do x <- sInteger "x"; y <- sInteger "y"; pure $ (uninterpret "ku" :: (SInteger, SInteger) -> SInteger) (x, y) .== 7)
                  , ("ui_bool",         do x <- sInteger "x"; let p = uninterpret "p" :: SInteger -> SBool in pure $ p x .&& sNot (p (x + 1)))
                  , ("ui_adt_arg",      do e <- free "e"; pure $ (uninterpret "g" :: ST -> SInteger) e .== 3 .&& isNode e)
                  , ("ui_adt_res",      do x <- sInteger "x"; pure $ isNode ((uninterpret "h" :: SInteger -> ST) x) .&& x .> 2)
                  , ("ui_usort_arg",    do u <- free "u"; pure $ (uninterpret "us" :: SU -> SInteger) u .== 2)
                  , ("ui_array",        do i <- sInteger "i"; pure $ readArray (uninterpret "arr" :: SArray Integer Integer) i .== 5)
                  , ("ui_float_rtz",    pure $ fpAdd sRoundTowardZero (uninterpret "cf" :: SFloat) 1 .== 3)
                  , ("float_add_rtz",   do x <- sFloat  "x"; pure $ fpAdd sRoundTowardZero x 1 .== 3)
                  , ("float_mul_rtp",   do x <- sFloat  "x"; y <- sFloat "y"; pure $ fpMul sRoundTowardPositive x y .== 3.5 .&& x .> 1 .&& y .> 1)
                  , ("float_fma",       do x <- sFloat  "x"; pure $ fpFMA sRNE x x x .== 12)
                  , ("double_fma_rtn",  do x <- sDouble "x"; pure $ fpFMA sRoundTowardNegative x x 1 .== 5)
                  , ("fp512_rtz",       do x <- sFloatingPoint "x"; pure $ fpAdd sRoundTowardZero x 1 .== (3 :: SFloatingPoint 5 12))
                  , ("ovf_add",         do x <- sWord8 "x"; y <- sWord8 "y"; pure $ bvAddO x y)
                  , ("ovf_mul_signed",  do x <- sInt8  "x"; y <- sInt8  "y"; pure $ bvMulO x y .&& x .> 3)
                  , ("ovf_div_signed",  do x <- sInt8  "x"; y <- sInt8  "y"; pure $ bvDivO x y)
                  , ("ovf_neg_signed",  do x <- sInt8  "x"; pure $ bvNegO x)
                  , ("set_member_union",do s <- free "s"; pure $ 3 `S.member` ((s :: SSet Integer) `S.union` S.singleton 5))
                  -- Bit-wise and/or must not be short-cut like their boolean counterparts
                  , ("ui_bitwise_or",   let x = uninterpret "bw1" :: SWord8 in pure $ x .== 2 .&& (x .|. 4) .== 6)
                  , ("ui_bitwise_and",  let x = uninterpret "bw2" :: SWord8 in pure $ x .== 0 .&& (x .&. 5) .== 0)
                  -- No-op writes change the representation of an array, but not its value
                  , ("ui_fun_array_noop_write", do
                        a <- free "a"; b <- free "b"; c <- free "c"
                        let f = uninterpret "fa" :: SArray Integer Integer -> SInteger
                            noop x = writeArray x 7 (readArray x 7)
                        constrain $ distinct [a, b, c :: SArray Integer Integer]
                        pure $ sAnd [f x .== v .&& f (noop x) .== v | (x, v) <- [(a, 3), (b, 4), (c, 5)]])
                  -- Same, but the no-op write is in an inner array
                  , ("ui_fun_nested_array_noop_write", do
                        let f      = uninterpret "fn" :: SArray Integer (ArrayModel Integer Integer) -> SInteger
                            inner  = constArray 1 :: SArray Integer Integer
                            base   = constArray (constArray 0 :: SArray Integer Integer)
                        pure $ f base .== 2 .&& f (writeArray base 0 inner) .== 1 .&& f (writeArray base 0 (writeArray inner 7 1)) .== 1)
                  , ("ui_array_index_noop_write", do
                        a <- free "a"; b <- free "b"; c <- free "c"
                        let aa = uninterpret "aa" :: SArray (ArrayModel Integer Integer) Integer
                            noop x = writeArray x 7 (readArray x 7)
                        constrain $ distinct [a, b, c :: SArray Integer Integer]
                        pure $ sAnd [readArray aa x .== v .&& readArray aa (noop x) .== v | (x, v) <- [(a, 3), (b, 4), (c, 5)]])
                  , ("set_diff_mixed",  do s <- free "s"; pure $ S.complement (s :: SSet Integer) `S.difference` S.singleton 1 .== S.complement (S.fromList [1, 2]))
                  ]

          -- Proofs whose counter-examples should validate
          okCex :: [(String, Predicate)]
          okCex = [ ("ui_const", pure $ (uninterpret "cp" :: SInteger) .> 3)
                  , ("ui_fun",   do x <- sInteger "x"; pure $ (uninterpret "fc" :: SInteger -> SInteger) x .> x)
                  ]

          -- Problems whose models we cannot validate, along with the explanation we expect
          cant :: [(String, String, Predicate)]
          cant = [ ("accessor",      "The field accessor getNode_2 is applied to a value built with the constructor Leaf",
                                     do e <- free "e"; pure $ isLeaf e .&& getNode_2 e .== 5)
                 , ("fromJust",      "The field accessor getJust_1 is applied to a value built with the constructor Nothing",
                                     do m <- free "m"; pure $ M.isNothing m .&& M.fromJust m .== (5 :: SInteger))
                 , ("head",          "Element 0 of a list of length 0 is accessed",
                                     do l <- free "l"; pure $ L.null l .&& L.head l .== (5 :: SInteger))
                 , ("ui_smtFun",     "The function cnt @(SBV Integer -> SBV Integer) is applied to arguments that depend on uninterpreted values",
                                     do x <- sInteger "x"; pure $ cnt ((uninterpret "f2" :: SInteger -> SInteger) x) .== 2)
                 , ("lambdaArray",   "Arrays created via lambdaArray are not supported concretely",
                                     do i <- sInteger "i"; pure $ readArray (lambdaArray (+ 1)) i .== (5 :: SInteger))
                 , ("irrational",    "The value depends on an irrational algebraic real",
                                     do x <- sReal "x"; pure $ x * x .== 2)
                 , ("quantified",    "The value depends on a quantified variable",
                                     do x <- sInteger "x"; pure $ quantifiedBool $ \(Forall y) -> x .<= y * y)
                 -- Equality of arrays with float elements can't be decided concretely, so we must not guess a table entry
                 , ("ui_fun_undecided", "SBV cannot decide which entry in the model value for the uninterpreted function ff applies to its arguments",
                                     do a <- free "a"; b <- free "b"
                                        let f = uninterpret "ff" :: SArray Integer Float -> SInteger
                                        constrain $ readArray a 0 .== 1 .&& readArray b 0 .== 2
                                        pure $ f a .== 3 .&& f b .== 4)
                 , ("array_index_undecided", "SBV cannot decide which entry of the array applies to the index it is read at",
                                     do a <- free "a"; b <- free "b"
                                        let aa = uninterpret "af" :: SArray (ArrayModel Integer Float) Integer
                                        constrain $ readArray a 0 .== 1 .&& readArray b 0 .== 2
                                        pure $ readArray aa a .== 3 .&& readArray aa b .== 4)
                 ]

          vcfg = z3{validateModel = True}

          checkSat :: String -> SatResult -> Assertion
          checkSat _ (SatResult Satisfiable{}) = pure ()
          checkSat w r                         = assertFailure $ "Expected a validated model, got:\n" ++ w ++ "\n" ++ show r

          validates :: Predicate -> Assertion
          validates p = satWith vcfg p >>= \r -> checkSat "" r

          validatesP :: Predicate -> Assertion
          validatesP p = do r <- proveWith vcfg p
                            case r of
                              ThmResult Satisfiable{} -> pure ()
                              _                       -> assertFailure $ "Expected a validated counter-example, got:\n" ++ show r

          validatesAll :: (SInteger -> SBool) -> Assertion
          validatesAll p = do AllSatResult{allSatResults = rs} <- allSatWith vcfg{allSatMaxModelCount = Just 3} p
                              assertBool "Expected some models" (not (null rs))
                              mapM_ (\r -> checkSat "" (SatResult r)) rs

          cantValidate :: String -> Predicate -> Assertion
          cantValidate msg p = do r <- satWith vcfg p
                                  case r of
                                    SatResult ProofError{} | msg `isInfixOf` show r -> pure ()
                                    _ -> assertFailure $ "Expected validation failure with: " ++ msg ++ "\nGot:\n" ++ show r

          -- Concrete evaluation of floating-point operations with all rounding modes must match the solver
          fpConcrete :: [(String, Assertion)]
          fpConcrete = concat [ [ ("float_"  ++ show rm, fpChk rm (fpVals :: [(Float,  Float,  Float)]))
                                , ("double_" ++ show rm, fpChk rm (fpVals :: [(Double, Double, Double)]))
                                ]
                              | rm <- [minBound .. maxBound]
                              ]

          fpVals :: Fractional a => [(a, a, a)]
          fpVals = [ (1, 3, 7), (0.1, 0.2, 0.3), (-1.5, 1e-40, 2.5e-39), (3.4e38, 3.4e38, -1), (1e300, 1e300, 1e-320), (-0, 0, -0), (1/3, 2/3, -1/3) ]

          fpChk :: forall a. (IEEEFloating a, SymVal a, Show a) => RoundingMode -> [(a, a, a)] -> Assertion
          fpChk rm vals = mapM_ check [ (op, a, b, c) | op <- [0 .. 5 :: Int], (a, b, c) <- vals ]
            where srm = literal rm

                  f :: Int -> SBV a -> SBV a -> SBV a -> SBV a
                  f 0 x y _ = fpAdd srm x y
                  f 1 x y _ = fpSub srm x y
                  f 2 x y _ = fpMul srm x y
                  f 3 x y _ = fpDiv srm x y
                  f 4 x y z = fpFMA srm x y z
                  f _ x _ _ = fpSqrt srm x

                  check (op, a, b, c) = case unliteral (f op (literal a) (literal b) (literal c)) of
                                          Nothing -> assertFailure $ "Not concretely computed: " ++ show (op, a, b, c)
                                          Just r  -> do res <- prove $ do x <- free "x"; y <- free "y"; z <- free "z"
                                                                          constrain $ x .=== literal a .&& y .=== literal b .&& z .=== literal c
                                                                          pure $ f op x y z .=== literal r
                                                        case res of
                                                          ThmResult Unsatisfiable{} -> pure ()
                                                          _ -> assertFailure $ "Concrete result mismatch for " ++ show (op, rm, a, b, c, r) ++ ":\n" ++ show res

          -- Concrete evaluation of overflow checks must match the solver
          ovfConcrete :: [(String, Assertion)]
          ovfConcrete = [ ("word8", ovfChk (map literal [minBound, 1, 100, 200, maxBound] :: [SWord8]))
                        , ("int8",  ovfChk (map literal [minBound, -1, 0, 1, 100, maxBound] :: [SInt8]))
                        ]

          ovfChk :: forall a. (SymVal a, Show a, ArithOverflow (SBV a)) => [SBV a] -> Assertion
          ovfChk vs = mapM_ check [ (op, a, b) | op <- [0 .. 4 :: Int], a <- vs, b <- vs ]
            where f :: Int -> SBV a -> SBV a -> SBool
                  f 0 = bvAddO
                  f 1 = bvSubO
                  f 2 = bvMulO
                  f 3 = bvDivO
                  f _ = const . bvNegO

                  check (op, a, b) = case unliteral (f op a b) of
                                       Nothing -> assertFailure $ "Not concretely computed: " ++ show (op, a, b)
                                       Just r  -> do res <- prove $ do x <- free "x"; y <- free "y"
                                                                       constrain $ x .== a .&& y .== b
                                                                       pure $ f op x y .== literal r
                                                     case res of
                                                       ThmResult Unsatisfiable{} -> pure ()
                                                       _ -> assertFailure $ "Concrete result mismatch for " ++ show (op, a, b, r) ++ ":\n" ++ show res

          -- Concrete evaluation of set operations on mixed regular/complement sets
          setConcrete :: [(String, Bool)]
          setConcrete = [ ("union_rc",        S.union        reg  cmp  `is` ComplementSet (Set.fromList [3]))
                        , ("union_cr",        S.union        cmp  reg  `is` ComplementSet (Set.fromList [3]))
                        , ("intersection_rc", S.intersection reg  cmp  `is` RegularSet    (Set.fromList [1]))
                        , ("intersection_cr", S.intersection cmp  reg  `is` RegularSet    (Set.fromList [1]))
                        , ("difference_rc",   S.difference   reg  cmp  `is` RegularSet    (Set.fromList [2]))
                        , ("difference_cr",   S.difference   cmp  reg  `is` ComplementSet (Set.fromList [1, 2, 3]))
                        , ("difference_cc",   S.difference   cmp  cmp2 `is` RegularSet    (Set.fromList [4]))
                        , ("insert_c",        S.insert 7 cmp           `is` ComplementSet (Set.fromList [2, 3]))
                        , ("delete_c",        S.delete 2 cmp           `is` ComplementSet (Set.fromList [2, 3]))
                        , ("subset_rc",       unliteral (reg `S.isSubsetOf` cmp)  == Just False)
                        , ("subset_rc_true",  unliteral (S.fromList [1] `S.isSubsetOf` cmp) == Just True)
                        ]
            where reg, cmp, cmp2 :: SSet Integer
                  reg  = S.fromList [1, 2]                  -- {1, 2}
                  cmp  = literal $ ComplementSet (Set.fromList [2, 3])  -- everything but {2, 3}
                  cmp2 = literal $ ComplementSet (Set.fromList [2, 3, 4]) -- everything but {2, 3, 4}

                  is s v = case (unliteral s, v) of
                             (Just (RegularSet    a), RegularSet    b) -> a == b
                             (Just (ComplementSet a), ComplementSet b) -> a == b
                             _                                         -> False

          -- Concrete equality of arrays must compare values, not representations
          arrConcrete :: [(String, Bool)]
          arrConcrete = [ ("noop_write_eq",  unliteral (arr .== writeArray arr 7 (readArray arr 7)) == Just True)
                        , ("noop_write_eq2", unliteral (writeArray arr 7 10 .== arr)                  == Just True)
                        , ("write_neq",      unliteral (writeArray arr 7 11 .== arr)                  == Just False)
                        , ("write_neq2",     unliteral (writeArray arr 2 10 .== arr)                  == Just False)
                        -- Nested arrays are compared by value, not by representation
                        , ("nested_noop_eq",  unliteral (writeArray outer 0 arr .== writeArray outer 0 (writeArray arr 7 10)) == Just True)
                        , ("nested_neq",      unliteral (writeArray outer 0 arr .== writeArray outer 0 (writeArray arr 7 11)) == Just False)
                        -- Different defaults: Over an infinite index type, some index maps to the defaults. Over a finite one, we can't tell
                        , ("defaults_neq_infinite",  unliteral (constArray 0 .== (constArray 1 :: SArray Integer Integer)) == Just False)
                        , ("defaults_neq_finite",    unliteral (constArray 0 .== (constArray 1 :: SArray Word8   Integer)) == Nothing)
                        ]
            where arr :: SArray Integer Integer
                  arr = listArray [(2, 7)] 10

                  outer :: SArray Integer (ArrayModel Integer Integer)
                  outer = constArray (literal (ArrayModel [] 0))

          -- Regression test for a z3 bug that returned an invalid model here.
          -- See: https://github.com/Z3Prover/z3/issues/7664
          t6 :: Assertion
          t6 = do r <- satWith z3 $ do xs <- free "xs"
                                       pure $ L.length (L.concat (xs :: SList String)) .>= 5
                  case getModelValue "xs" r of
                    Just (xs :: [String]) -> assertBool ("Model is too short: " ++ show xs) (length (concat xs) >= 5)
                    Nothing               -> assertFailure $ "No model for xs:\n" ++ show r
