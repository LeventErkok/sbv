-----------------------------------------------------------------------------
-- |
-- Module    : TestSuite.Basics.Lambda
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Test lambda generation
-----------------------------------------------------------------------------

{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE DeriveAnyClass      #-}
{-# LANGUAGE DeriveDataTypeable  #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE OverloadedLists     #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving  #-}
{-# LANGUAGE TemplateHaskell     #-}
{-# LANGUAGE TypeApplications    #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module TestSuite.Basics.Lambda(tests)  where

import Prelude hiding((++), map, foldl, foldr, sum, length, zip, zipWith, all, any, concat, filter)
import qualified Prelude as P

import Control.Monad (unless)
import qualified Control.Exception as C

import Data.SBV.Control
import Data.SBV.Internals hiding(free_)

import Documentation.SBV.Examples.Misc.Definitions

import Data.SBV.List
import Data.SBV.Tuple

import Data.Proxy

import Utils.SBVTestFramework

data P
mkUninterpretedSort ''P

drinker :: Predicate
drinker = pure $ quantifiedBool $ \(Exists x) (Forall y) -> d x .=> d y
  where d :: SP -> SBool
        d = uninterpret "D"

-- Test suite
tests :: TestTree
tests =
  testGroup "Basics.Lambda" $ [
        goldenCapturedIO "lambda01" $ record $ \st -> lambdaStr st (kindOf (Proxy @SInteger)) (2             :: SInteger)
      , goldenCapturedIO "lambda02" $ record $ \st -> lambdaStr st (kindOf (Proxy @SInteger)) (\x   -> x+1   :: SInteger)
      , goldenCapturedIO "lambda03" $ record $ \st -> lambdaStr st (kindOf (Proxy @SInteger)) (\x y -> x+y*2 :: SInteger)

      , goldenCapturedIO "lambda04" $ eval1 [1 .. 3 :: Integer] (map (const sFalse),  P.map (const False))
      , goldenCapturedIO "lambda05" $ eval1 [1 .. 5 :: Integer] (map (+1) . map (+2), P.map (+1) . P.map (+2))
      , goldenCapturedIO "lambda06" $ eval1 [1 .. 5 :: Integer]
                                            ( map   (\x -> P.sum [x .^ literal i | i <- [1..10 :: Integer]])
                                            , P.map (\x -> P.sum [x  ^ i         | i <- [1..10 :: Integer]])
                                            )

      , goldenCapturedIO "lambda07" $ eval1 ([[1..5], [1..10], [1..20]] :: [[Integer]])
                                            ( let sum = foldl (+) 0 in   sum .   map   sum
                                            ,                          P.sum . P.map P.sum
                                            )

      , goldenCapturedIO "lambda08" $ eval1 [1 .. 5 :: Float]   (map (+1), P.map (+1))
      , goldenCapturedIO "lambda09" $ eval1 [1 .. 5 :: Int8]    (map (+1), P.map (+1))
      , goldenCapturedIO "lambda10" $ eval1 [1 .. 5 :: Integer] (map (+1), P.map (+1))
      , goldenCapturedIO "lambda11" $ eval1 [1 .. 5 :: Word8]   (map (+1), P.map (+1))

      , goldenCapturedIO "lambda12" $ eval1 [1 .. 3 :: Integer] (map singleton, P.map (: []))

      , goldenCapturedIO "lambda13" $ eval1 [(x, y) | x <- [1..3], y <- [4..6 :: Integer]]
                                            (map (\t -> t^._1 + t^._2), P.map (uncurry (+)))

      , goldenCapturedIO "lambda14" $ eval1 [1 .. 5 :: Integer] (mapi (+) 10, P.zipWith (+) [10..])

      , goldenCapturedIO "lambda15" $ eval1 [1 .. 5 :: Integer] (foldl (+) 0, P.sum)
      , goldenCapturedIO "lambda16" $ eval1 [1 .. 5 :: Integer] (foldl (*) 1, P.product)
      , goldenCapturedIO "lambda17" $ eval1 [1 .. 5 :: Integer]
                                           (   foldl (\soFar elt -> singleton elt ++ soFar) []
                                           , P.foldl (\soFar elt ->           elt :  soFar) []
                                           )

      , goldenCapturedIO "lambda18" $ eval1 [1 .. 5 :: Integer]
                                            (   foldli (\i b a    -> i+b+a) 10 0
                                            , P.foldl  (\b (i, a) -> i+b+a)  0 . P.zip [10..]
                                            )

      , goldenCapturedIO "lambda19" $ eval1 [1 .. 5 :: Integer] (foldr (+) 0, P.foldr (+) 0)
      , goldenCapturedIO "lambda20" $ eval1 [1 .. 5 :: Integer] (foldr (*) 1, P.foldr (*) 1)
      , goldenCapturedIO "lambda21" $ eval1 [1 .. 5 :: Integer]
                                           (   foldr (\elt soFar -> soFar   ++ singleton elt) []
                                           , P.foldr (\elt soFar -> soFar P.++ [elt])         []
                                           )

      , goldenCapturedIO "lambda22" $ eval2 [1 .. 10 :: Integer] [11..20 :: Integer] (zip, P.zip)
      , goldenCapturedIO "lambda23" $ eval2 [1 .. 10 :: Integer] [10, 9 .. 1 :: Integer]
                                            ( \a b ->   foldr (+) 0 (  map (\t -> t^._1+t^._2::SInteger) (  zip a b))
                                            , \a b -> P.foldr (+) 0 (P.map (\t -> fst t+snd t::Integer ) (P.zip a b))
                                            )
      , goldenCapturedIO "lambda24" $ eval2 [1 .. 10 :: Integer] [11..20 :: Integer] (zipWith (+), P.zipWith (+))
      , goldenCapturedIO "lambda25" $ eval2 [1 .. 10 :: Integer] [10, 9 .. 1 :: Integer]
                                            ( \a b ->   foldr (+) 0 (  zipWith (+) a b)
                                            , \a b -> P.foldr (+) 0 (P.zipWith (+) a b)
                                            )

      , goldenCapturedIO "lambda26" $ eval1 ([[1..5], [1..10], [1..20]] :: [[Integer]]) (concat, P.concat)

      , goldenCapturedIO "lambda27" $ eval1 [2, 4, 6,    8, 10 :: Integer] (all (\x -> x `sMod` 2 .== 0), P.all (\x -> x `mod` 2 == 0))
      , goldenCapturedIO "lambda28" $ eval1 [2, 4, 6, 1, 8, 10 :: Integer] (all (\x -> x `sMod` 2 .== 0), P.all (\x -> x `mod` 2 == 0))

      , goldenCapturedIO "lambda29" $ eval1 [2, 4, 6,    8, 10 :: Integer] (any (\x -> x `sMod` 2 ./= 0), P.any (\x -> x `mod` 2 /= 0))
      , goldenCapturedIO "lambda30" $ eval1 [2, 4, 6, 1, 8, 10 :: Integer] (any (\x -> x `sMod` 2 .== 0), P.any (\x -> x `mod` 2 == 0))

      , goldenCapturedIO "lambda31" $ eval1 [1 .. 10 :: Integer] (filter (\x -> x `sMod` 2 .== 0), P.filter (\x -> x `mod` 2 == 0))
      , goldenCapturedIO "lambda32" $ eval1 [1 .. 10 :: Integer] (filter (\x -> x `sMod` 2 ./= 0), P.filter (\x -> x `mod` 2 /= 0))

      , goldenCapturedIO "lambda33" $ record $ \st -> lambdaStr st (kindOf (Proxy @SInt8)) (0           :: SInt8)
      , goldenCapturedIO "lambda34" $ record $ \st -> lambdaStr st (kindOf (Proxy @SInt8)) (\x   -> x+1 :: SInt8)
      , goldenCapturedIO "lambda35" $ record $ \st -> lambdaStr st (kindOf (Proxy @SInt8)) (\x y -> x+y :: SInt8)

      , goldenCapturedIO "lambda36" $ record $ \st -> constraintStr st $ \(Forall (_ :: SBool))  -> sTrue
      , goldenCapturedIO "lambda37" $ record $ \st -> constraintStr st $ \(Forall b)             -> sNot b
      , goldenCapturedIO "lambda38" $ record $ \st -> constraintStr st $ \(Forall x) (Forall y) -> x .== (0 :: SInteger) .|| y

      , goldenCapturedIO "lambda40" $ record $ \st -> namedLambdaStr st "lambda40" t_i    (0           :: SInteger)
      , goldenCapturedIO "lambda41" $ record $ \st -> namedLambdaStr st "lambda41" t_i2i  (\x   -> x+1 :: SInteger)
      , goldenCapturedIO "lambda42" $ record $ \st -> namedLambdaStr st "lambda42" t_ii2i (\x y -> x+y :: SInteger)

      , goldenCapturedIO "lambda43" $ record $ \st -> namedLambdaStr st "lambda43" t_w32         (0           :: SWord32)
      , goldenCapturedIO "lambda44" $ record $ \st -> namedLambdaStr st "lambda44" t_w32_w32     (\x   -> x+1 :: SWord32)
      , goldenCapturedIO "lambda45" $ record $ \st -> namedLambdaStr st "lambda45" t_w32_w32_w32 (\x y -> x+y :: SWord32)

      , goldenCapturedIO "lambda46" $ runSat ((.== 5) . add1)

      , goldenCapturedIO "lambda47"   $ runSat2 (\a r -> a .== 5 .&& sumToN a .== r)
      , goldenCapturedIO "lambda47_c" $ runSat  (sumToN 5 .==)

      , goldenCapturedIO "lambda48"   $ runSat2 (\a r -> a .== [1,2,3::Integer] .&& len a .== r)
      , goldenCapturedIO "lambda48_c" $ runSat  (len [1,2,3::Integer] .==)

      , goldenCapturedIO "lambda49"   $ runSat2 (\a r -> a .== 20 .&& isEven a .== r)
      , goldenCapturedIO "lambda49_c" $ runSat  (isEven 20 .==)

      , goldenCapturedIO "lambda50"   $ runSat2 (\a r -> a .== 21 .&& isEven a .== r)
      , goldenCapturedIO "lambda50_c" $ runSat  (isEven 21 .==)

      , goldenCapturedIO "lambda51"   $ runSat2 (\a r -> a .== 20 .&& isOdd  a .== r)
      , goldenCapturedIO "lambda51_c" $ runSat  (isOdd  20 .==)

      , goldenCapturedIO "lambda52"   $ runSat2 (\a r -> a .== 21 .&& isOdd  a .== r)
      , goldenCapturedIO "lambda52_c" $ runSat  (isOdd  21 .==)

      , goldenCapturedIO "lambda53" $ runSat $ \x -> x .== smtFunction "foo" (+(x::SInteger)) x

      -- Make sure we can handle dependency orders
      , goldenCapturedIO "lambda54" $ runSat   $ \x -> let foo = smtFunction "foo" (\a -> bar a + 1)
                                                           bar = smtFunction "bar" (+1)
                                                       in bar x + foo x .== (x :: SInteger)
      , goldenCapturedIO "lambda55" $ runSat   $ \x -> let foo = smtFunction "foo" (\a -> bar a + 1)
                                                           bar = smtFunction "bar" (+1)
                                                       in foo x + bar x .== (x :: SInteger)
      , goldenCapturedIO "lambda56" $ runUnsat $ \x -> let foo = smtFunction "foo" (\a -> bar a + 1)
                                                           bar = smtFunction "bar" (\a -> foo a + 1)
                                                       in foo x + bar x .== (x :: SInteger)
      , goldenCapturedIO "lambda57" $ runSat   $ \x -> let f1 = smtFunction "f1" (\a -> ite (a .== 0) 0 (1 + (f1 (a-1) + f2 (a-2))))
                                                           f2 = smtFunction "f2" (\a -> ite (a .== 0) 0 (1 + (f2 (a-1) + f3 (a-2))))
                                                           f3 = smtFunction "f3" (\a -> ite (a .== 0) 0 (1 + (f3 (a-1) + f4 (a-2))))
                                                           f4 = smtFunction "f4" (\a -> ite (a .== 0) 0 (1 + (f4 (a-1) + f1 (a-2))))
                                                       in f1 x .== (x :: SWord8)

      -- Quantified axioms
      , goldenCapturedIO "lambda58" $ record $ \st -> constraintStr st $ \(Forall b) (Exists c) -> sNot b .|| c
      , goldenCapturedIO "lambda59" $ record $ \st -> constraintStr st $ \(Forall x) (Exists y) -> x .== (0 :: SInteger) .|| y

      , goldenCapturedIO "lambda60" $ runAxSat   $ constrain $ \(Forall x) (Exists y) (Exists z) -> y .> (x+z :: SInteger)
      , goldenCapturedIO "lambda61" $ runAxUnsat $ constrain $ \(Forall x) (Exists y) -> y .> (x :: SWord8)

      -- Quantified booleans
      , goldenCapturedIO "lambda62" $ \rf -> do m <- proveWith z3{verbose=True, redirectVerbose=Just rf} drinker
                                                appendFile rf ("\nRESULT:\n" P.++ show m P.++ "\n")
                                                `C.catch` (\(e :: C.SomeException) -> appendFile rf ("\nEXCEPTION CAUGHT:\n" P.++ show e P.++ "\n"))

      -- Special relations (kind of lambda related)
      , goldenCapturedIO "lambda63" $ runP $         quantifiedBool (\(Forall x) -> rel (x, x))
      , goldenCapturedIO "lambda64" $ runP $ po  .=> quantifiedBool (\(Forall x) -> rel (x, x))
      , goldenCapturedIO "lambda65" $ runP $ poI .=> quantifiedBool (\(Forall x) -> leq (x, x))
      , goldenCapturedIO "lambda66" $ runP $ let u   = uninterpret "U" :: Relation Integer
                                                 tcU = mkTransitiveClosure "tcU" u
                                             in quantifiedBool (\(Forall x) (Forall y) (Forall z)
                                                                     -> (u (x, y) .&& u (y, z)) .=> tcU (x, z))

      , goldenCapturedIO "lambda67" $ runP $ let u   = uninterpret "U" :: Relation Word8
                                                 tcU = mkTransitiveClosure "tcU" u
                                             in quantifiedBool (\(Forall x) (Forall y) (Forall z)
                                                                     -> (u (x, y) .&& u (y, z)) .=> tcU (x, z))

      -- Not really lambda related, but kind of fits in here
      , goldenCapturedIO "lambda68" $ runS $ \(Forall x) -> uninterpret "F" x .== 2*x+(3::SInteger)
      , goldenCapturedIO "lambda69" $ runS $ \(Forall x) (Forall y) -> uninterpret "F" x y .== 2*x+(3-y::SInteger)

      -- Most skolems are tested inline, here's a fancy one!
      , goldenCapturedIO "lambda70" $
                let phi :: ExistsUnique "x" Integer -> SBool
                    phi (ExistsUnique  x) = x .== 0 .|| x .== 1

                    nPhi :: Forall "x" Integer -> Exists "x_eu1" Integer -> Exists "x_eu2" Integer -> SBool
                    nPhi = qNot phi

                    snPhi :: Forall "x" Integer -> SBool
                    snPhi = skolemize nPhi
                in runS snPhi

      , goldenCapturedIO "lambda71" $ \f -> sbv2smt def_foo >>= writeFile f
      , goldenCapturedIO "lambda72" $ \f -> sbv2smt def_bar >>= writeFile f
      , goldenCapturedIO "lambda73" $ \f -> sbv2smt def_baz >>= writeFile f
      , goldenCapturedIO "lambda74" $ \f -> sbv2smt def_e   >>= writeFile f
      , goldenCapturedIO "lambda75" $ \f -> sbv2smt def_o   >>= writeFile f

      , goldenCapturedIO "lambda76" $ \f -> sbv2smt (2 :: SInteger)                    >>= writeFile f
      , goldenCapturedIO "lambda77" $ \f -> sbv2smt (literal 'a' :: SChar)             >>= writeFile f
      , goldenCapturedIO "lambda78" $ \f -> sbv2smt (literal [1,2,3] :: SList Integer) >>= writeFile f

      , goldenCapturedIO "lambda79" $ \f -> sbv2smt def_t1 >>= writeFile f
      , goldenCapturedIO "lambda80" $ \f -> sbv2smt def_t2 >>= writeFile f
      ]
   P.++ qc1 "lambdaQC1" P.sum (foldr (+) (0::SInteger))
   P.++ qc2 "lambdaQC2" (+)  (smtFunction "sadd" ((+) :: SInteger -> SInteger -> SInteger))
   P.++ qc1 "lambdaQC3" (\n -> let pn = abs n in (pn * (pn+1)) `sDiv` 2)
                        (let ssum = smtFunction "ssum" $ \(n :: SInteger) -> let pn = abs n in ite (pn .== 0) 0 (pn + ssum (pn - 1)) in ssum)
  where t_i           = SBVType [kindOf (Proxy @SInteger)]
        t_i2i         = SBVType [kindOf (Proxy @SInteger), kindOf (Proxy @SInteger)]
        t_ii2i        = SBVType [kindOf (Proxy @SInteger), kindOf (Proxy @SInteger), kindOf (Proxy @SInteger)]
        t_w32         = SBVType [kindOf (Proxy @SWord32)]
        t_w32_w32     = SBVType [kindOf (Proxy @SWord32), kindOf (Proxy @SWord32)]
        t_w32_w32_w32 = SBVType [kindOf (Proxy @SWord32), kindOf (Proxy @SWord32), kindOf (Proxy @SWord32)]

        def_foo, def_bar, def_baz, def_e, def_o :: SInteger -> SInteger
        def_foo = smtFunction "foo" $ \x -> def_bar (x-1)
        def_bar = smtFunction "bar" $ \x -> def_bar (x-1)
        def_baz = smtFunction "baz" $ \x -> x+1
        def_e = smtFunction "e" $ \x -> def_o (x-1)
        def_o = smtFunction "o" $ \x -> def_e (x-1)
        def_t1 = smtFunction "foo" (\x -> select [1,2,3]       (0 :: SWord32)  (x::SInteger))
        def_t2 = smtFunction "foo" (\x -> select [x+1,x+2,x+3] (0 :: SInteger) (x::SInteger))

        rel, leq :: Relation Integer
        rel = uninterpret "R"
        leq = uncurry $ smtFunction "leq" (.<=)
        po  = isPartialOrder "poR" rel
        poI = isPartialOrder "poI" leq

        record :: (State -> IO String) -> FilePath -> IO ()
        record gen rf = do st <- mkNewState defaultSMTCfg (LambdaGen 0)
                           appendFile rf . (P.++ "\n") =<< gen st

        runP b rf = runGen proveWith b rf
        runS b rf = runGen satWith   b rf
        runGen a b rf = do m <- a z3{verbose=True, redirectVerbose=Just rf} b
                           appendFile rf ("\nRESULT:\n" P.++ show m P.++ "\n")

        runSat   f = runSatExpecting f Sat
        runUnsat f = runSatExpecting f Unsat

        runAxSat   f = runSatAxExpecting f Sat
        runAxUnsat f = runSatAxExpecting f Unsat

        runSatAxExpecting f what rf = do m <- runSMTWith z3{verbose=True, redirectVerbose=Just rf} run
                                         appendFile rf ("\nRESULT:\n" P.++ m P.++ "\n")
                                         `C.catch` (\(e :: C.SomeException) -> appendFile rf ("\nEXCEPTION CAUGHT:\n" P.++ show e P.++ "\n"))
           where run = do _ <- f
                          query $ do cs <- checkSat
                                     if cs /= what
                                        then error $ "Unexpected output: " P.++ show cs
                                        else if cs == Sat
                                                then showModel z3 <$> getModel
                                                else pure $ "All good, expecting: " P.++ show cs

        runSatExpecting f what rf = do m <- runSMTWith z3{verbose=True, redirectVerbose=Just rf} run
                                       appendFile rf ("\nRESULT:\n" P.++ m P.++ "\n")
                                       `C.catch` (\(e :: C.SomeException) -> appendFile rf ("\nEXCEPTION CAUGHT:\n" P.++ show e P.++ "\n"))
           where run = do arg <- free_
                          constrain $ f arg
                          query $ do arg2 <- freshVar_
                                     constrain $ f arg2
                                     cs <- checkSat
                                     if cs /= what
                                        then error $ "Unexpected output: " P.++ show cs
                                        else if cs == Sat
                                                then showModel z3 <$> getModel
                                                else pure $ "All good, expecting: " P.++ show cs

        runSat2 f rf = do m <- runSMTWith z3{verbose=True, redirectVerbose=Just rf} run
                          appendFile rf ("\nRESULT:\n" P.++ showModel z3 m P.++ "\n")
           where run = do arg1 <- free_
                          arg2 <- free_
                          constrain $ f arg1 arg2
                          query $ do arg3 <- freshVar_
                                     arg4 <- freshVar_
                                     constrain $ f arg3 arg4
                                     cs <- checkSat
                                     case cs of
                                       Sat -> getModel
                                       _   -> error $ "Unexpected output: " P.++ show cs

eval1 :: (SymVal a, SymVal b, Show a, Show b, Eq b) => a -> (SBV a -> SBV b, a -> b) -> FilePath -> IO ()
eval1 cArg (sFun, cFun) rf = do m <- runSMTWith z3{verbose=True, redirectVerbose=Just rf} run
                                appendFile rf ("\nRESULT:\n" P.++ showModel z3 m P.++ "\n")

 where run = do arg <- free_
                res <- free_
                constrain $ arg .== literal cArg
                constrain $ res .== sFun arg

                let concResult = cFun cArg

                query $ do
                  cs <- checkSat
                  case cs of
                    Sat -> do resV <- getValue res
                              unless (resV == concResult) $
                                  error $ unlines [ "Bad output:"
                                                  , "  arg      = " P.++ show cArg
                                                  , "  concrete = " P.++ show concResult
                                                  , "  symbolic = " P.++ show resV
                                                  ]
                              getModel
                    _ -> error $ "Unexpected output: " P.++ show cs

eval2 :: (SymVal a, SymVal b, SymVal c, Eq c, Show a, Show b, Show c) => a -> b -> (SBV a -> SBV b -> SBV c, a -> b -> c) -> FilePath -> IO ()
eval2 cArg1 cArg2 (sFun, cFun) rf = do m <- runSMTWith z3{verbose=True, redirectVerbose=Just rf} run
                                       appendFile rf ("\nRESULT:\n" P.++ showModel z3 m P.++ "\n")

 where run = do arg1 <- free_
                arg2 <- free_
                res <- free_
                constrain $ arg1 .== literal cArg1
                constrain $ arg2 .== literal cArg2
                constrain $ res  .== sFun arg1 arg2

                let concResult = cFun cArg1 cArg2

                query $ do
                  cs <- checkSat
                  case cs of
                    Sat -> do resV <- getValue res
                              unless (resV == concResult) $
                                  error $ unlines [ "Bad output:"
                                                  , "  arg1     = " P.++ show cArg1
                                                  , "  arg2     = " P.++ show cArg2
                                                  , "  concrete = " P.++ show concResult
                                                  , "  symbolic = " P.++ show resV
                                                  ]
                              getModel
                    _ -> error $ "Unexpected output: " P.++ show cs


{- HLint ignore module "Use map once"   -}
{- HLint ignore module "Use sum"        -}
{- HLint ignore module "Fuse foldr/map" -}
{- HLint ignore module "Use zipWith"    -}
{- HLint ignore module "Use uncurry"    -}
{- HLint ignore module "Use even"       -}
{- HLint ignore module "Use odd"        -}
{- HLint ignore module "Use product"    -}
{- HLint ignore module "Avoid lambda"   -}
{- HLint ignore module "Eta reduce"     -}
