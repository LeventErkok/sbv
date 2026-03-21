-----------------------------------------------------------------------------
-- |
-- Module    : TestSuite.Basics.Recursive
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Some recursive definitions.
-----------------------------------------------------------------------------

{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE OverloadedLists     #-}
{-# LANGUAGE QuasiQuotes         #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeAbstractions    #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module TestSuite.Basics.Recursive(tests) where

import Utils.SBVTestFramework

import Data.SBV.Internals  (genMkSymVar, unSBV, VarContext(..))

import Data.List (isInfixOf)

import qualified Data.SBV.List as L
import qualified Data.SBV.Dynamic as D
import Data.SBV.TP (runTPWith, lemma)

import qualified Control.Exception as C

import Documentation.SBV.Examples.Misc.Definitions (ack)
import Documentation.SBV.Examples.TP.McCarthy91    (mcCarthy91)

-- This is recursive and can't be symbolically simulated for arbitrary inputs.
-- But we can still prove a few things about it!
mgcd :: SWord8 -> SWord8 -> SWord8
mgcd a b = [sCase| b of
              _ | b .== 0 -> a
              _           -> mgcd b (a `sMod` b)
           |]

-- Same construction, expressed in terms of the dynamic interface
mgcdDyn :: Int -> IO ThmResult
mgcdDyn i = D.proveWith z3 $ do

              let var8 :: String -> Symbolic D.SVal
                  var8 nm = unSBV <$> genMkSymVar word8 (NonQueryVar (Just D.ALL)) (Just nm)

                  word8   = KBounded False 8
                  zero8   = D.svInteger word8 0

                  gcdDyn a b = D.svIte (b `D.svEqual` zero8) a (gcdDyn b (a `D.svRem` b))

              x <- var8 "x"

              let prop0 = gcdDyn zero8 x `D.svEqual` x
                  prop1 = gcdDyn x zero8 `D.svEqual` x

              return $  if i == 0 then prop0 else prop1

checkThm :: ThmResult -> Assertion
checkThm r = assert isThm
  where isThm = case r of
                  ThmResult Unsatisfiable{} -> return True :: IO Bool
                  ThmResult Satisfiable{}   -> return False
                  _                         -> error "checkThm: Unexpected result!"

-- | Test that auto-guess succeeds for an integer-recursive function (abs measure)
autoGuessInteger :: Assertion
autoGuessInteger = assertIsSat $ \(x :: SInteger) -> f x .== x
  where f :: SInteger -> SInteger
        f = smtFunction "autoGuessIntF" $ \x -> ite (x .<= 0) 0 (1 + f (x - 1))

-- | Test that auto-guess succeeds for a list-recursive function (length measure)
autoGuessList :: Assertion
autoGuessList = assertIsSat $ \(xs :: SList Integer) -> myLen xs .>= 0
  where myLen :: SList Integer -> SInteger
        myLen = smtFunction "autoGuessListLen" $ \xs ->
                  ite (L.null xs) 0 (1 + myLen (L.tail xs))

-- | Test that auto-guess fails when candidates exist but don't work (Ackermann)
autoGuessFailCandidates :: Assertion
autoGuessFailCandidates = do
  r <- C.try $ sat $ \(x :: SInteger) (y :: SInteger) -> ack' x y .== 0
  case r of
    Left (e :: C.SomeException) -> if "Cannot determine a termination measure" `isInfixOf` show e
                                      then pure ()
                                      else assertFailure $ "Unexpected exception: " ++ show e
    Right _                     -> assertFailure "Expected error for Ackermann auto-guess"
  where ack' :: SInteger -> SInteger -> SInteger
        ack' = smtFunction "ackermann" $ \m n ->
                ite (m .== 0) (n + 1)
                    (ite (n .== 0) (ack' (m - 1) 1)
                                   (ack' (m - 1) (ack' m (n - 1))))

-- | Test that auto-guess fails when no candidates can be derived (non-integer, non-list args)
autoGuessNoCandidates :: Assertion
autoGuessNoCandidates = do
  r <- C.try $ sat $ \(b :: SBool) -> h b .== 0
  case r of
    Left (e :: C.SomeException) -> if "No measure candidates" `isInfixOf` show e
                                      then pure ()
                                      else assertFailure $ "Unexpected exception: " ++ show e
    Right _                     -> assertFailure "Expected error for no-candidate auto-guess"
  where h :: SBool -> SInteger
        h = smtFunction "noCandidate" $ \b -> ite b (1 + h (sNot b)) 0

-- | Test that a non-recursive smtFunction without a measure is accepted
nonRecursiveNoMeasure :: Assertion
nonRecursiveNoMeasure = assertIsSat $ \(x :: SInteger) -> g x .== 4
  where g :: SInteger -> SInteger
        g = smtFunction "nonRecG" $ \x -> 2 * x

-- Test suite
tests :: TestTree
tests = testGroup "Basics.Recursive"
   [ testCase "recursive1"                $ assertIsThm $ \x -> mgcd    0 x .== x
   , testCase "recursive2"                $ assertIsThm $ \x -> mgcd    x 0 .== x
   , testCase "recursiveDyn1"             $ checkThm =<< mgcdDyn 0
   , testCase "recursiveDyn2"             $ checkThm =<< mgcdDyn 1
   , testCase "autoGuessInteger"          autoGuessInteger
   , testCase "autoGuessList"             autoGuessList
   , testCase "autoGuessFailCandidates"   autoGuessFailCandidates
   , testCase "autoGuessNoCandidates"     autoGuessNoCandidates
   , testCase "nonRecursiveNoMeasure"     nonRecursiveNoMeasure

   -- Test that an explicit measure that doesn't decrease is rejected
   , goldenCapturedIO "recursive3_badMeasure" $ \rf -> do
        let badSum :: SInteger -> SInteger
            badSum = smtFunctionWithMeasure "badSum" (\_ -> 1 :: SInteger, [])
                   $ \x -> ite (x .<= 0) 0 (x + badSum (x - 1))
        r <- C.try $ satWith z3{verbose=True, redirectVerbose=Just rf} $
                \x -> badSum x .>= 0
        case r of
          Left (e :: C.SomeException) -> appendFile rf ("\nEXCEPTION:\n" ++ show e ++ "\n")
          Right m                     -> appendFile rf ("\nRESULT:\n" ++ show m ++ "\n")

   -- Test that lexicographic measure auto-guess works for Ackermann (nested recursion)
   , goldenCapturedIO "recursive1_ack" $ \rf -> do
        m <- satWith z3{verbose=True, redirectVerbose=Just rf} $
                \y r -> y .== (5 :: SInteger) .&& r .== ack 1 y
        appendFile rf ("\nRESULT:\n" ++ show m ++ "\n")

   -- Test that explicit measure works for enumFromThenTo.down (descending enumeration)
   , goldenCapturedIO "recursive2_enum" $ \rf -> do
        m <- satWith z3{verbose=True, redirectVerbose=Just rf} $
                \x -> L.length [sEnum|(5::SInteger), 4 .. x|] .>= 0
        appendFile rf ("\nRESULT:\n" ++ show m ++ "\n")

   -- Test that contract-based measure works for McCarthy91 (nested recursion)
   , goldenCapturedIO "recursive4_mcCarthy91" $ \rf -> do
        m <- satWith z3{verbose=True, redirectVerbose=Just rf} $
                \n -> mcCarthy91 n .== (91 :: SInteger)
        appendFile rf ("\nRESULT:\n" ++ show m ++ "\n")

   -- Test that a bad contract is rejected (contract says result is always 0, which is wrong)
   , goldenCapturedIO "recursive5_badContract" $ \rf -> do
        let mc91bad :: SInteger -> SInteger
            mc91bad = smtFunctionWithContract "mc91bad"
                        ( \n -> 0 `smax` (101 - n)
                        , \_ r -> r .== 0
                        , []
                        )
                    $ \n -> ite (n .> 100) (n - 10) (mc91bad (mc91bad (n + 11)))
        r <- C.try $ satWith z3{verbose=True, redirectVerbose=Just rf} $
                \n -> mc91bad n .>= 0
        case r of
          Left (e :: C.SomeException) -> appendFile rf ("\nEXCEPTION:\n" ++ show e ++ "\n")
          Right m                     -> appendFile rf ("\nRESULT:\n" ++ show m ++ "\n")

   -- Test that a true-but-useless contract is rejected (contract is trivially True,
   -- so the IH provides no information about recursive call results, and the measure
   -- decrease for the outer call can't be proven)
   , goldenCapturedIO "recursive6_uselessContract" $ \rf -> do
        let mc91triv :: SInteger -> SInteger
            mc91triv = smtFunctionWithContract "mc91triv"
                         ( \n -> 0 `smax` (101 - n)
                         , \_ _ -> sTrue
                         , []
                         )
                     $ \n -> ite (n .> 100) (n - 10) (mc91triv (mc91triv (n + 11)))
        r <- C.try $ satWith z3{verbose=True, redirectVerbose=Just rf} $
                \n -> mc91triv n .>= 0
        case r of
          Left (e :: C.SomeException) -> appendFile rf ("\nEXCEPTION:\n" ++ show e ++ "\n")
          Right m                     -> appendFile rf ("\nRESULT:\n" ++ show m ++ "\n")

   -- Test that a productive function (guarded recursion) is accepted
   , goldenCapturedIO "recursive7_productive" $ \rf -> do
        let rep :: SInteger -> SInteger -> SList Integer
            rep = smtProductiveFunction "rep" $ \n x ->
                    ite (n .<= 0) L.nil (x L..: rep (n - 1) x)
        m <- satWith z3{verbose=True, redirectVerbose=Just rf} $
                \x -> L.length (rep 3 x) .== 3
        appendFile rf ("\nRESULT:\n" ++ show m ++ "\n")

   -- Test that a non-guarded function marked productive is rejected
   , goldenCapturedIO "recursive8_badProductive" $ \rf -> do
        let bad :: SInteger -> SInteger
            bad = smtProductiveFunction "bad" $ \n -> ite (n .== 0) 0 (1 + bad (n - 1))
        r <- C.try $ satWith z3{verbose=True, redirectVerbose=Just rf} $
                \n -> bad n .>= 0
        case r of
          Left (e :: C.SomeException) -> appendFile rf ("\nEXCEPTION:\n" ++ show e ++ "\n")
          Right m                     -> appendFile rf ("\nRESULT:\n" ++ show m ++ "\n")

   -- Test that a multi-arg productive function (guarded recursion) is accepted
   , goldenCapturedIO "recursive9_productive2" $ \rf -> do
        let countdown :: SInteger -> SList Integer
            countdown = smtProductiveFunction "countdown" $ \n ->
                          ite (n .<= 0) (L.singleton 0) (n L..: countdown (n - 1))
        m <- satWith z3{verbose=True, redirectVerbose=Just rf} $
                \n -> L.head (countdown n) .== (n :: SInteger) .&& n .> 0
        appendFile rf ("\nRESULT:\n" ++ show m ++ "\n")

   -- Test mutual recursion (2-way): mf calls mg, mg calls mf, neither is self-recursive.
   -- No measure check should fire. The SMTLib emission should use define-funs-rec.
   , goldenCapturedIO "recursive10_mutual" $ \rf -> do
        let mf :: SInteger -> SInteger
            mf = smtFunction "mf" $ \n -> ite (n .<= 0) 0 (1 + mg (n - 1))
            mg :: SInteger -> SInteger
            mg = smtFunction "mg" $ \n -> ite (n .<= 0) 0 (1 + mf (n - 1))
        m <- satWith z3{verbose=True, redirectVerbose=Just rf} $
                \x -> mf x .== (x :: SInteger)
        appendFile rf ("\nRESULT:\n" ++ show m ++ "\n")

   -- Test chain recursion (3-way): ca calls cb, cb calls cc, cc calls ca.
   -- No measure check should fire. The SMTLib emission should use define-funs-rec.
   , goldenCapturedIO "recursive11_chain" $ \rf -> do
        let ca :: SInteger -> SInteger
            ca = smtFunction "ca" $ \n -> ite (n .<= 0) 0 (1 + cb (n - 1))
            cb :: SInteger -> SInteger
            cb = smtFunction "cb" $ \n -> ite (n .<= 0) 0 (1 + cc (n - 1))
            cc :: SInteger -> SInteger
            cc = smtFunction "cc" $ \n -> ite (n .<= 0) 0 (1 + ca (n - 1))
        m <- satWith z3{verbose=True, redirectVerbose=Just rf} $
                \x -> ca x .== (x :: SInteger)
        appendFile rf ("\nRESULT:\n" ++ show m ++ "\n")

   -- Test bad mutual recursion: bf calls bg with (n+1), so no measure can decrease.
   , goldenCapturedIO "recursive12_badMutual" $ \rf -> do
        let bf :: SInteger -> SInteger
            bf = smtFunction "bf" $ \n -> ite (n .<= 0) 0 (1 + bg (n + 1))
            bg :: SInteger -> SInteger
            bg = smtFunction "bg" $ \n -> ite (n .<= 0) 0 (1 + bf (n - 1))
        r <- C.try $ satWith z3{verbose=True, redirectVerbose=Just rf} $
                \x -> bf x .== (x :: SInteger)
        case r of
          Left (e :: C.SomeException) -> appendFile rf ("\nEXCEPTION:\n" ++ show e ++ "\n")
          Right m                     -> appendFile rf ("\nRESULT:\n" ++ show m ++ "\n")

   -- Test mutual recursion with explicit measures: ef calls eg, eg calls ef, both decreasing.
   , goldenCapturedIO "recursive13_mutualMeasure" $ \rf -> do
        let ef :: SInteger -> SInteger
            ef = smtFunctionWithMeasure "ef" (abs, [])
               $ \n -> ite (n .<= 0) 0 (1 + eg (n - 1))
            eg :: SInteger -> SInteger
            eg = smtFunctionWithMeasure "eg" (abs, [])
               $ \n -> ite (n .<= 0) 0 (1 + ef (n - 1))
        m <- satWith z3{verbose=True, redirectVerbose=Just rf} $
                \x -> ef x .== (x :: SInteger)
        appendFile rf ("\nRESULT:\n" ++ show m ++ "\n")

   -- Test mutual recursion with explicit measure that fails: constant measure doesn't decrease.
   , goldenCapturedIO "recursive14_badMutualMeasure" $ \rf -> do
        let hf :: SInteger -> SInteger
            hf = smtFunctionWithMeasure "hf" (\_ -> 1 :: SInteger, [])
               $ \n -> ite (n .<= 0) 0 (1 + hg (n - 1))
            hg :: SInteger -> SInteger
            hg = smtFunctionWithMeasure "hg" (\_ -> 1 :: SInteger, [])
               $ \n -> ite (n .<= 0) 0 (1 + hf (n - 1))
        r <- C.try $ satWith z3{verbose=True, redirectVerbose=Just rf} $
                \x -> hf x .== (x :: SInteger)
        case r of
          Left (e :: C.SomeException) -> appendFile rf ("\nEXCEPTION:\n" ++ show e ++ "\n")
          Right m                     -> appendFile rf ("\nRESULT:\n" ++ show m ++ "\n")

   -- Test mixed mutual recursion: xf has explicit measure, xg uses auto-guess.
   -- xf's user-provided measure (abs n) is tried first and works for the whole group.
   , goldenCapturedIO "recursive15_mixedMutualMeasure" $ \rf -> do
        let xf :: SInteger -> SInteger
            xf = smtFunctionWithMeasure "xf" (abs, [])
               $ \n -> ite (n .<= 0) 0 (1 + xg (n - 1))
            xg :: SInteger -> SInteger
            xg = smtFunction "xg"
               $ \n -> ite (n .<= 0) 0 (1 + xf (n - 1))
        m <- satWith z3{verbose=True, redirectVerbose=Just rf} $
                \x -> xf x .== (x :: SInteger)
        appendFile rf ("\nRESULT:\n" ++ show m ++ "\n")

   -- Test bad mixed mutual recursion: yf has explicit measure but yg calls yf with (n+1).
   -- The user-provided measure fails, and auto-guess also fails.
   , goldenCapturedIO "recursive16_badMixedMutualMeasure" $ \rf -> do
        let yf :: SInteger -> SInteger
            yf = smtFunctionWithMeasure "yf" (abs, [])
               $ \n -> ite (n .<= 0) 0 (1 + yg (n - 1))
            yg :: SInteger -> SInteger
            yg = smtFunction "yg"
               $ \n -> ite (n .<= 0) 0 (1 + yf (n + 1))
        r <- C.try $ satWith z3{verbose=True, redirectVerbose=Just rf} $
                \x -> yf x .== (x :: SInteger)
        case r of
          Left (e :: C.SomeException) -> appendFile rf ("\nEXCEPTION:\n" ++ show e ++ "\n")
          Right m                     -> appendFile rf ("\nRESULT:\n" ++ show m ++ "\n")

   -- Test 3-way chain with explicit measures: da calls db, db calls dc, dc calls da, all with abs measure.
   , goldenCapturedIO "recursive17_chainMeasure" $ \rf -> do
        let da :: SInteger -> SInteger
            da = smtFunctionWithMeasure "da" (abs, [])
               $ \n -> ite (n .<= 0) 0 (1 + db (n - 1))
            db :: SInteger -> SInteger
            db = smtFunctionWithMeasure "db" (abs, [])
               $ \n -> ite (n .<= 0) 0 (1 + dc (n - 1))
            dc :: SInteger -> SInteger
            dc = smtFunctionWithMeasure "dc" (abs, [])
               $ \n -> ite (n .<= 0) 0 (1 + da (n - 1))
        m <- satWith z3{verbose=True, redirectVerbose=Just rf} $
                \x -> da x .== (x :: SInteger)
        appendFile rf ("\nRESULT:\n" ++ show m ++ "\n")

   -- Test mutual recursion with different arg types: tf takes Integer, tg takes a list.
   -- Auto-guess fails because no single measure applies to both signatures.
   , testCase "diffTypeMutual" $ do
        let tf :: SInteger -> SInteger
            tf = smtFunction "tf" $ \n -> ite (n .<= 0) 0 (1 + tg (L.singleton n))
            tg :: SList Integer -> SInteger
            tg = smtFunction "tg" $ \xs -> ite (L.null xs) 0 (tf (L.head xs - 1))
        r <- C.try $ sat $ \(x :: SInteger) -> tf x .== 0
        case r of
          Left (e :: C.SomeException) -> if "Cannot determine a termination measure" `isInfixOf` show e
                                            then pure ()
                                            else assertFailure $ "Unexpected exception: " ++ show e
          Right _                     -> assertFailure "Expected error for different-type mutual recursion"

   -- Test self-recursive + mutual: sf calls itself AND sg. Both paths should be checked.
   , goldenCapturedIO "recursive19_selfAndMutual" $ \rf -> do
        let sf :: SInteger -> SInteger
            sf = smtFunction "sf" $ \n -> ite (n .<= 0) 0 (sf (n - 1) + sg (n - 1))
            sg :: SInteger -> SInteger
            sg = smtFunction "sg" $ \n -> ite (n .<= 0) 0 (1 + sf (n - 1))
        m <- satWith z3{verbose=True, redirectVerbose=Just rf} $
                \x -> sf x .== (x :: SInteger)
        appendFile rf ("\nRESULT:\n" ++ show m ++ "\n")

   -- Test all-self-recursive mutual group with bad cross-calls:
   -- bf and bg both self-recurse (n-1), but cross-call with (n+1).
   -- Self-recursion checks pass, but mutual group check must catch the bad cross-calls.
   , goldenCapturedIO "recursive21_allSelfBadCross" $ \rf -> do
        let bf :: SInteger -> SInteger
            bf = smtFunction "bf21" $ \n -> ite (n .<= 0) 0 (bf (n - 1) + bg (n + 1))
            bg :: SInteger -> SInteger
            bg = smtFunction "bg21" $ \n -> ite (n .<= 0) 0 (bg (n - 1) + bf (n + 1))
        r <- C.try $ satWith z3{verbose=True, redirectVerbose=Just rf} $
                \x -> bf x .== (x :: SInteger)
        case r of
          Left (e :: C.SomeException) -> appendFile rf ("\nEXCEPTION:\n" ++ show e ++ "\n")
          Right m                     -> appendFile rf ("\nRESULT:\n" ++ show m ++ "\n")

   -- Test all-self-recursive mutual group with good cross-calls and explicit measures:
   -- Both bf and bg self-recurse and cross-call with (n-1). User-provided abs measure works.
   , goldenCapturedIO "recursive22_allSelfGoodCross" $ \rf -> do
        let bf :: SInteger -> SInteger
            bf = smtFunctionWithMeasure "bf22" (abs, []) $ \n -> ite (n .<= 0) 0 (bf (n - 1) + bg (n - 1))
            bg :: SInteger -> SInteger
            bg = smtFunctionWithMeasure "bg22" (abs, []) $ \n -> ite (n .<= 0) 0 (bg (n - 1) + bf (n - 1))
        m <- satWith z3{verbose=True, redirectVerbose=Just rf} $
                \x -> bf x .== (x :: SInteger)
        appendFile rf ("\nRESULT:\n" ++ show m ++ "\n")

   -- Test mutual recursion via TP proofs (exercises checkNewMeasures in Kernel.hs)
   , goldenCapturedIO "recursive20_mutualTP" $ \rf -> do
        let cfg = z3{verbose=True, redirectVerbose=Just rf}
            mf :: SInteger -> SInteger
            mf = smtFunction "mf_tp" $ \n -> ite (n .<= 0) 0 (1 + mg (n - 1))
            mg :: SInteger -> SInteger
            mg = smtFunction "mg_tp" $ \n -> ite (n .<= 0) 0 (1 + mf (n - 1))
        _ <- runTPWith cfg $
                lemma "mutual_at_0"
                      (\(Forall @"n" n) -> n .== 0 .=> mf n .== 0)
                      []
        pure ()
   ]
