-----------------------------------------------------------------------------
-- |
-- Module    : TestSuite.ADT.ADT
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Testing ADTs
-----------------------------------------------------------------------------

{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell     #-}

{-# OPTIONS_GHC -Wall -Werror -Wno-unused-top-binds #-}

module TestSuite.ADT.ADT(tests) where

import Utils.SBVTestFramework
import Data.SBV.Control

data ADT  = AEmpty
          | ABool    Bool
          | AInteger Integer
          | AWord8   (Word8)
          | AWord16  (Word16)
          | AWord32  (Word32)
          | AWord64  (Word64)
          | AInt8    (Int8)
          | AInt16   (Int16)
          | AInt32   (Int32)
          | AInt64   (Int64)
          | AWord1   (WordN  1)
          | AWord5   (WordN  5)
          | AWord30  (WordN 30)
          | AInt1    (IntN   1)
          | AInt5    (IntN   5)
          | AInt30   (IntN  30)
          | AReal    AlgReal
          | AFloat   Float
          | ADouble  Double
          | AFP      (FloatingPoint 5 12)
          | AString  String
          | AList    [Integer]
          | ATuple   (Double, [(WordN 5, [Float])])
          | AMaybe   (Maybe (AlgReal, Float, (Rational, [Bool])))
          | AEither  (Either (Maybe Integer, Bool) [Rational])
          | APair    ADT ADT
          {-
          | KUserSort String (Maybe [String])
          | KADT      String (Maybe [(String, [Kind])])
          | KChar
          | KSet  Kind
          | KArray  Kind Kind
          -}

mkSymbolic ''ADT

tests :: TestTree
tests =
  testGroup "ADT" [
      goldenCapturedIO "adt00" $ checkWith t00
    , goldenCapturedIO "adt01" $ checkWith t01
    , goldenCapturedIO "adt02" $ checkWith t02
    , goldenCapturedIO "adt03" $ checkWith t03
    , goldenCapturedIO "adt04" t04
    , goldenCapturedIO "adt05" t05
    ]

checkWith :: Symbolic () -> FilePath -> IO ()
checkWith props rf = runSMTWith z3{verbose=True, redirectVerbose = Just rf} $ do
        _ <- props
        query $ do cs <- checkSat
                   case cs of
                     Unsat  -> io $ appendFile rf "\nUNSAT"
                     DSat{} -> io $ appendFile rf "\nDSAT"
                     Sat{}  -> getModel         >>= \m -> io $ appendFile rf $ "\nMODEL: "   ++ show m ++ "\nDONE."
                     Unk    -> getUnknownReason >>= \r -> io $ appendFile rf $ "\nUNKNOWN: " ++ show r ++ "\nDONE."

t00 :: Symbolic ()
t00 = do (a :: SADT) <- free "e"
         constrain $ a ./== a

t01 :: Symbolic ()
t01 = do (a :: SADT) <- free "e"
         constrain $ a .=== literal (APair (AInt64 4) (AMaybe (Just (0, 12, (3, [False, True])))))

t02 :: Symbolic ()
t02 = do (a :: SADT) <- free "e"
         constrain $ isAList a

t03 :: Symbolic ()
t03 = do (a :: SADT) <- free "e"
         constrain $ isAList a .&& isAFP a

t04 :: FilePath -> IO ()
t04 rf = do AllSatResult _ _ _ ms <- allSatWith z3{verbose=True, redirectVerbose = Just rf} t
            let sh m = appendFile rf $ "\nMODEL:" ++ show (SatResult m)
            mapM_ sh ms
  where t = do (a :: SADT) <- free "a"
               constrain $ isAInteger a
               constrain $ getAInteger_1 a .>= 0
               constrain $ getAInteger_1 a .<= 5

-- z3 is buggy on this. So we use cvc5. See: https://github.com/Z3Prover/z3/issues/7842
t05 :: FilePath -> IO ()
t05 rf = do AllSatResult _ _ _ ms <- allSatWith cvc5{verbose=True, redirectVerbose = Just rf, allSatMaxModelCount=Just 10} t
            let sh m = appendFile rf $ "\nMODEL:" ++ show (SatResult m)
            mapM_ sh ms
  where t = do (a :: SADT) <- free "a"
               (b :: SADT) <- free "b"
               constrain $ isAFloat a .&& getAFloat_1 a .== 4
               constrain $ isAFloat b .&& fpIsNaN (getAFloat_1 b)
