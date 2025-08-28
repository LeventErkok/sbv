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
      goldenCapturedIO "adt00" $ \rf -> checkWith rf t00
    ]

checkWith :: FilePath -> Symbolic () -> IO ()
checkWith rf props = runSMTWith z3{verbose=True, redirectVerbose = Just rf} $ do
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
