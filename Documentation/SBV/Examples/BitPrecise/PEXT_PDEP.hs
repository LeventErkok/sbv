-----------------------------------------------------------------------------
-- |
-- Module    : Documentation.SBV.Examples.BitPrecise.PEXT_PDEP
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
--
-- Models the x86 [PEXT](https://www.felixcloutier.com/x86/pext) and [PDEP](https://www.felixcloutier.com/x86/pdep) instructions.
--
-- The pseudo-code implementation given by Intel for PEXT (parallel extract) is:
--
-- @
--    TEMP := SRC1;
--    MASK := SRC2;
--    DEST := 0 ;
--    m := 0, k := 0;
--    DO WHILE m < OperandSize
--        IF MASK[m] = 1 THEN
--            DEST[k] := TEMP[m];
--            k := k+ 1;
--        FI
--        m := m+ 1;
--    OD
-- @
--
-- PDEP (parallel deposit) is similar, except the assigment is:
--
-- @
--    DEST[m] := TEMP[k]
-- @
--
-- In PEXT, we grab the values of the source corresponding to the mask, and pile them into the destination from the bottom. In PDEP, we
-- do the reverse: We distribute the bits from the bottom of the source to the destination according to the mask.
-----------------------------------------------------------------------------

{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE Rank2Types          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications    #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module Documentation.SBV.Examples.BitPrecise.PEXT_PDEP where

import Data.SBV
import GHC.TypeLits (KnownNat)

-- $setup
-- >>> -- For doctest purposes only:
-- >>> import Data.SBV
-- >>> :set -XDataKinds

--------------------------------------------------------------------------------------------------
-- * Parallel extraction
--------------------------------------------------------------------------------------------------

-- | Parallel extraction: Given a source value and a mask, extract the bits in the source that are
-- pointed to by the mask, and put it in the destination starting from the bottom.
--
-- >>> satWith z3{printBase = 16} $ \r -> r .== pext (0xAA :: SWord 8) 0xAA
-- Satisfiable. Model:
--   s0 = 0x0f :: Word8
-- >>> prove $ \x -> pext @8 x 0 .== 0
-- Q.E.D.
-- >>> prove $ \x -> pext @8 x (complement 0) .== x
-- Q.E.D.
pext :: forall n. (KnownNat n, BVIsNonZero n) => SWord n -> SWord n -> SWord n
pext src mask = walk 0 src 0 (blastLE mask)
  where walk dest _ _   []     = dest
        walk dest x idx (m:ms) = walk (ite m (sSetBitTo dest idx (lsb x)) dest)
                                      (x `shiftR` 1)
                                      (ite m (idx + 1) idx)
                                      ms

--------------------------------------------------------------------------------------------------
-- * Parallel deposit
--------------------------------------------------------------------------------------------------

-- | Parallel deposit: Given a source value and a mask, write into the destination that are
-- allowed by the mask, grabbing the bits from the source starting from the bottom.
--
-- >>> satWith z3{printBase = 16} $ \r -> r .== pdep (0xFF :: SWord 8) 0xAA
-- Satisfiable. Model:
--   s0 = 0xaa :: Word8
-- >>> prove $ \x -> pdep @8 x 0 .== 0
-- Q.E.D.
-- >>> prove $ \x -> pdep @8 x (complement 0) .== x
-- Q.E.D.
pdep :: forall n. (KnownNat n, BVIsNonZero n) => SWord n -> SWord n -> SWord n
pdep src mask = walk 0 src 0 (blastLE mask)
  where walk dest _ _   []     = dest
        walk dest x idx (m:ms) = walk (ite m (sSetBitTo dest idx (lsb x)) dest)
                                      (ite m (x `shiftR` 1) x)
                                      (idx + 1)
                                      ms
--------------------------------------------------------------------------------------------------
-- * Round-trip property
--------------------------------------------------------------------------------------------------

-- | Prove that extraction and depositing with the same mask restore the source in all masked positions:
--
-- >>> extractThenDeposit
-- Q.E.D.
extractThenDeposit :: IO ThmResult
extractThenDeposit = prove $ do x :: SWord 8 <- sWord "x"
                                m :: SWord 8 <- sWord "m"
                                pure $ (x .&. m) .== pdep (pext x m) m

-- | Prove that depositing and extracting with the same mask will push preserve the bottom
-- n-bits of the source, where n is the number of bits set in the mask.
--
-- >>> depositThenExtract
-- Q.E.D.
depositThenExtract :: IO ThmResult
depositThenExtract = prove $ do x :: SWord 8 <- sWord "x"
                                m :: SWord 8 <- sWord "m"
                                let preserved = 2 .^ sPopCount m - 1
                                pure $ (x .&. preserved) .== pext (pdep x m) m

--------------------------------------------------------------------------------------------------
-- * Code generation
--------------------------------------------------------------------------------------------------

-- | We can generate the code for these functions if they need to be used in SMTLib. Below
-- is an example at 2-bits, which can be adjusted to produce any bit-size.
--
-- >>> putStrLn =<< sbv2smt pext_2
-- ; Automatically generated by SBV. Do not modify!
-- ; pext_2 :: SWord 2 -> SWord 2 -> SWord 2
-- (define-fun pext_2 ((l1_s0 (_ BitVec 2)) (l1_s1 (_ BitVec 2))) (_ BitVec 2)
--   (let ((l1_s3 #b0))
--   (let ((l1_s7 #b01))
--   (let ((l1_s8 #b00))
--   (let ((l1_s20 #b10))
--   (let ((l1_s2 ((_ extract 1 1) l1_s1)))
--   (let ((l1_s4 (distinct l1_s2 l1_s3)))
--   (let ((l1_s5 ((_ extract 0 0) l1_s1)))
--   (let ((l1_s6 (distinct l1_s3 l1_s5)))
--   (let ((l1_s9 (ite l1_s6 l1_s7 l1_s8)))
--   (let ((l1_s10 (= l1_s7 l1_s9)))
--   (let ((l1_s11 (bvlshr l1_s0 l1_s7)))
--   (let ((l1_s12 ((_ extract 0 0) l1_s11)))
--   (let ((l1_s13 (distinct l1_s3 l1_s12)))
--   (let ((l1_s14 (= l1_s8 l1_s9)))
--   (let ((l1_s15 ((_ extract 0 0) l1_s0)))
--   (let ((l1_s16 (distinct l1_s3 l1_s15)))
--   (let ((l1_s17 (ite l1_s16 l1_s7 l1_s8)))
--   (let ((l1_s18 (ite l1_s6 l1_s17 l1_s8)))
--   (let ((l1_s19 (bvor l1_s7 l1_s18)))
--   (let ((l1_s21 (bvand l1_s18 l1_s20)))
--   (let ((l1_s22 (ite l1_s13 l1_s19 l1_s21)))
--   (let ((l1_s23 (ite l1_s14 l1_s22 l1_s18)))
--   (let ((l1_s24 (bvor l1_s20 l1_s23)))
--   (let ((l1_s25 (bvand l1_s7 l1_s23)))
--   (let ((l1_s26 (ite l1_s13 l1_s24 l1_s25)))
--   (let ((l1_s27 (ite l1_s10 l1_s26 l1_s23)))
--   (let ((l1_s28 (ite l1_s4 l1_s27 l1_s18)))
--   l1_s28))))))))))))))))))))))))))))
pext_2 :: SWord 2 -> SWord 2 -> SWord 2
pext_2 = smtFunction "pext_2" (pext @2)
