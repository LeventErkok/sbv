-----------------------------------------------------------------------------
-- |
-- Module    : Documentation.SBV.Examples.TP.AES
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Compositional proofs for the implementation in
-- "Documentation.SBV.Examples.Crypto.AES". The implementation is imported
-- unchanged; shift/XOR descriptions of column mixing are proof intermediates,
-- connected to its lookup tables by checked equivalence lemmas.
--
-- The `aes128Correct` theorem proves the existing 'AES.aes128IsCorrect' predicate for
-- every plaintext and key. It covers ordinary AES-128 decryption, not the on-the-fly
-- path or the other key sizes. The result is a round-trip theorem, not a conformance or
-- cryptographic-security proof.
--
-- The proof proceeds from byte identities through table equivalence and
-- column linearity to cancellation of one middle round. It then follows the
-- original encryption/decryption traces, cancelling the nine middle rounds
-- in reverse order and handling the initial/final key additions separately.
-----------------------------------------------------------------------------

{-# LANGUAGE CPP                 #-}
{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeAbstractions    #-}
{-# LANGUAGE TypeApplications    #-}

{-# OPTIONS_GHC -Wall -Werror -Wno-incomplete-uni-patterns -Wno-x-partial #-}

module Documentation.SBV.Examples.TP.AES where

import Control.Monad (foldM)

import Data.SBV
import Data.SBV.TP
import Data.SBV.Tuple (tuple, untuple)

import qualified Documentation.SBV.Examples.Crypto.AES as AES

#ifdef DOCTEST
-- $setup
-- >>> import Data.SBV
-- >>> import Data.SBV.TP
#endif

-----------------------------------------------------------------------------
-- * States and theorem types
-----------------------------------------------------------------------------

-- | A universally quantified property of a packed 128-bit state.
type BlockProperty = Forall "s" (WordN 128) -> SBool

-- | A universally quantified property of a state and one round key.
type RoundProperty = Forall "s" (WordN 128) -> Forall "k" (WordN 128) -> SBool

-- | The AES-128 round-trip property, quantified over plaintexts and keys.
type AES128Property = Forall "pt" (WordN 128) -> Forall "key" (WordN 128) -> SBool

-- | Four original words, used only to instantiate packing lemmas. The AES
-- computation itself continues to use its original Haskell lists.
type Block = (WordN 32, WordN 32, WordN 32, WordN 32)

-- | A property of a state and round key in the four-word representation.
type BlockLaw = Forall "s" Block -> Forall "k" Block -> SBool

-- | Split a packed state into its four words, most significant word first.
wordsOf :: SWord 128 -> [SWord 32]
wordsOf = map fromBytes . AES.chop4 . toBytes

-- | Pack exactly four words into one state. Packing and splitting are inverses:
--
-- >>> prove $ \s -> packWords (wordsOf s) .== s
-- Q.E.D.
packWords :: [SWord 32] -> SWord 128
packWords [a, b, c, d] = a # b # c # d
packWords _            = error "AES proof: expected four words"

-- | Turn exactly four host-list elements into a symbolic tuple for instantiation.
toBlock :: [SWord 32] -> SBV Block
toBlock [a, b, c, d] = tuple (a, b, c, d)
toBlock _            = error "AES proof: expected four words"

-- | Recover the four host-list elements of a symbolic tuple.
fromBlock :: SBV Block -> [SWord 32]
fromBlock t = [a, b, c, d]
  where (a, b, c, d) = untuple t

-----------------------------------------------------------------------------
-- * Field arithmetic and column mixing
-----------------------------------------------------------------------------

-- | The constant field-multiplication tables used by the implementation.
tableMul :: AES.GF28 -> AES.GF28 -> AES.GF28
tableMul k = select [AES.gf28Mult k (literal x) | x <- [0 .. 255]] 0

-- | A proof-friendly description of multiplication by a constant byte.
-- Each @xtime@ doubles in GF(2^8), reducing by the low eight bits of @0x11b@.
-- 'roundLemmas' connects this description to the original lookup tables.
--
-- >>> unliteral (multiplyByte 0x13 0x57) == Just 0xfe
-- True
multiplyByte :: WordN 8 -> SWord 8 -> SWord 8
multiplyByte k x = foldr xor 0 [v | (i, v) <- zip [0 .. 7] (iterate xtime x), testBit k i]
  where xtime :: SWord 8 -> SWord 8
        xtime b = (b `shiftL` 1) `xor` ite (sTestBit b 7) 0x1b 0

-- | Mix one column by XORing the contributions of its four bytes.
mixColumn :: SWord 32 -> SWord 32
mixColumn w = foldr xor 0 (zipWith mixContribution [0 .. 3] (toBytes w))

-- | Inverse column mixing, with the same contribution-by-contribution layout.
inverseMixColumn :: SWord 32 -> SWord 32
inverseMixColumn w = foldr xor 0 (zipWith inverseMixContribution [0 .. 3] (toBytes w))

-- | One byte's contribution to a forward column, rotated into its row position.
mixContribution :: Int -> SWord 8 -> SWord 32
mixContribution i x = fromBytes $ rotateBytes [multiplyByte 2 x, x, x, multiplyByte 3 x] i

-- | One byte's contribution to an inverse column, rotated into its row position.
inverseMixContribution :: Int -> SWord 8 -> SWord 32
inverseMixContribution i x = fromBytes $ rotateBytes [ multiplyByte 14 x
                                                    , multiplyByte  9 x
                                                    , multiplyByte 13 x
                                                    , multiplyByte 11 x
                                                    ] i

-- | Rotate a column's four bytes right by zero, one, two, or three positions.
rotateBytes :: [SWord 8] -> Int -> [SWord 8]
rotateBytes xs 0 = xs
rotateBytes xs i = AES.rotR xs i

-- | Extract the sole column returned by a one-column transformation.
singleWord :: [SWord 32] -> SWord 32
singleWord [w] = w
singleWord _   = error "AES proof: expected one column"

-- | Combine column contributions by XOR.
xorWords :: [SWord 32] -> SWord 32
xorWords = foldr xor 0

-----------------------------------------------------------------------------
-- * Packed views of the original AES operations
-----------------------------------------------------------------------------

-- | SubBytes followed by ShiftRows: a final encryption round with a zero key.
subShift :: SWord 128 -> SWord 128
subShift s = packWords $ AES.aesRound True (wordsOf s) (replicate 4 0)

-- | Inverse SubBytes/ShiftRows: a final decryption round with a zero key.
inverseSubShift :: SWord 128 -> SWord 128
inverseSubShift s = packWords $ AES.aesInvRound True (wordsOf s) (replicate 4 0)

-- | Apply the arithmetic column-mixing description to all four columns.
mixState :: SWord 128 -> SWord 128
mixState = packWords . map mixColumn . wordsOf

-- | Apply the arithmetic inverse-column description to all four columns.
inverseMixState :: SWord 128 -> SWord 128
inverseMixState = packWords . map inverseMixColumn . wordsOf

-- | The original T-box encryption round, with a packed state and key.
encryptRound :: SWord 128 -> SWord 128 -> SWord 128
encryptRound s k = packWords $ AES.aesRound False (wordsOf s) (wordsOf k)

-- | The original T-box decryption round, with a packed state and key.
decryptRound :: SWord 128 -> SWord 128 -> SWord 128
decryptRound s k = packWords $ AES.aesInvRound False (wordsOf s) (wordsOf k)

-- | The original final encryption round, which omits column mixing.
encryptFinalRound :: SWord 128 -> SWord 128 -> SWord 128
encryptFinalRound s k = packWords $ AES.aesRound True (wordsOf s) (wordsOf k)

-- | The original final decryption round, which omits inverse column mixing.
decryptFinalRound :: SWord 128 -> SWord 128 -> SWord 128
decryptFinalRound s k = packWords $ AES.aesInvRound True (wordsOf s) (wordsOf k)

-- | The implementation's table-based inverse mixing, used on decryption keys.
originalInverseMixState :: SWord 128 -> SWord 128
originalInverseMixState = packWords . AES.invMixColumns . wordsOf

-----------------------------------------------------------------------------
-- * Component lemmas and middle-round cancellation
-----------------------------------------------------------------------------

-- | Establish inverse SubBytes/ShiftRows and the middle-round cancellation law.
-- Two table-equivalence calculations use CVC5; the remaining checks use the
-- solver selected by 'runTP'. Small congruence lemmas let later calculations
-- apply a known equality inside a large cipher expression without asking the
-- solver to rediscover it by bit-blasting that expression.
roundLemmas :: TP (Proof BlockProperty, Proof RoundProperty)
roundLemmas = do
  sboxInverse <- lemma "AES.byteInverse"
    (\(Forall @"x" x) -> AES.sboxInverseCorrect x) []

  subShiftInverse <- calc "AES.subShiftInverse"
    (\(Forall @"s" s) -> inverseSubShift (subShift s) .== s) $ \s ->
    [] |- inverseSubShift (subShift s)
       ?? [sboxInverse `at` Inst @"x" x | x <- toBytes s]
       =: s
       =: qed

  -- Connect the implementation's inverse-mixing tables to field arithmetic.
  inverseTableEquivalence <- lemma "AES.inverseTablesFast"
    (\(Forall @"x" x) -> sAnd
     [tableMul (literal k) x .== multiplyByte k x | k <- [9, 11, 13, 14]]) []

  inverseColumnEquivalence <- calcWith cvc5 "AES.inverseMixColumnBridge"
    (\(Forall @"w" w) ->
       singleWord (AES.invMixColumns [w]) .== inverseMixColumn w) $ \w ->
    [] |- singleWord (AES.invMixColumns [w])
       ?? [inverseTableEquivalence `at` Inst @"x" x | x <- toBytes w]
       =: inverseMixColumn w
       =: qed

  inverseStateEquivalence <- calc "AES.inverseMixBridge"
    (\(Forall @"s" s) -> originalInverseMixState s .== inverseMixState s) $ \s ->
    [] |- originalInverseMixState s
       ?? [inverseColumnEquivalence `at` Inst @"w" w | w <- wordsOf s]
       =: inverseMixState s
       =: qed

  -- Prove the inverse law on one column, then lift it to the state.
  columnInverse <- lemma "AES.mixColumnFastInverse"
    (\(Forall @"w" w) -> inverseMixColumn (mixColumn w) .== w) []

  stateInverse <- calc "AES.mixStateInverse"
    (\(Forall @"s" s) -> inverseMixState (mixState s) .== s) $ \s ->
    [] |- inverseMixState (mixState s)
       ?? [columnInverse `at` Inst @"w" w | w <- wordsOf s]
       =: s
       =: qed

  -- Lift byte-contribution linearity to columns, then to the entire state.
  contributionLinear <- lemma "AES.inverseMixTermLinear"
    (\(Forall @"x" x) (Forall @"y" y) -> sAnd
      [inverseMixContribution i (x `xor` y) .== (inverseMixContribution i x `xor` inverseMixContribution i y) | i <- [0 .. 3]]) []

  xorShuffle <- lemma "AES.xorShuffle4"
    (\(Forall @"s" s) (Forall @"t" t) ->
       xorWords (zipWith xor (wordsOf s) (wordsOf t)) .==
       (xorWords (wordsOf s) `xor` xorWords (wordsOf t))) []

  columnLinear <- calc "AES.inverseMixWordLinear"
    (\(Forall @"w" w) (Forall @"v" v) -> inverseMixColumn (w `xor` v) .== (inverseMixColumn w `xor` inverseMixColumn v)) $ \w v ->
    let ts :: SWord 32 -> [SWord 32]
        ts q = zipWith inverseMixContribution [0 .. 3] (toBytes q)

        [a, b, c, d] = ts w
        [e, f, g, h] = ts v
    in [] |- inverseMixColumn (w `xor` v)
          ?? [contributionLinear `at` (Inst @"x" x, Inst @"y" y) | (x, y) <- zip (toBytes w) (toBytes v)]
          =: xorWords [a `xor` e, b `xor` f, c `xor` g, d `xor` h]
          ?? xorShuffle `at` (Inst @"s" (packWords [a, b, c, d]), Inst @"t" (packWords [e, f, g, h]))
          =: (inverseMixColumn w `xor` inverseMixColumn v)
          =: qed

  stateLinear <- calc "AES.inverseMixLinear"
    (\(Forall @"s" s) (Forall @"k" k) ->
       inverseMixState (s `xor` k) .== (inverseMixState s `xor` inverseMixState k)) $ \s k ->
    [] |- inverseMixState (s `xor` k)
       ?? [columnLinear `at` (Inst @"w" w, Inst @"v" v) | (w, v) <- zip (wordsOf s) (wordsOf k)]
       =: (inverseMixState s `xor` inverseMixState k)
       =: qed

  -- Connect both original T-box round functions to the arithmetic view.
  encryptionTableEquivalence <- lemma "AES.forwardTBoxes"
    (\(Forall @"x" x) ->
    let y  = AES.sbox x
        bs = [multiplyByte 2 y, y, y, multiplyByte 3 y]
    in sAnd [ AES.t0 x .== fromBytes bs
            , AES.t1 x .== fromBytes (AES.rotR bs 1)
            , AES.t2 x .== fromBytes (AES.rotR bs 2)
            , AES.t3 x .== fromBytes (AES.rotR bs 3)
            ]) []

  encryptionRoundEquivalence <- calc "AES.encryptionRoundBridge"
    (\(Forall @"s" s) (Forall @"k" k) ->
       encryptRound s k .== (mixState (subShift s) `xor` k)) $ \s k ->
    [] |- encryptRound s k
       ?? [encryptionTableEquivalence `at` Inst @"x" x | x <- toBytes s]
       =: (mixState (subShift s) `xor` k)
       =: qed

  decryptionTableEquivalence <- lemma "AES.inverseTBoxes"
    (\(Forall @"x" x) ->
    let y  = AES.unSBox x
        bs = [multiplyByte 14 y, multiplyByte 9 y, multiplyByte 13 y, multiplyByte 11 y]
    in sAnd [ AES.u0 x .== fromBytes bs
            , AES.u1 x .== fromBytes (AES.rotR bs 1)
            , AES.u2 x .== fromBytes (AES.rotR bs 2)
            , AES.u3 x .== fromBytes (AES.rotR bs 3)
            ]) []

  decryptionRoundEquivalence <- calcWith cvc5 "AES.decryptionRoundBridge"
    (\(Forall @"s" s) (Forall @"k" k) ->
       decryptRound s k .== (inverseMixState (inverseSubShift s) `xor` k)) $ \s k ->
    [] |- decryptRound s k
       ?? [decryptionTableEquivalence `at` Inst @"x" x | x <- toBytes s]
       =: (inverseMixState (inverseSubShift s) `xor` k)
       =: qed

  -- Congruence steps carry established equalities through cipher expressions.
  decryptKeyCongruence <- lemma "AES.decryptKeyCongruence"
    (\(Forall @"s" s) (Forall @"k" k) (Forall @"j" j) ->
       k .== j .=> decryptRound s k .== decryptRound s j) []

  inverseMixXorCongruence <- lemma "AES.inverseMixXorCongruence"
    (\(Forall @"s" s) (Forall @"t" t) (Forall @"k" k) ->
       s .== t .=> (inverseMixState s `xor` k) .== (inverseMixState t `xor` k)) []

  xorCongruence <- lemma "AES.xorCongruence"
    (\(Forall @"s" (s :: SWord 128)) (Forall @"t" t) (Forall @"k" k) ->
       s .== t .=> (s `xor` k) .== (t `xor` k)) []

  xorCancellation <- lemma "AES.xorCancellation"
    (\(Forall @"s" (s :: SWord 128)) (Forall @"k" k) ->
       (s `xor` k `xor` k) .== s) []

  -- The invariant between paired rounds is SubBytes/ShiftRows of the
  -- corresponding forward state, rather than the forward state itself.
  middleCancellation <- calc "AES.middleRoundCancellation"
    (\(Forall @"s" s) (Forall @"k" k) ->
       decryptRound (subShift (encryptRound s k)) (originalInverseMixState k) .== subShift s) $ \s k ->
    [] |- decryptRound (subShift (encryptRound s k)) (originalInverseMixState k)
       ?? inverseStateEquivalence `at` Inst @"s" k
       ?? decryptKeyCongruence `at`
          ( Inst @"s" (subShift (encryptRound s k))
          , Inst @"k" (originalInverseMixState k)
          , Inst @"j" (inverseMixState k)
          )
       =: decryptRound (subShift (encryptRound s k)) (inverseMixState k)
       ?? decryptionRoundEquivalence `at` (Inst @"s" (subShift (encryptRound s k)), Inst @"k" (inverseMixState k))
       =: (inverseMixState (inverseSubShift (subShift (encryptRound s k))) `xor` inverseMixState k)
       ?? subShiftInverse `at` Inst @"s" (encryptRound s k)
       ?? inverseMixXorCongruence `at`
          ( Inst @"s" (inverseSubShift (subShift (encryptRound s k)))
          , Inst @"t" (encryptRound s k)
          , Inst @"k" (inverseMixState k)
          )
       =: (inverseMixState (encryptRound s k) `xor` inverseMixState k)
       ?? encryptionRoundEquivalence `at` (Inst @"s" s, Inst @"k" k)
       ?? inverseMixXorCongruence `at`
          ( Inst @"s" (encryptRound s k)
          , Inst @"t" (mixState (subShift s) `xor` k)
          , Inst @"k" (inverseMixState k)
          )
       =: (inverseMixState (mixState (subShift s) `xor` k) `xor` inverseMixState k)
       ?? stateLinear `at` (Inst @"s" (mixState (subShift s)), Inst @"k" k)
       ?? xorCongruence `at`
          ( Inst @"s" (inverseMixState (mixState (subShift s) `xor` k))
          , Inst @"t" (inverseMixState (mixState (subShift s)) `xor` inverseMixState k)
          , Inst @"k" (inverseMixState k)
          )
       =: (inverseMixState (mixState (subShift s)) `xor` inverseMixState k `xor` inverseMixState k)
       ?? xorCancellation `at` (Inst @"s" (inverseMixState (mixState (subShift s))), Inst @"k" (inverseMixState k))
       =: inverseMixState (mixState (subShift s))
       ?? stateInverse `at` Inst @"s" (subShift s)
       =: subShift s
       =: qed

  pure (subShiftInverse, middleCancellation)

-- | Prove middle-round cancellation for every state and round key. The state
-- between the rounds includes SubBytes/ShiftRows; the decryption key is the
-- inverse-mixed encryption key, exactly as in 'AES.aesKeySchedule'.
roundCancellation :: TP (Proof RoundProperty)
roundCancellation = snd <$> roundLemmas

-----------------------------------------------------------------------------
-- * Connecting packed proofs to the four-word implementation
-----------------------------------------------------------------------------

-- | Packing is only a proof interface. These equations keep every round tied
-- to the original four-word implementation and make the representation
-- changes explicit even when their arguments contain many earlier rounds.
packingLemmas :: TP ( Proof BlockLaw                      -- Middle encryption round
                    , Proof BlockLaw                      -- Middle decryption round
                    , Proof BlockLaw                      -- Final encryption round
                    , Proof BlockLaw                      -- Final decryption round
                    , Proof BlockLaw                      -- Key addition
                    , Proof (Forall "s" Block -> SBool)   -- Inverse column mixing
                    )
packingLemmas = do
  encryptPacking <- lemma "AES.packEncryptionRound"
    (\(Forall s) (Forall k) ->
       packWords (AES.aesRound False (fromBlock s) (fromBlock k))
       .== encryptRound (packWords (fromBlock s)) (packWords (fromBlock k))) []

  decryptPacking <- lemma "AES.packDecryptionRound"
    (\(Forall s) (Forall k) ->
       packWords (AES.aesInvRound False (fromBlock s) (fromBlock k))
       .== decryptRound (packWords (fromBlock s)) (packWords (fromBlock k))) []

  finalEncryptPacking <- lemma "AES.packFinalEncryptionRound"
    (\(Forall s) (Forall k) ->
       packWords (AES.aesRound True (fromBlock s) (fromBlock k))
       .== encryptFinalRound (packWords (fromBlock s)) (packWords (fromBlock k))) []

  finalDecryptPacking <- lemma "AES.packFinalDecryptionRound"
    (\(Forall s) (Forall k) ->
       packWords (AES.aesInvRound True (fromBlock s) (fromBlock k))
       .== decryptFinalRound (packWords (fromBlock s)) (packWords (fromBlock k))) []

  addKeyPacking <- lemma "AES.packAddRoundKey"
    (\(Forall s) (Forall k) ->
       packWords (AES.addRoundKey (fromBlock k) (fromBlock s))
       .== (packWords (fromBlock s) `xor` packWords (fromBlock k))) []

  inverseMixPacking <- lemma "AES.packInverseMix"
    (\(Forall s) ->
       packWords (AES.invMixColumns (fromBlock s)) .== originalInverseMixState (packWords (fromBlock s))) []

  pure (encryptPacking, decryptPacking, finalEncryptPacking, finalDecryptPacking, addKeyPacking, inverseMixPacking)

-----------------------------------------------------------------------------
-- * Following the encryption and decryption traces
-----------------------------------------------------------------------------

-- | The original implementation's forward states and reverse states. Keeping
-- the host-list representation here is important: repeatedly packing/unpacking
-- the state between rounds builds a much larger symbolic expression. Both
-- traces are nonempty: each scan includes its initial state, so the proof can
-- use 'head' and 'last' on them.
aesTrace :: SWord 128 -> SWord 128 -> ([AES.State], [AES.State], [AES.Key], AES.Key, AES.Key)
aesTrace pt key = (es, ds, middle, first, lastKey)
  where (encKS@(first, middle, lastKey), _) = AES.aesKeySchedule (wordsOf key)
        es                                  = scanl (AES.aesRound False) (AES.addRoundKey first (wordsOf pt)) middle
        ct                                  = AES.aesEncrypt (wordsOf pt) encKS
        ds                                  = scanl (\s k -> AES.aesInvRound False s (AES.invMixColumns k)) (AES.addRoundKey lastKey ct) (reverse middle)

-- | Run the original AES-128 encryptor and decryptor with their original schedules.
aesResult :: SWord 128 -> SWord 128 -> AES.State
aesResult pt key = AES.aesDecrypt (AES.aesEncrypt (wordsOf pt) encKS) decKS
  where (encKS, decKS) = AES.aesKeySchedule (wordsOf key)

-- | Packed-state version of the round-trip theorem. The invariant after
-- @n@ middle decryption rounds equates the reverse state to 'subShift' of
-- forward state @9 - n@. The base case removes the final encryption key;
-- each successive calculation uses the middle-round cancellation lemma.
-- The last calculation removes the initial encryption key. Both Z3 and CVC5
-- must be installed.
--
-- >>> runTP aes128PackedCorrect
-- Lemma: AES.byteInverse                      Q.E.D.
-- Lemma: AES.subShiftInverse
--   Step: 1                                   Q.E.D.
--   Result:                                   Q.E.D.
-- Lemma: AES.inverseTablesFast                Q.E.D.
-- Lemma: AES.inverseMixColumnBridge
--   Step: 1                                   Q.E.D.
--   Result:                                   Q.E.D.
-- Lemma: AES.inverseMixBridge
--   Step: 1                                   Q.E.D.
--   Result:                                   Q.E.D.
-- Lemma: AES.mixColumnFastInverse             Q.E.D.
-- Lemma: AES.mixStateInverse
--   Step: 1                                   Q.E.D.
--   Result:                                   Q.E.D.
-- Lemma: AES.inverseMixTermLinear             Q.E.D.
-- Lemma: AES.xorShuffle4                      Q.E.D.
-- Lemma: AES.inverseMixWordLinear
--   Step: 1                                   Q.E.D.
--   Step: 2                                   Q.E.D.
--   Result:                                   Q.E.D.
-- Lemma: AES.inverseMixLinear
--   Step: 1                                   Q.E.D.
--   Result:                                   Q.E.D.
-- Lemma: AES.forwardTBoxes                    Q.E.D.
-- Lemma: AES.encryptionRoundBridge
--   Step: 1                                   Q.E.D.
--   Result:                                   Q.E.D.
-- Lemma: AES.inverseTBoxes                    Q.E.D.
-- Lemma: AES.decryptionRoundBridge
--   Step: 1                                   Q.E.D.
--   Result:                                   Q.E.D.
-- Lemma: AES.decryptKeyCongruence             Q.E.D.
-- Lemma: AES.inverseMixXorCongruence          Q.E.D.
-- Lemma: AES.xorCongruence                    Q.E.D.
-- Lemma: AES.xorCancellation                  Q.E.D.
-- Lemma: AES.middleRoundCancellation
--   Step: 1                                   Q.E.D.
--   Step: 2                                   Q.E.D.
--   Step: 3                                   Q.E.D.
--   Step: 4                                   Q.E.D.
--   Step: 5                                   Q.E.D.
--   Step: 6                                   Q.E.D.
--   Step: 7                                   Q.E.D.
--   Result:                                   Q.E.D.
-- Lemma: AES.packEncryptionRound              Q.E.D.
-- Lemma: AES.packDecryptionRound              Q.E.D.
-- Lemma: AES.packFinalEncryptionRound         Q.E.D.
-- Lemma: AES.packFinalDecryptionRound         Q.E.D.
-- Lemma: AES.packAddRoundKey                  Q.E.D.
-- Lemma: AES.packInverseMix                   Q.E.D.
-- Lemma: AES.aesXorCongruence                 Q.E.D.
-- Lemma: AES.aesXorCancel                     Q.E.D.
-- Lemma: AES.finalEncryptionDefinition        Q.E.D.
-- Lemma: AES.finalDecryptionDefinition        Q.E.D.
-- Lemma: AES.initialDecryptionCancellation
--   Step: 1                                   Q.E.D.
--   Step: 2                                   Q.E.D.
--   Result:                                   Q.E.D.
-- Lemma: AES.finalDecryptionCancellation
--   Step: 1                                   Q.E.D.
--   Step: 2                                   Q.E.D.
--   Result:                                   Q.E.D.
-- Lemma: AES.aesDecryptKeyCongruence          Q.E.D.
-- Lemma: AES.aesDecryptStateCongruence        Q.E.D.
-- Lemma: AES.aesDecryptSubShiftCongruence     Q.E.D.
-- Lemma: AES.aesFinalStateCongruence          Q.E.D.
-- Lemma: aes128Prefix0
--   Step: 1                                   Q.E.D.
--   Step: 2                                   Q.E.D.
--   Step: 3                                   Q.E.D.
--   Result:                                   Q.E.D.
-- Lemma: aes128Prefix1
--   Step: 1                                   Q.E.D.
--   Step: 2                                   Q.E.D.
--   Step: 3                                   Q.E.D.
--   Step: 4                                   Q.E.D.
--   Step: 5                                   Q.E.D.
--   Result:                                   Q.E.D.
-- Lemma: aes128Prefix2
--   Step: 1                                   Q.E.D.
--   Step: 2                                   Q.E.D.
--   Step: 3                                   Q.E.D.
--   Step: 4                                   Q.E.D.
--   Step: 5                                   Q.E.D.
--   Result:                                   Q.E.D.
-- Lemma: aes128Prefix3
--   Step: 1                                   Q.E.D.
--   Step: 2                                   Q.E.D.
--   Step: 3                                   Q.E.D.
--   Step: 4                                   Q.E.D.
--   Step: 5                                   Q.E.D.
--   Result:                                   Q.E.D.
-- Lemma: aes128Prefix4
--   Step: 1                                   Q.E.D.
--   Step: 2                                   Q.E.D.
--   Step: 3                                   Q.E.D.
--   Step: 4                                   Q.E.D.
--   Step: 5                                   Q.E.D.
--   Result:                                   Q.E.D.
-- Lemma: aes128Prefix5
--   Step: 1                                   Q.E.D.
--   Step: 2                                   Q.E.D.
--   Step: 3                                   Q.E.D.
--   Step: 4                                   Q.E.D.
--   Step: 5                                   Q.E.D.
--   Result:                                   Q.E.D.
-- Lemma: aes128Prefix6
--   Step: 1                                   Q.E.D.
--   Step: 2                                   Q.E.D.
--   Step: 3                                   Q.E.D.
--   Step: 4                                   Q.E.D.
--   Step: 5                                   Q.E.D.
--   Result:                                   Q.E.D.
-- Lemma: aes128Prefix7
--   Step: 1                                   Q.E.D.
--   Step: 2                                   Q.E.D.
--   Step: 3                                   Q.E.D.
--   Step: 4                                   Q.E.D.
--   Step: 5                                   Q.E.D.
--   Result:                                   Q.E.D.
-- Lemma: aes128Prefix8
--   Step: 1                                   Q.E.D.
--   Step: 2                                   Q.E.D.
--   Step: 3                                   Q.E.D.
--   Step: 4                                   Q.E.D.
--   Step: 5                                   Q.E.D.
--   Result:                                   Q.E.D.
-- Lemma: aes128Prefix9
--   Step: 1                                   Q.E.D.
--   Step: 2                                   Q.E.D.
--   Step: 3                                   Q.E.D.
--   Step: 4                                   Q.E.D.
--   Step: 5                                   Q.E.D.
--   Result:                                   Q.E.D.
-- Lemma: aes128PackedCorrect
--   Step: 1                                   Q.E.D.
--   Step: 2                                   Q.E.D.
--   Step: 3                                   Q.E.D.
--   Step: 4                                   Q.E.D.
--   Step: 5                                   Q.E.D.
--   Result:                                   Q.E.D.
-- [Proven] aes128PackedCorrect :: Ɐpt ∷ (WordN 128) → Ɐkey ∷ (WordN 128) → Bool
aes128PackedCorrect :: TP (Proof AES128Property)
aes128PackedCorrect = do
  (subShiftInverse, middleCancellation) <- roundLemmas
  (encryptPacking, decryptPacking, finalEncryptPacking, finalDecryptPacking, addKeyPacking, inverseMixPacking) <- packingLemmas

  xorCongruence <- lemma "AES.aesXorCongruence"
    (\(Forall @"s" (s :: SWord 128)) (Forall @"t" t) (Forall @"k" k) ->
       s .== t .=> (s `xor` k) .== (t `xor` k)) []

  xorCancellation <- lemma "AES.aesXorCancel"
    (\(Forall @"s" (s :: SWord 128)) (Forall @"k" k) ->
       (s `xor` k `xor` k) .== s) []

  finalEncryptDefinition <- lemma "AES.finalEncryptionDefinition"
    (\(Forall @"s" s) (Forall @"k" k) ->
       encryptFinalRound s k .== (subShift s `xor` k)) []

  finalDecryptDefinition <- lemma "AES.finalDecryptionDefinition"
    (\(Forall @"s" s) (Forall @"k" k) ->
       decryptFinalRound s k .== (inverseSubShift s `xor` k)) []

  initial <- calc "AES.initialDecryptionCancellation"
    (\(Forall @"s" s) (Forall @"k" k) ->
       (encryptFinalRound s k `xor` k) .== subShift s) $ \s k ->
       [] |- (encryptFinalRound s k `xor` k)
          ?? finalEncryptDefinition `at` (Inst @"s" s, Inst @"k" k)
          ?? xorCongruence `at` (Inst @"s" (encryptFinalRound s k), Inst @"t" (subShift s `xor` k), Inst @"k" k)
          =: (subShift s `xor` k `xor` k)
          ?? xorCancellation `at` (Inst @"s" (subShift s), Inst @"k" k)
          =: subShift s
          =: qed

  final <- calc "AES.finalDecryptionCancellation"
    (\(Forall @"s" s) (Forall @"k" k) ->
       decryptFinalRound (subShift s) k .== (s `xor` k)) $ \s k ->
       [] |- decryptFinalRound (subShift s) k
          ?? finalDecryptDefinition `at` (Inst @"s" (subShift s), Inst @"k" k)
          =: (inverseSubShift (subShift s) `xor` k)
          ?? subShiftInverse `at` Inst @"s" s
          ?? xorCongruence `at` (Inst @"s" (inverseSubShift (subShift s)), Inst @"t" s, Inst @"k" k)
          =: (s `xor` k)
          =: qed

  keyCongruence <- lemma "AES.aesDecryptKeyCongruence"
    (\(Forall @"s" s) (Forall @"k" k) (Forall @"j" j) ->
       k .== j .=> decryptRound s k .== decryptRound s j) []

  stateCongruence <- lemma "AES.aesDecryptStateCongruence"
    (\(Forall @"s" s) (Forall @"t" t) (Forall @"k" k) ->
       s .== t .=> decryptRound s k .== decryptRound t k) []

  shiftedStateCongruence <- lemma "AES.aesDecryptSubShiftCongruence"
    (\(Forall @"s" s) (Forall @"t" t) (Forall @"k" k) ->
       s .== t .=> decryptRound (subShift s) k .== decryptRound (subShift t) k) []

  finalStateCongruence <- lemma "AES.aesFinalStateCongruence"
    (\(Forall @"s" s) (Forall @"t" t) (Forall @"k" k) ->
       s .== t .=> decryptFinalRound s k .== decryptFinalRound t k) []

  -- AES-128 has nine middle rounds and one final round. After n inverse
  -- middle rounds, the state is subShift of forward state (middleRounds-n).
  let middleRounds :: Int
      middleRounds = 9

  base <- calc "aes128Prefix0"
    (\(Forall @"pt" pt) (Forall @"key" key) ->
       let (es, dvals, _, _, _) = aesTrace pt key
       in packWords (head dvals) .== subShift (packWords (last es))) $ \pt key ->
       let (es, dvals, _, _, kn) = aesTrace pt key
           (encKS, _)            = AES.aesKeySchedule (wordsOf key)
           ct                    = AES.aesEncrypt (wordsOf pt) encKS
           s                     = packWords (last es)
           k                     = packWords kn
       in [] |- packWords (head dvals)
             ?? addKeyPacking `at` (Inst @"s" (toBlock ct), Inst @"k" (toBlock kn))
             =: (packWords ct `xor` k)
             ?? finalEncryptPacking `at` (Inst @"s" (toBlock (last es)), Inst @"k" (toBlock kn))
             ?? xorCongruence `at` (Inst @"s" (packWords ct), Inst @"t" (encryptFinalRound s k), Inst @"k" k)
             =: (encryptFinalRound s k `xor` k)
             ?? initial `at` (Inst @"s" s, Inst @"k" k)
             =: subShift s
             =: qed

  let advance :: Proof AES128Property -> Int -> TP (Proof AES128Property)
      advance previous n = calc ("aes128Prefix" ++ show n)
        (\(Forall @"pt" pt) (Forall @"key" key) ->
          let (es, dvals, _, _, _) = aesTrace pt key
          in packWords (dvals !! n) .== subShift (packWords (es !! (middleRounds - n)))) $ \pt key ->
        let (es, dvals, keys, _, _) = aesTrace pt key
            rawKey                  = keys !! (middleRounds - n)
            rawPrev                 = dvals !! (n - 1)
            prevEnc                 = es !! (middleRounds + 1 - n)
            nextEnc                 = es !! (middleRounds - n)
            k                       = packWords rawKey
            s                       = packWords nextEnc
            rawInvKey               = AES.invMixColumns rawKey
        in [] |- packWords (dvals !! n)
              ?? decryptPacking `at` (Inst @"s" (toBlock rawPrev), Inst @"k" (toBlock rawInvKey))
              =: decryptRound (packWords rawPrev) (packWords rawInvKey)
              ?? inverseMixPacking `at` Inst @"s" (toBlock rawKey)
              ?? keyCongruence `at`
                 ( Inst @"s" (packWords rawPrev)
                 , Inst @"k" (packWords rawInvKey)
                 , Inst @"j" (originalInverseMixState k)
                 )
              =: decryptRound (packWords rawPrev) (originalInverseMixState k)
              ?? previous `at` (Inst @"pt" pt, Inst @"key" key)
              ?? stateCongruence `at`
                 ( Inst @"s" (packWords rawPrev)
                 , Inst @"t" (subShift (packWords prevEnc))
                 , Inst @"k" (originalInverseMixState k)
                 )
              =: decryptRound (subShift (packWords prevEnc)) (originalInverseMixState k)
              ?? encryptPacking `at` (Inst @"s" (toBlock nextEnc), Inst @"k" (toBlock rawKey))
              ?? shiftedStateCongruence `at`
                 ( Inst @"s" (packWords prevEnc)
                 , Inst @"t" (encryptRound s k)
                 , Inst @"k" (originalInverseMixState k)
                 )
              =: decryptRound (subShift (encryptRound s k)) (originalInverseMixState k)
              ?? middleCancellation `at` (Inst @"s" s, Inst @"k" k)
              =: subShift s
              =: qed

  -- Generate a finite TP calculation, not an unbounded symbolic loop.
  allRounds <- foldM advance base [1 .. middleRounds]

  calc "aes128PackedCorrect" (\(Forall pt) (Forall key) ->
         packWords (aesResult pt key) .== pt) $ \pt key ->
    let (es, dvals, _, first, _) = aesTrace pt key
        (encKS, decKS)           = AES.aesKeySchedule (wordsOf key)
        ciphertext               = AES.aesEncrypt (wordsOf pt) encKS
        result                   = AES.aesDecrypt ciphertext decKS
        k                        = packWords first
        s0                       = packWords (head es)
        lastD                    = last dvals
    in [] |- packWords result
          ?? finalDecryptPacking `at` (Inst @"s" (toBlock lastD), Inst @"k" (toBlock first))
          =: decryptFinalRound (packWords lastD) k
          ?? allRounds `at` (Inst @"pt" pt, Inst @"key" key)
          ?? finalStateCongruence `at` (Inst @"s" (packWords lastD), Inst @"t" (subShift s0), Inst @"k" k)
          =: decryptFinalRound (subShift s0) k
          ?? final `at` (Inst @"s" s0, Inst @"k" k)
          =: (s0 `xor` k)
          ?? addKeyPacking `at` (Inst @"s" (toBlock (wordsOf pt)), Inst @"k" (toBlock first))
          ?? xorCongruence `at` (Inst @"s" s0, Inst @"t" (pt `xor` k), Inst @"k" k)
          =: (pt `xor` k `xor` k)
          ?? xorCancellation `at` (Inst @"s" pt, Inst @"k" k)
          =: pt
          =: qed

-----------------------------------------------------------------------------
-- * The original AES-128 round-trip theorem
-----------------------------------------------------------------------------

-- | Prove 'AES.aes128IsCorrect' by recalling the packed-state theorem and
-- connecting its equality to the original four-word predicate. Recall keeps
-- the packed proof's output brief; it still checks it when no cached result
-- is available. Run 'aes128PackedCorrect' to see that proof's full transcript.
--
-- >>> runTP aes128Correct
-- Lemma: aes128PackedCorrect                  Q.E.D.
-- Lemma: AES.blockEqualityRepresentation      Q.E.D.
-- Lemma: aes128Correct
--   Step: 1                                   Q.E.D.
--   Step: 2                                   Q.E.D.
--   Result:                                   Q.E.D.
-- [Proven] aes128Correct :: Ɐpt ∷ (WordN 128) → Ɐkey ∷ (WordN 128) → Bool
aes128Correct :: TP (Proof AES128Property)
aes128Correct = do
  packed <- recall aes128PackedCorrect

  representation <- lemma "AES.blockEqualityRepresentation"
    (\(Forall @"s" s) (Forall @"t" t) ->
       (fromBlock s .== fromBlock t) .== (packWords (fromBlock t) .== packWords (fromBlock s))) []

  calc "aes128Correct" (\(Forall pt) (Forall key) ->
    let [p0, p1, p2, p3] = wordsOf pt
        [k0, k1, k2, k3] = wordsOf key
    in AES.aes128IsCorrect (p0, p1, p2, p3) (k0, k1, k2, k3)) $ \pt key ->
    let [p0, p1, p2, p3] = wordsOf pt
        [k0, k1, k2, k3] = wordsOf key
    in [] |- AES.aes128IsCorrect (p0, p1, p2, p3) (k0, k1, k2, k3)
          ?? representation `at` (Inst @"s" (toBlock (wordsOf pt)), Inst @"t" (toBlock (aesResult pt key)))
          =: (packWords (aesResult pt key) .== pt)
          ?? packed `at` (Inst @"pt" pt, Inst @"key" key)
          =: sTrue
          =: qed
