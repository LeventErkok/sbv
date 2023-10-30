-----------------------------------------------------------------------------
-- |
-- Module    : Documentation.SBV.Examples.Crypto.AES
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- An implementation of AES (Advanced Encryption Standard), using SBV.
-- For details on AES, see <http://en.wikipedia.org/wiki/Advanced_Encryption_Standard>.
--
-- We do a T-box implementation, which leads to good C code as we can take
-- advantage of look-up tables. Note that we make virtually no attempt to
-- optimize our Haskell code. The concern here is not with getting Haskell running
-- fast at all. The idea is to program the T-Box implementation as naturally and clearly
-- as possible in Haskell, and have SBV's code-generator generate fast C code automatically.
-- Therefore, we merely use ordinary Haskell lists as our data-structures, and do not
-- bother with any unboxing or strictness annotations. Thus, we achieve the separation
-- of concerns: Correctness via clarity and simplicity and proofs on the Haskell side,
-- performance by relying on SBV's code generator. If necessary, the generated code
-- can be FFI'd back into Haskell to complete the loop.
--
-- All 3 valid key sizes (128, 192, and 256) as required by the FIPS-197 standard
-- are supported.
-----------------------------------------------------------------------------

{-# LANGUAGE CPP              #-}
{-# LANGUAGE DataKinds        #-}
{-# LANGUAGE ParallelListComp #-}
{-# LANGUAGE TypeApplications #-}

#if MIN_VERSION_base(4,19,0)
{-# OPTIONS_GHC -Wall -Werror -Wno-incomplete-uni-patterns -Wno-x-partial #-}
#else
{-# OPTIONS_GHC -Wall -Werror -Wno-incomplete-uni-patterns #-}
#endif

module Documentation.SBV.Examples.Crypto.AES where

import Control.Monad (void, when)

import Data.SBV
import Data.SBV.Tools.CodeGen
import Data.SBV.Tools.Polynomial

import Data.List (transpose)
import Data.Maybe (fromJust)

import Data.Proxy

import Numeric (showHex)

import Test.QuickCheck hiding (verbose)

-- $setup
-- >>> -- For doctest purposes only:
-- >>> import Data.SBV

-----------------------------------------------------------------------------
-- * Formalizing GF(2^8)
-----------------------------------------------------------------------------

-- | An element of the Galois Field 2^8, which are essentially polynomials with
-- maximum degree 7. They are conveniently represented as values between 0 and 255.
type GF28 = SWord 8

-- | Multiplication in GF(2^8). This is simple polynomial multiplication, followed
-- by the irreducible polynomial @x^8+x^4+x^3+x^1+1@. We simply use the 'pMult'
-- function exported by SBV to do the operation.
gf28Mult :: GF28 -> GF28 -> GF28
gf28Mult x y = pMult (x, y, [8, 4, 3, 1, 0])

-- | Exponentiation by a constant in GF(2^8). The implementation uses the usual
-- square-and-multiply trick to speed up the computation.
gf28Pow :: GF28 -> Int -> GF28
gf28Pow n = pow
  where sq x  = x `gf28Mult` x
        pow 0    = 1
        pow i
         | odd i = n `gf28Mult` sq (pow (i `shiftR` 1))
         | True  = sq (pow (i `shiftR` 1))

-- | Computing inverses in GF(2^8). By the mathematical properties of GF(2^8)
-- and the particular irreducible polynomial used @x^8+x^5+x^3+x^1+1@, it
-- turns out that raising to the 254 power gives us the multiplicative inverse.
-- Of course, we can prove this using SBV:
--
-- >>> prove $ \x -> x ./= 0 .=> x `gf28Mult` gf28Inverse x .== 1
-- Q.E.D.
--
-- Note that we exclude @0@ in our theorem, as it does not have a
-- multiplicative inverse.
gf28Inverse :: GF28 -> GF28
gf28Inverse x = x `gf28Pow` 254

-----------------------------------------------------------------------------
-- * Implementing AES
-----------------------------------------------------------------------------

-----------------------------------------------------------------------------
-- ** Types and basic operations
-----------------------------------------------------------------------------
-- | AES state. The state consists of four 32-bit words, each of which is in turn treated
-- as four GF28's, i.e., 4 bytes. The T-Box implementation keeps the four-bytes together
-- for efficient representation.
type State = [SWord 32]

-- | The key, which can be 128, 192, or 256 bits. Represented as a sequence of 32-bit words.
type Key = [SWord 32]

-- | The key schedule. AES executes in rounds, and it treats first and last round keys slightly
-- differently than the middle ones. We reflect that choice by being explicit about it in our type.
-- The length of the middle list of keys depends on the key-size, which in turn determines
-- the number of rounds.
type KS = (Key, [Key], Key)

-- | Rotating a state row by a fixed amount to the right.
rotR :: [GF28] -> Int -> [GF28]
rotR [a, b, c, d] 1 = [d, a, b, c]
rotR [a, b, c, d] 2 = [c, d, a, b]
rotR [a, b, c, d] 3 = [b, c, d, a]
rotR xs           i = error $ "rotR: Unexpected input: " ++ show (xs, i)

-----------------------------------------------------------------------------
-- ** The key schedule
-----------------------------------------------------------------------------

-- | Definition of round-constants, as specified in Section 5.2 of the AES standard.
roundConstants :: [GF28]
roundConstants = 0 : [ gf28Pow 2 (k-1) | k <- [1 .. ] ]

-- | The @InvMixColumns@ transformation, as described in Section 5.3.3 of the standard. Note
-- that this transformation is only used explicitly during key-expansion in the T-Box implementation
-- of AES.
invMixColumns :: State -> State
invMixColumns state = map fromBytes $ transpose $ mmult (map toBytes state)
 where dot f   = foldr1 xor . zipWith ($) f
       mmult n = [map (dot r) n | r <- [ [mE, mB, mD, m9]
                                       , [m9, mE, mB, mD]
                                       , [mD, m9, mE, mB]
                                       , [mB, mD, m9, mE]
                                       ]]
       -- table-lookup versions of gf28Mult with the constants used in invMixColumns
       mE = select mETable 0
       mB = select mBTable 0
       mD = select mDTable 0
       m9 = select m9Table 0
       mETable = map (gf28Mult 0xE) [0..255]
       mBTable = map (gf28Mult 0xB) [0..255]
       mDTable = map (gf28Mult 0xD) [0..255]
       m9Table = map (gf28Mult 0x9) [0..255]

-- | Key expansion. Starting with the given key, returns an infinite sequence of
-- words, as described by the AES standard, Section 5.2, Figure 11.
keyExpansion :: Int -> Key -> [Key]
keyExpansion nk key = chop4 keys
   where keys :: [SWord 32]
         keys = key ++ [nextWord i prev old | i <- [nk ..] | prev <- drop (nk-1) keys | old <- keys]

         nextWord :: Int -> SWord 32 -> SWord 32 -> SWord 32
         nextWord i prev old
           | i `mod` nk == 0           = old `xor` subWordRcon (prev `rotateL` 8) (roundConstants !! (i `div` nk))
           | i `mod` nk == 4 && nk > 6 = old `xor` subWordRcon prev 0
           | True                      = old `xor` prev

         subWordRcon :: SWord 32 -> GF28 -> SWord 32
         subWordRcon w rc = fromBytes [a `xor` rc, b, c, d]
            where [a, b, c, d] = map sbox $ toBytes w

-----------------------------------------------------------------------------
-- ** The S-box transformation
-----------------------------------------------------------------------------

-- | The values of the AES S-box table. Note that we describe the S-box programmatically
-- using the mathematical construction given in Section 5.1.1 of the standard. However,
-- the code-generation will turn this into a mere look-up table, as it is just a
-- constant table, all computation being done at \"compile-time\".
sboxTable :: [GF28]
sboxTable = [xformByte (gf28Inverse b) | b <- [0 .. 255]]
  where xformByte :: GF28 -> GF28
        xformByte b = foldr xor 0x63 [b `rotateR` i | i <- [0, 4, 5, 6, 7]]

-- | The sbox transformation. We simply select from the sbox table. Note that we
-- are obliged to give a default value (here @0@) to be used if the index is out-of-bounds
-- as required by SBV's 'select' function. However, that will never happen since
-- the table has all 256 elements in it.
sbox :: GF28 -> GF28
sbox = select sboxTable 0

-----------------------------------------------------------------------------
-- ** The inverse S-box transformation
-----------------------------------------------------------------------------

-- | The values of the inverse S-box table. Again, the construction is programmatic.
unSBoxTable :: [GF28]
unSBoxTable = [gf28Inverse (xformByte b) | b <- [0 .. 255]]
  where xformByte :: GF28 -> GF28
        xformByte b = foldr xor 0x05 [b `rotateR` i | i <- [2, 5, 7]]

-- | The inverse s-box transformation.
unSBox :: GF28 -> GF28
unSBox = select unSBoxTable 0

-- | Prove that the 'sbox' and 'unSBox' are inverses. We have:
--
-- >>> prove sboxInverseCorrect
-- Q.E.D.
--
sboxInverseCorrect :: GF28 -> SBool
sboxInverseCorrect x = unSBox (sbox x) .== x .&& sbox (unSBox x) .== x

-----------------------------------------------------------------------------
-- ** AddRoundKey transformation
-----------------------------------------------------------------------------

-- | Adding the round-key to the current state. We simply exploit the fact
-- that addition is just xor in implementing this transformation.
addRoundKey :: Key -> State -> State
addRoundKey = zipWith xor

-----------------------------------------------------------------------------
-- ** Tables for T-Box encryption
-----------------------------------------------------------------------------

-- | T-box table generation function for encryption
t0Func :: GF28 -> [GF28]
t0Func a = [s `gf28Mult` 2, s, s, s `gf28Mult` 3] where s = sbox a

-- | First look-up table used in encryption
t0 :: GF28 -> SWord 32
t0 = select t0Table 0 where t0Table = [fromBytes (t0Func a)          | a <- [0..255]]

-- | Second look-up table used in encryption
t1 :: GF28 -> SWord 32
t1 = select t1Table 0 where t1Table = [fromBytes (t0Func a `rotR` 1) | a <- [0..255]]

-- | Third look-up table used in encryption
t2 :: GF28 -> SWord 32
t2 = select t2Table 0 where t2Table = [fromBytes (t0Func a `rotR` 2) | a <- [0..255]]

-- | Fourth look-up table used in encryption
t3 :: GF28 -> SWord 32
t3 = select t3Table 0 where t3Table = [fromBytes (t0Func a `rotR` 3) | a <- [0..255]]

-----------------------------------------------------------------------------
-- ** Tables for T-Box decryption
-----------------------------------------------------------------------------

-- | T-box table generating function for decryption
u0Func :: GF28 -> [GF28]
u0Func a = [s `gf28Mult` 0xE, s `gf28Mult` 0x9, s `gf28Mult` 0xD, s `gf28Mult` 0xB] where s = unSBox a

-- | First look-up table used in decryption
u0 :: GF28 -> SWord 32
u0 = select t0Table 0 where t0Table = [fromBytes (u0Func a)          | a <- [0..255]]

-- | Second look-up table used in decryption
u1 :: GF28 -> SWord 32
u1 = select t1Table 0 where t1Table = [fromBytes (u0Func a `rotR` 1) | a <- [0..255]]

-- | Third look-up table used in decryption
u2 :: GF28 -> SWord 32
u2 = select t2Table 0 where t2Table = [fromBytes (u0Func a `rotR` 2) | a <- [0..255]]

-- | Fourth look-up table used in decryption
u3 :: GF28 -> SWord 32
u3 = select t3Table 0 where t3Table = [fromBytes (u0Func a `rotR` 3) | a <- [0..255]]

-----------------------------------------------------------------------------
-- ** AES rounds
-----------------------------------------------------------------------------

-- | Generic round function. Given the function to perform one round, a key-schedule,
-- and a starting state, it performs the AES rounds.
doRounds :: (Bool -> State -> Key -> State) -> KS -> State -> State
doRounds rnd (ikey, rkeys, fkey) sIn = rnd True (last rs) fkey
  where s0 = ikey `addRoundKey` sIn
        rs = s0 : [rnd False s k | s <- rs | k <- rkeys ]

-- | One encryption round. The first argument indicates whether this is the final round
-- or not, in which case the construction is slightly different.
aesRound :: Bool -> State -> Key -> State
aesRound isFinal s key = d `addRoundKey` key
  where d = map (f isFinal) [0..3]
        a = map toBytes s
        f True j = fromBytes [ sbox (a !! ((j+0) `mod` 4) !! 0)
                             , sbox (a !! ((j+1) `mod` 4) !! 1)
                             , sbox (a !! ((j+2) `mod` 4) !! 2)
                             , sbox (a !! ((j+3) `mod` 4) !! 3)
                             ]
        f False j = e0 `xor` e1 `xor` e2 `xor` e3
              where e0 = t0 (a !! ((j+0) `mod` 4) !! 0)
                    e1 = t1 (a !! ((j+1) `mod` 4) !! 1)
                    e2 = t2 (a !! ((j+2) `mod` 4) !! 2)
                    e3 = t3 (a !! ((j+3) `mod` 4) !! 3)

-- | One decryption round. Similar to the encryption round, the first argument
-- indicates whether this is the final round or not.
aesInvRound :: Bool -> State -> Key -> State
aesInvRound isFinal s key = d `addRoundKey` key
  where d = map (f isFinal) [0..3]
        a = map toBytes s
        f True j = fromBytes [ unSBox (a !! ((j+0) `mod` 4) !! 0)
                             , unSBox (a !! ((j+3) `mod` 4) !! 1)
                             , unSBox (a !! ((j+2) `mod` 4) !! 2)
                             , unSBox (a !! ((j+1) `mod` 4) !! 3)
                             ]
        f False j = e0 `xor` e1 `xor` e2 `xor` e3
              where e0 = u0 (a !! ((j+0) `mod` 4) !! 0)
                    e1 = u1 (a !! ((j+3) `mod` 4) !! 1)
                    e2 = u2 (a !! ((j+2) `mod` 4) !! 2)
                    e3 = u3 (a !! ((j+1) `mod` 4) !! 3)

-----------------------------------------------------------------------------
-- * AES API
-----------------------------------------------------------------------------

-- | Key schedule. Given a 128, 192, or 256 bit key, expand it to get key-schedules
-- for encryption and decryption. The key is given as a sequence of 32-bit words.
-- (4 elements for 128-bits, 6 for 192, and 8 for 256.) Compare this function to 'aesInvKeySchedule'
-- which can calculate the key-expansion for decryption on the fly, as opposed to calculating
-- the forward key-expansion first.
aesKeySchedule :: Key -> (KS, KS)
aesKeySchedule key
  | nk `elem` [4, 6, 8]
  = (encKS, decKS)
  | True
  = error "aesKeySchedule: Invalid key size"
  where nk = length key
        nr = nk + 6
        encKS@(f, m, l) = (head rKeys, take (nr-1) (tail rKeys), rKeys !! nr)
        decKS = (l, map invMixColumns (reverse m), f)
        rKeys = keyExpansion nk key

-- | Block encryption. The first argument is the plain-text, which must have
-- precisely 4 elements, for a total of 128-bits of input. The second
-- argument is the key-schedule to be used, obtained by a call to 'aesKeySchedule'.
-- The output will always have 4 32-bit words, which is the cipher-text.
aesEncrypt :: [SWord 32] -> KS -> [SWord 32]
aesEncrypt pt encKS
  | length pt == 4
  = doRounds aesRound encKS pt
  | True
  = error "aesEncrypt: Invalid plain-text size"

-- | Block decryption. The arguments are the same as in 'aesEncrypt', except
-- the first argument is the cipher-text and the output is the corresponding
-- plain-text.
aesDecrypt :: [SWord 32] -> KS -> [SWord 32]
aesDecrypt ct decKS
  | length ct == 4
  = doRounds aesInvRound decKS ct
  | True
  = error "aesDecrypt: Invalid cipher-text size"

-----------------------------------------------------------------------------
-- * On-the-fly decryption
-- ${ontheflyintro}
-----------------------------------------------------------------------------
{- $ontheflyintro
   While regular encryption can be fused with key-generation, the standard method of AES
   decryption has to perform the key-expansion before decryption starts. This can be undesirable
   as it necessarily serializes the action of key-expansion before decryption. An
   alternative is to do on-the-fly decryption: We can expand the key in reverse, and thus
   need not save the key-schedule. One downside of this approach, however, is that we need
   to keep the "unwound" key: That is, instead of the common key used for encryption and
   decryption, we need to hold on to the final value of key-expansion, so it can be run
   in reverse. In this section, we implement on-the-fly decryption using this idea.
-}

-- | Inverse key expansion. Starting from the final round key, unwinds key generation operation
-- to construct keys for the previous rounds. Used in on-the-fly decryption.
invKeyExpansion :: Int -> Key -> [Key]
invKeyExpansion nk rkey = map reverse (chop4 keys)
   where keys :: [SWord 32]
         keys = rkey ++ [invNextWord i prev old | i <- reverse [0 .. remaining - 1] | prev <- drop 1 keys | old <- keys]

         totalWords = 4 * (nk + 6 + 1)
         remaining  = totalWords - nk

         invNextWord :: Int -> SWord 32 -> SWord 32 -> SWord 32
         invNextWord i prev old
           | i `mod` nk == 0           = old `xor` subWordRcon (prev `rotateL` 8) (roundConstants !! (1 + i `div` nk))
           | i `mod` nk == 4 && nk > 6 = old `xor` subWordRcon prev 0
           | True                      = old `xor` prev

         subWordRcon :: SWord 32 -> GF28 -> SWord 32
         subWordRcon w rc = fromBytes [a `xor` rc, b, c, d]
            where [a, b, c, d] = map sbox $ toBytes w

-- | AES inverse key schedule. Starting from the last-round key, construct the sequence of keys
-- that can be used for doing on-the-fly decryption. Compare this function to 'aesKeySchedule' which
-- returns both encryption and decryption schedules: In this case, we don't calculate the encryption
-- sequence, hence we can fuse this function with the decryption operation.
aesInvKeySchedule :: Key -> KS
aesInvKeySchedule key
  | nk `elem` [4, 6, 8]
  = decKS
  | True
  = error "aesInvKeySchedule: Invalid key size"
  where nk = length key
        nr = nk + 6
        decKS = (head rKeys, take (nr-1) (tail rKeys), rKeys !! nr)
        rKeys = invKeyExpansion nk key

-- | Block decryption, starting from the unwound key. That is, start from the final key.
-- Also; we don't use the T-box implementation. Just pure AES inverse cipher.
aesDecryptUnwoundKey :: [SWord 32] -> KS -> [SWord 32]
aesDecryptUnwoundKey ct decKS
  | length ct == 4
  = doRounds aesInvRoundRegular decKS ct
  | True
  = error "aesDecrypt: Invalid cipher-text size"
  where aesInvRoundRegular isFinal s key = u
          where u :: State
                u = map (f isFinal) [0 .. 3]
                  where a   = map toBytes s
                        kbs = map toBytes key
                        f True j = fromBytes [ unSBox (a !! ((j+0) `mod` 4) !! 0)
                                             , unSBox (a !! ((j+3) `mod` 4) !! 1)
                                             , unSBox (a !! ((j+2) `mod` 4) !! 2)
                                             , unSBox (a !! ((j+1) `mod` 4) !! 3)
                                             ] `xor` (key !! j)
                        f False j = e0 `xor` e1 `xor` e2 `xor` e3
                              where e0 = otfU0 $ unSBox (a !! ((j+0) `mod` 4) !! 0) `xor` (kbs !! j !! 0)
                                    e1 = otfU1 $ unSBox (a !! ((j+3) `mod` 4) !! 1) `xor` (kbs !! j !! 1)
                                    e2 = otfU2 $ unSBox (a !! ((j+2) `mod` 4) !! 2) `xor` (kbs !! j !! 2)
                                    e3 = otfU3 $ unSBox (a !! ((j+1) `mod` 4) !! 3) `xor` (kbs !! j !! 3)

                otfU0Func b = [b `gf28Mult` 0xE, b `gf28Mult` 0x9, b `gf28Mult` 0xD, b `gf28Mult` 0xB]
                otfU0 = select t0Table 0 where t0Table = [fromBytes (otfU0Func a)          | a <- [0..255]]
                otfU1 = select t1Table 0 where t1Table = [fromBytes (otfU0Func a `rotR` 1) | a <- [0..255]]
                otfU2 = select t2Table 0 where t2Table = [fromBytes (otfU0Func a `rotR` 2) | a <- [0..255]]
                otfU3 = select t3Table 0 where t3Table = [fromBytes (otfU0Func a `rotR` 3) | a <- [0..255]]

-----------------------------------------------------------------------------
-- * Test vectors
-----------------------------------------------------------------------------

-- | Common plain text for test vectors
commonPT :: [SWord 32]
commonPT = [0x00112233, 0x44556677, 0x8899aabb, 0xccddeeff]

-- | Key for 128-bit encryption test
aes128Key :: Key
aes128Key = [0x00010203, 0x04050607, 0x08090a0b, 0x0c0d0e0f]

-- | Key for 192-bit encryption test
aes192Key :: Key
aes192Key = aes128Key ++ [0x10111213, 0x14151617]

-- | Key for 256-bit encryption test
aes256Key :: Key
aes256Key = aes192Key ++ [0x18191a1b, 0x1c1d1e1f]

-- | Expected cipher-text for 128-bit encryption
aes128CT :: [SWord 32]
aes128CT = [0x69c4e0d8, 0x6a7b0430, 0xd8cdb780, 0x70b4c55a]

-- | Expected cipher-text for 192-bit encryption
aes192CT :: [SWord 32]
aes192CT = [0xdda97ca4, 0x864cdfe0, 0x6eaf70a0, 0xec0d7191]

-- | Expected cipher-text for 256-bit encryption
aes256CT :: [SWord 32]
aes256CT = [0x8ea2b7ca, 0x516745bf, 0xeafc4990, 0x4b496089]

-- | Calculate the 128-bit final-round key from on-the-fly decryption key schedule
aes128InvKey :: Key
aes128InvKey = extractFinalKey aes128Key

-- | Calculate the 192-bit final-round key from on-the-fly decryption key schedule
aes192InvKey :: Key
aes192InvKey = extractFinalKey aes192Key

-- | Calculate the 192-bit final-round key from on-the-fly decryption key schedule. Compare this
-- to 'aes192InvKey': Typically we just need the final 6-blocks, but it is advantageous to have
-- the entire last 8-blocks even for 192-bit keys. That is,  e store the final 256-bits of key-expansion
-- for speed purposes for both 192 and 256 bit versions. (But only the final 128 bits for the 128-bit version.)
aes192InvKeyExtended :: Key
aes192InvKeyExtended = extractFinalKeyExtended aes192Key

-- | Calculate the 256-bit final-round key from on-the-fly decryption key schedule
aes256InvKey :: Key
aes256InvKey = extractFinalKey aes256Key

-- | Extract the final key for on-the-fly decryption. This will extract exactly the number of blocks we need.
extractFinalKey :: [SWord 32] -> [SWord 32]
extractFinalKey initKey = take nk (extractFinalKeyExtended initKey)
  where nk = length initKey

-- | Extract the extended key for on-the-fly decryption. This will extract 4-blocks for 128-bit decryption,
-- but 256 bit for both 192 and 256-bit variants
extractFinalKeyExtended :: [SWord 32] -> [SWord 32]
extractFinalKeyExtended initKey = take feed (concatMap reverse (chop4 (take feed roundKeys)))
  where nk             = length initKey
        feed | nk == 4 = 4
             | True    = 8

        ((f, m, l), _) = aesKeySchedule initKey
        roundKeys      = l ++ concat (reverse m) ++ f

-----------------------------------------------------------------------------
-- ** 128-bit enc/dec test
-----------------------------------------------------------------------------

-- | 128-bit encryption test, from Appendix C.1 of the AES standard:
--
-- >>> map hex8 t128Enc
-- ["69c4e0d8","6a7b0430","d8cdb780","70b4c55a"]
t128Enc :: [SWord 32]
t128Enc = aesEncrypt commonPT ks
  where (ks, _) = aesKeySchedule aes128Key

-- | 128-bit decryption test, from Appendix C.1 of the AES standard:
--
-- >>> map hex8 t128Dec
-- ["00112233","44556677","8899aabb","ccddeeff"]
t128Dec :: [SWord 32]
t128Dec = aesDecrypt aes128CT ks
  where (_, ks) = aesKeySchedule aes128Key

-----------------------------------------------------------------------------
-- ** 192-bit enc/dec test
-----------------------------------------------------------------------------

-- | 192-bit encryption test, from Appendix C.2 of the AES standard:
--
-- >>> map hex8 t192Enc
-- ["dda97ca4","864cdfe0","6eaf70a0","ec0d7191"]
t192Enc :: [SWord 32]
t192Enc = aesEncrypt commonPT ks
  where (ks, _) = aesKeySchedule aes192Key

-- | 192-bit decryption test, from Appendix C.2 of the AES standard:
--
-- >>> map hex8 t192Dec
-- ["00112233","44556677","8899aabb","ccddeeff"]
--
t192Dec :: [SWord 32]
t192Dec = aesDecrypt aes192CT ks
  where (_, ks) = aesKeySchedule aes192Key

-----------------------------------------------------------------------------
-- ** 256-bit enc/dec test
-----------------------------------------------------------------------------

-- | 256-bit encryption, from Appendix C.3 of the AES standard:
--
-- >>> map hex8 t256Enc
-- ["8ea2b7ca","516745bf","eafc4990","4b496089"]
t256Enc :: [SWord 32]
t256Enc = aesEncrypt commonPT ks
  where (ks, _) = aesKeySchedule aes256Key

-- | 256-bit decryption, from Appendix C.3 of the AES standard:
--
-- >>> map hex8 t256Dec
-- ["00112233","44556677","8899aabb","ccddeeff"]
t256Dec :: [SWord 32]
t256Dec = aesDecrypt aes256CT ks
  where (_, ks) = aesKeySchedule aes256Key

-- | Various tests for round-trip properties. We have:
--
-- >>> runAESTests False
-- GOOD: Key generation AES128
-- GOOD: Key generation AES192
-- GOOD: Key generation AES256
-- GOOD: Encryption     AES128
-- GOOD: Decryption     AES128
-- GOOD: Decryption-OTF AES128
-- GOOD: Encryption     AES192
-- GOOD: Decryption     AES192
-- GOOD: Decryption-OTF AES192
-- GOOD: Encryption     AES256
-- GOOD: Decryption     AES256
-- GOOD: Decryption-OTF AES256
runAESTests :: Bool -> IO ()
runAESTests runQC = do
                 testInvKeyExpansion

                 check "AES128" aes128Key aes128InvKey aes128CT
                 check "AES192" aes192Key aes192InvKey aes192CT
                 check "AES256" aes256Key aes256InvKey aes256CT

                 -- Quick-check tests are rather slow. So only run when requested.
                 when runQC $ do
                   putStrLn "Quick-check AES128 roundtrip" >> quickCheck roundTrip128
                   putStrLn "Quick-check AES192 roundtrip" >> quickCheck roundTrip192
                   putStrLn "Quick-check AES256 roundtrip" >> quickCheck roundTrip256

  where check :: String -> Key -> Key -> [SWord 32] -> IO ()
        check what key invKey ctExpected = do eq ("Encryption     " ++ what) ctExpected ctGot
                                              eq ("Decryption     " ++ what) commonPT   ptGot
                                              eq ("Decryption-OTF " ++ what) commonPT   ptGotInv
           where (encKS, decKS) = aesKeySchedule key
                 ctGot          = aesEncrypt           commonPT   encKS
                 ptGot          = aesDecrypt           ctExpected decKS
                 ptGotInv       = aesDecryptUnwoundKey ctExpected (aesInvKeySchedule invKey)

                 eq tag expected got
                   | length expected /= length got
                   = error $ unlines [ "BAD!: " ++ tag
                                     , "Comparing different sized lists:"
                                     , "Expected: " ++ show expected
                                     , "Got     : " ++ show got
                                     ]
                   | map extract expected == map extract got
                   = putStrLn $ "GOOD: " ++ tag
                   | True
                   = error $ unlines [ "BAD!: " ++ tag
                                     , "Expected: " ++ unwords (map hex8 expected)
                                     , "Got     : " ++ unwords (map hex8 got)
                                     ]
                  where extract :: SWord 32 -> Integer
                        extract = fromIntegral . fromJust . unliteral

        testInvKeyExpansion :: IO ()
        testInvKeyExpansion = do goTestInvKey "128" aes128Key
                                 goTestInvKey "192" aes192Key
                                 goTestInvKey "256" aes256Key
        goTestInvKey what k = do
          let nk = length k
              nr = nk + 6

              feed = case nk of
                       4 -> 4
                       _ -> 8

              ((f, m, l), _) = aesKeySchedule k
              required       = l ++ concat (reverse m) ++ f
              invKeySchedule = take (nr+1) $ invKeyExpansion nk (take nk (concatMap reverse (chop4 (take feed required))))
              obtained       = concat invKeySchedule

              expected = map (fromJust . unliteral) required
              result   = map (fromJust . unliteral) obtained

              sh i a b
               | a == b = pad ++ show i ++ " " ++ disp a
               | True   = pad ++ show i ++ " " ++ disp a ++ " |vs| " ++ disp b
               where pad = if i < 10 then " " else ""

              disp = unwords . map (hex8 . literal)

              lexpected = length expected
              lresult   = length result

          when (lexpected /= lresult) $
             error $ what ++ ": BAD! Mismatching lengths: " ++ show (lexpected, lresult)

          let debugging = False

          if expected == result
             then if debugging
                     then putStrLn $ unlines $ ("Size " ++ what ++ ": Good") : zipWith3 sh [(0::Int)..] (chop4 expected) (chop4 result)
                     else putStrLn $ "GOOD: Key generation AES" ++ what
             else error    $ unlines $ ("Size " ++ what ++ ": BAD!") : zipWith3 sh [(0::Int)..] (chop4 expected) (chop4 result)

        roundTrip128 (i0, i1, i2, i3) (k0, k1, k2, k3)                 = roundTrip [i0, i1, i2, i3] [k0, k1, k2, k3]
        roundTrip192 (i0, i1, i2, i3) (k0, k1, k2, k3, k4, k5)         = roundTrip [i0, i1, i2, i3] [k0, k1, k2, k3, k4, k5]
        roundTrip256 (i0, i1, i2, i3) (k0, k1, k2, k3, k4, k5, k6, k7) = roundTrip [i0, i1, i2, i3] [k0, k1, k2, k3, k4, k5, k6, k7]

        roundTrip :: [SWord32] -> [SWord32] -> SBool
        roundTrip ptIn keyIn = pt .== pt' .&& pt .== pt''
           where pt  = map toSized ptIn
                 key = map toSized keyIn

                 (encKS, decKS) = aesKeySchedule key
                 ct   = aesEncrypt pt encKS
                 pt'  = aesDecrypt ct decKS
                 pt'' = aesDecryptUnwoundKey ct (aesInvKeySchedule (extractFinalKey key))

-----------------------------------------------------------------------------
-- * Verification
-- ${verifIntro}
-----------------------------------------------------------------------------
{- $verifIntro
  While SMT based technologies can prove correct many small properties fairly quickly, it would
  be naive for them to automatically verify that our AES implementation is correct. (By correct,
  we mean decryption followed by encryption yielding the same result.) However, we can state
  this property precisely using SBV, and use quick-check to gain some confidence.
-}

-- | Correctness theorem for 128-bit AES. Ideally, we would run:
--
-- @
--   prove aes128IsCorrect
-- @
--
-- to get a proof automatically. Unfortunately, while SBV will successfully generate the proof
-- obligation for this theorem and ship it to the SMT solver, it would be naive to expect the SMT-solver
-- to finish that proof in any reasonable time with the currently available SMT solving technologies.
-- Instead, we can issue:
--
-- @
--   quickCheck aes128IsCorrect
-- @
--
-- and get some degree of confidence in our code. Similar predicates can be easily constructed for 192, and
-- 256 bit cases as well.
aes128IsCorrect :: (SWord 32, SWord 32, SWord 32, SWord 32)  -- ^ plain-text words
                -> (SWord 32, SWord 32, SWord 32, SWord 32)  -- ^ key-words
                -> SBool                                     -- ^ True if round-trip gives us plain-text back
aes128IsCorrect (i0, i1, i2, i3) (k0, k1, k2, k3) = pt .== pt'
   where pt  = [i0, i1, i2, i3]
         key = [k0, k1, k2, k3]
         (encKS, decKS) = aesKeySchedule key
         ct  = aesEncrypt pt encKS
         pt' = aesDecrypt ct decKS

-----------------------------------------------------------------------------
-- * Block encryption at full size
-----------------------------------------------------------------------------

-- | 128-bit encryption, that takes 128-bit values, instead of chunks. We have:
--
-- >>> hex8 $ aes128Enc 0x000102030405060708090a0b0c0d0e0f 0x00112233445566778899aabbccddeeff
-- "69c4e0d86a7b0430d8cdb78070b4c55a"
--
-- You can also render this function as a stand-alone function using:
--
-- @
--   sbv2smt (smtFunction "aes128Enc" aes128Enc)
-- @
aes128Enc :: SWord 128 -> SWord 128 -> SWord 128
aes128Enc key pt = from32 $ aesEncrypt (to32 pt) ks
  where to32 :: SWord 128 -> [SWord 32]
        to32 x = [ bvExtract (Proxy @127) (Proxy @96) x
                 , bvExtract (Proxy  @95) (Proxy @64) x
                 , bvExtract (Proxy  @63) (Proxy @32) x
                 , bvExtract (Proxy  @31) (Proxy  @0) x
                 ]

        from32 :: [SWord 32] -> SWord 128
        from32 [a, b, c, d] = a # b # c # d
        from32 _ = error "nope"

        (ks, _)  = aesKeySchedule (to32 key)

-----------------------------------------------------------------------------
-- * Code generation
-- ${codeGenIntro}
-----------------------------------------------------------------------------
{- $codeGenIntro
   We have emphasized that our T-Box implementation in Haskell was guided by clarity and correctness, not
   performance. Indeed, our implementation is hardly the fastest AES implementation in Haskell. However,
   we can use it to automatically generate straight-line C-code that can run fairly fast.

   For the purposes of illustration, we only show here how to generate code for a 128-bit AES block-encrypt
   function, that takes 8 32-bit words as an argument. The first 4 are the 128-bit input, and the final
   four are the 128-bit key. The impact of this is that the generated function would expand the key for
   each block of encryption, a needless task unless we change the key in every block. In a more serious application,
   we would instead generate code for both the 'aesKeySchedule' and the 'aesEncrypt' functions, thus reusing the
   key-schedule over many applications of the encryption call. (Unfortunately doing this is rather cumbersome right
   now, since Haskell does not support fixed-size lists.)
-}

-- | Code generation for 128-bit AES encryption.
--
-- The following sample from the generated code-lines show how T-Boxes are rendered as C arrays:
--
-- @
--   static const SWord32 table1[] = {
--       0xc66363a5UL, 0xf87c7c84UL, 0xee777799UL, 0xf67b7b8dUL,
--       0xfff2f20dUL, 0xd66b6bbdUL, 0xde6f6fb1UL, 0x91c5c554UL,
--       0x60303050UL, 0x02010103UL, 0xce6767a9UL, 0x562b2b7dUL,
--       0xe7fefe19UL, 0xb5d7d762UL, 0x4dababe6UL, 0xec76769aUL,
--       ...
--       }
-- @
--
-- The generated program has 5 tables (one sbox table, and 4-Tboxes), all converted to fast C arrays. Here
-- is a sample of the generated straightline C-code:
--
-- @
--   const SWord8  s1915 = (SWord8) s1912;
--   const SWord8  s1916 = table0[s1915];
--   const SWord16 s1917 = (((SWord16) s1914) << 8) | ((SWord16) s1916);
--   const SWord32 s1918 = (((SWord32) s1911) << 16) | ((SWord32) s1917);
--   const SWord32 s1919 = s1844 ^ s1918;
--   const SWord32 s1920 = s1903 ^ s1919;
-- @
--
-- The GNU C-compiler does a fine job of optimizing this straightline code to generate a fairly efficient C implementation.
cgAES128BlockEncrypt :: IO ()
cgAES128BlockEncrypt = compileToC Nothing "aes128BlockEncrypt" $ do
        pt  <- cgInputArr 4 "pt"        -- plain-text as an array of 4 Word32's
        key <- cgInputArr 4 "key"       -- key as an array of 4 Word32s

        -- Use the test values from Appendix C.1 of the AES standard as the driver values
        cgSetDriverValues $ map (fromIntegral . fromJust . unliteral) $ commonPT ++ aes128Key

        let (encKs, _) = aesKeySchedule key
        cgOutputArr "ct" $ aesEncrypt pt encKs

-----------------------------------------------------------------------------
-- * C-library generation
-- ${libraryIntro}
-----------------------------------------------------------------------------
{- $libraryIntro
   The 'cgAES128BlockEncrypt' example shows how to generate code for 128-bit AES encryption. As the generated
   function performs encryption on a given block, it performs key expansion as necessary. However, this is
   not quite practical: We would like to expand the key only once, and encrypt the stream of plain-text blocks using
   the same expanded key (potentially using some crypto-mode), until we decide to change the key. In this
   section, we show how to use SBV to instead generate a library of functions that can be used in such a scenario.
   The generated library is a typical @.a@ archive, that can be linked using the C-compiler as usual.
-}

-- | Components of the AES implementation that the library is generated from. For each case, we provide
-- the driver values from the AES test-vectors.
aesLibComponents :: Int -> [(String, [Integer], SBVCodeGen ())]
aesLibComponents sz = [ ("aes" ++ show sz ++ "KeySchedule",    keyDriverVals,    keySchedule)
                      , ("aes" ++ show sz ++ "BlockEncrypt",   encDriverVals,    enc)
                      , ("aes" ++ show sz ++ "BlockDecrypt",   decDriverVals,    dec)
                      , ("aes" ++ show sz ++ "InvKeySchedule", invKeyDriverVals, invKeySchedule)
                      , ("aes" ++ show sz ++ "OTFDecrypt",     invDecDriverVals, otfDec)
                      ]
  where badSize = error $ "aesLibComponents: Size must be one of 128, 192, or 256; received: " ++ show sz

        -- key-schedule
        nk
         | sz == 128 = 4
         | sz == 192 = 6
         | sz == 256 = 8
         | True      = badSize

        -- We get 4*(nr+1) keys, where nr = nk + 6
        nr = nk + 6
        xk = 4 * (nr + 1)

        (keyDriverVals, invKeyDriverVals, encDriverVals, decDriverVals, invDecDriverVals)
           | sz == 128 = (keyDriver aes128Key, keyDriver aes128InvKey, encDriver commonPT aes128Key, decDriver aes128CT aes128Key, invDecDriver aes128CT aes128InvKey)
           | sz == 192 = (keyDriver aes192Key, keyDriver aes192InvKey, encDriver commonPT aes192Key, decDriver aes192CT aes192Key, invDecDriver aes192CT aes192InvKey)
           | sz == 256 = (keyDriver aes256Key, keyDriver aes256InvKey, encDriver commonPT aes256Key, decDriver aes256CT aes256Key, invDecDriver aes256CT aes256InvKey)
           | True      = badSize
           where keyDriver       key = map cvt $ concatMap reverse (chop4 key)
                 encDriver    pt key = map cvt $ pt ++ flatten (fst (aesKeySchedule    key))
                 decDriver    ct key = map cvt $ ct ++ flatten (snd (aesKeySchedule    key))
                 invDecDriver ct key = map cvt $ ct ++ flatten      (aesInvKeySchedule key)

                 flatten (f, mid, l) = f ++ concat mid ++ l
                 cvt = fromIntegral . fromJust . unliteral

        keySchedule = do key <- cgInputArr nk "key"     -- key
                         let (encKS, decKS) = aesKeySchedule key
                         cgOutputArr "encKS" (ksToXKey encKS)
                         cgOutputArr "decKS" (ksToXKey decKS)

        invKeySchedule = do key <- cgInputArr nk "key"     -- key
                            let decKS = aesInvKeySchedule (concatMap reverse (chop4 key))
                            cgOutputArr "decKS" (ksToXKey decKS)

        -- encryption
        enc = do pt   <- cgInputArr 4  "pt"    -- plain-text
                 xkey <- cgInputArr xk "xkey"  -- expanded key
                 cgOutputArr "ct" $ aesEncrypt pt (xkeyToKS xkey)

        -- decryption
        dec = do pt   <- cgInputArr 4  "ct"    -- cipher-text
                 xkey <- cgInputArr xk "xkey"  -- expanded key
                 cgOutputArr "pt" $ aesDecrypt pt (xkeyToKS xkey)

        -- on-the-fly decryption
        otfDec = do ct   <- cgInputArr 4  "ct"    -- cipher-text
                    xkey <- cgInputArr xk "xkey"  -- expanded key
                    cgOutputArr "pt" $ aesDecryptUnwoundKey ct (xkeyToKS xkey)

        -- Transforming back and forth from our KS type to a flat array used by the generated C code
        -- Turn a series of expanded keys to our internal KS type
        xkeyToKS :: [SWord 32] -> KS
        xkeyToKS xs = (f, m, l)
           where f  = take 4 xs                             -- first round key
                 m  = chop4 (take (xk - 8) (drop 4 xs))     -- middle rounds
                 l  = drop (xk - 4) xs                      -- last round key

        -- Turn a KS to a series of expanded key words
        ksToXKey :: KS -> [SWord 32]
        ksToXKey (f, m, l) = f ++ concat m ++ l

-- | Generate code for AES functionality; given the key size.
cgAESLibrary :: Int -> Maybe FilePath -> IO ()
cgAESLibrary sz mbd
  | sz `elem` [128, 192, 256] = void $ compileToCLib mbd nm [(fnm, configure dvals f) | (fnm, dvals, f) <- aesLibComponents sz]
  | True                      = error $ "cgAESLibrary: Size must be one of 128, 192, or 256, received: " ++ show sz
  where nm = "aes" ++ show sz ++ "Lib"

        configure dvals code = cgSetDriverValues dvals >> code

-- | Generate a C library, containing functions for performing 128-bit enc/dec/key-expansion.
-- A note on performance: In a very rough speed test, the generated code was able to do
-- 6.3 million block encryptions per second on a decent MacBook Pro. On the same machine, OpenSSL
-- reports 8.2 million block encryptions per second. So, the generated code is about 25% slower
-- as compared to the highly optimized OpenSSL implementation. (Note that the speed test was done
-- somewhat simplistically, so these numbers should be considered very rough estimates.)
cgAES128Library :: IO ()
cgAES128Library = cgAESLibrary 128 Nothing

--------------------------------------------------------------------------------------------
-- | For doctest purposes only
hex8 :: (SymVal a, Show a, Integral a) => SBV a -> String
hex8 v = replicate (8 - length s) '0' ++ s
  where s = flip showHex "" . fromJust . unliteral $ v

-- | Chunk in groups of 4. (This function must be in some standard library, where?)
chop4 :: [a] -> [[a]]
chop4 [] = []
chop4 xs = let (f, r) = splitAt 4 xs in f : chop4 r

{- HLint ignore aesRound             "Use head" -}
{- HLint ignore aesInvRound          "Use head" -}
{- HLint ignore aesDecryptUnwoundKey "Use head" -}
