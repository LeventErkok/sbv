-----------------------------------------------------------------------------
-- |
-- Module      :  Data.SBV.Examples.Crypto.RC4
-- Copyright   :  (c) Austin Seipp
-- License     :  BSD3
-- Maintainer  :  erkokl@gmail.com
-- Stability   :  experimental
-- Portability :  portable
--
-- An implementation of RC4 (AKA Rivest Cipher 4 or Alleged RC4/ARC4),
-- using SBV. For information on RC4, see: <http://en.wikipedia.org/wiki/RC4>.
--
-- We make no effort to optimize the code, and instead focus on a clear
-- implementation. We then prove that encryption followed by decryption
-- yields the original input. From this, we extract fast C code that
-- executes RC4 over 64 byte inputs with a key size of 40 bits.
-----------------------------------------------------------------------------

{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE PatternGuards       #-}

module Data.SBV.Examples.Crypto.RC4 where

import Control.Monad
import Data.Char  (ord, chr)
import Data.List  (genericIndex)
import Data.Maybe (fromJust)
import Data.SBV

-----------------------------------------------------------------------------
-- * Types
-----------------------------------------------------------------------------

-- | RC4 State contains 256 8-bit values. We use a symbolic array
-- to represent the state since RC4 needs access to the array via
-- a symbolic index.
type S = SFunArray Word8 Word8

-- | The key is a stream of 'Word8' values.
type Key = [SWord8]

-- | Represents the current state of the RC4 stream: it is the @S@ array
-- along with the @i@ and @j@ index values used by the PRGA.
type RC4 = (S, SWord8, SWord8)

-----------------------------------------------------------------------------
-- * The PRGA
-----------------------------------------------------------------------------

-- | Swaps two elements in the RC4 array.
swap :: SWord8 -> SWord8 -> S -> S
swap i j st = writeArray (writeArray st i stj) j sti
  where sti = readArray st i
        stj = readArray st j

-- | Implements the PRGA used in RC4. We return the new state and the next key value generated.
prga :: RC4 -> (SWord8, RC4)
prga (st', i', j') = (readArray st kInd, (st, i, j))
  where i    = i' + 1
        j    = j' + readArray st' i
        st   = swap i j st'
        kInd = readArray st i + readArray st j

-----------------------------------------------------------------------------
-- * Key schedule
-----------------------------------------------------------------------------

-- | Constructs the state to be used by the PRGA using the given key.
initRC4 :: Key -> RC4
initRC4 key
 | keyLength < 1 || keyLength > 256
 = error $ "RC4 requires a key of length between 1 and 256, received: " ++ show keyLength
 | True
 = (snd $ foldl mix (0, sInit) [0..255], 0, 0)
 where keyLength = length key
       sInit     = foldr (\i a -> writeArray a i i) (mkSFunArray 0) [0..255]
       mix :: (SWord8, S) -> SWord8 -> (SWord8, S)
       mix (j', s) i = let j = j' + readArray s i + genericIndex key (fromJust (unliteral i) `mod` fromIntegral keyLength)
                       in (j, swap i j s)

-- | The key-schedule. Note that this function returns an infinite list.
keySchedule :: Key -> [SWord8]
keySchedule key = genKeys (initRC4 key)
  where genKeys :: RC4 -> [SWord8]
        genKeys st = let (k, st') = prga st in k : genKeys st'

-- | Generate a key-schedule from a given key-string.
keyScheduleString :: String -> [SWord8]
keyScheduleString = keySchedule . map (literal . fromIntegral . ord)

-----------------------------------------------------------------------------
-- * Encryption and Decryption
-----------------------------------------------------------------------------

-- | RC4 encryption. We generate key-words and xor it with the input. The
-- following test-vectors are from Wikipedia: <http://en.wikipedia.org/wiki/RC4>:
--
-- >>> concatMap hex $ encrypt "Key" "Plaintext"
-- "bbf316e8d940af0ad3"
--
-- >>> concatMap hex $ encrypt "Wiki" "pedia"
-- "1021bf0420"
--
-- >>> concatMap hex $ encrypt "Secret" "Attack at dawn"
-- "45a01f645fc35b383552544b9bf5"
encrypt :: String -> String -> [SWord8]
encrypt key pt = zipWith xor (keyScheduleString key) (map cvt pt)
  where cvt = literal . fromIntegral . ord

-- | RC4 decryption. Essentially the same as decryption. We have:
--
-- >>> decrypt "Key" [0xbb, 0xf3, 0x16, 0xe8, 0xd9, 0x40, 0xaf, 0x0a, 0xd3]
-- "Plaintext"
--
-- >>> decrypt "Wiki" [0x10, 0x21, 0xbf, 0x04, 0x20]
-- "pedia"
--
-- >>> decrypt "Secret" [0x45, 0xa0, 0x1f, 0x64, 0x5f, 0xc3, 0x5b, 0x38, 0x35, 0x52, 0x54, 0x4b, 0x9b, 0xf5]
-- "Attack at dawn"
decrypt :: String -> [SWord8] -> String
decrypt key ct = map cvt $ zipWith xor (keyScheduleString key) ct
  where cvt = chr . fromIntegral . fromJust . unliteral

-----------------------------------------------------------------------------
-- * Verification
-----------------------------------------------------------------------------

-- | Prove that round-trip encryption/decryption leaves the plain-text unchanged.
-- The theorem is stated parametrically over key and plain-text sizes. Here is the
-- proof for a 40-bit key (5 bytes) and 40-bit plaintext (again 5 bytes).
--
-- >>> rc4IsCorrect 5 5
-- Q.E.D.
--
-- Note that this theorem is trivial, since it is essentially establishing
-- xor'in the same value twice leaves a word unchanged (i.e., @x `xor` y `xor` y = x@).
-- However, the proof takes quite a while to complete, as it gives rise to a fairly
-- large symbolic trace. The time spent in completing this proof is purely in the symbolic
-- simulation, while the actual proof time taken by Yices is comparatively negligable.
rc4IsCorrect :: Int -> Int -> IO ThmResult
rc4IsCorrect keyLen ptLen = proveWith verboseSMTCfg $ do
        key <- mkFreeVars keyLen
        pt  <- mkFreeVars ptLen
        let ks  = keySchedule key
            ct  = zipWith xor ks pt
            pt' = zipWith xor ks ct
        return $ pt .== pt'

-----------------------------------------------------------------------------
-- * Code generation
-----------------------------------------------------------------------------
-- | Generates C functions that perform the 'initRC4' and 'prga' functions.
-- In an imperative setting like in C, these two functions will suffice to
-- construct RC4 encryption/decryption quite easily. The 'initRC4' function
-- will expect a 40-byte input as the key stream.
codegenRC4 :: IO ()
codegenRC4 = compileToCLib Nothing "rc4Lib" [  ("initRC4", cInitRC4)
                                             , ("prga",    cPRGA)
                                            ]
  where cInitRC4 = do key <- cgInputArr 5 "key"
                      let (s, _, _) = initRC4 key
                      cgOutputArr "S" [readArray s i | i <- [0 .. 255]]
        cPRGA = do s <- cgInputArr 256 "S"
                   i <- cgInput "i"
                   j <- cgInput "j"
                   let sa = foldr (\i a -> writeArray a (literal i) (genericIndex s i)) (mkSFunArray 0) [0..255]
                       (k, (s', i', j')) = prga (sa, i, j)
                   cgOutputArr "newS" [readArray s' i | i <- [0 .. 255]]
                   cgOutput "newI" i'
                   cgOutput "newJ" j'
                   cgReturn k
