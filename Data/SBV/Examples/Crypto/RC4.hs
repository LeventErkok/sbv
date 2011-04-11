-----------------------------------------------------------------------------
-- |
-- Module      :  Data.SBV.Examples.Crypto.RC4
-- Copyright   :  (c) Austin Seipp 2011
-- License     :  BSD3
-- Maintainer  :  erkokl@gmail.com
-- Stability   :  experimental
-- Portability :  portable
-- 
-- An implementation of RC4 (AKA Rivest Cipher 4 or Alleged RC4/ARC4),
-- using SBV. For information on RC4, see: <http://en.wikipedia.org/wiki/RC4>.
-- 
-- For the original posting of RC4's code to cypherpunks, see:
-- <http://web.archive.org/web/20080404222417/http://cypherpunks.venona.com/date/1994/09/msg00304.html>
-- 
-- We implement RC4 as close as possible to the original
-- implementation posted to cypherpunks. We make no effort to optimize
-- the code, and instead focus on a clear implementation. We then
-- prove using the SMT solver that our encryption function followed by
-- decryption yields the original string. From this, we extract fast C
-- code that executes RC4 over 256 byte inputs with a key size of 128
-- bits.
{-# LANGUAGE ScopedTypeVariables, PatternGuards #-}
module Data.SBV.Examples.Crypto.RC4
( -- * Types
  S                    -- :: *
, Key                  -- :: *
, RC4                  -- :: *
  -- * Implementing RC4
  -- ** Swapping array values
, swap                 -- :: SWord8 -> SWord8 -> S -> S

  -- ** Key-scheduling algorithm
, initState            -- :: S
, ksa                  -- :: Key -> S -> S

  -- ** Psuedo-random generator algorithm
, prga                 -- :: RC4 -> (SWord8, RC4)

  -- ** Interface
, initCtx              -- :: Key -> RC4
, encrypt              -- :: [SWord8] -> RC4 -> ([SWord8], RC4)
, decrypt              -- :: [SWord8] -> RC4 -> ([SWord8], RC4)

  -- * Tests & Verification
, checkProps           -- :: IO ()
, doAllTests           -- :: IO ()

  -- * C Code generation
, codegenRC4           -- :: IO ()
) where
import Data.SBV
import Data.Maybe (fromJust)
import qualified Data.ByteString as B
import Control.Monad

import qualified Crypto.Cipher.RC4 as Crypto
import qualified Data.Vector.Unboxed as V
import Test.QuickCheck (quickCheck)

--------------------------
-- Types

-- | Denotes the @S@ array which is part of the RC4 state. Initially it is
-- populated with the values @[0x0,0xff]@ before key exchange.
type S = SFunArray Word8 Word8

-- | A key for RC4 is merely a stream of 'Word8' values.
type Key = [SWord8]

-- | Represents the current state of the RC4 stream: it is the @S@ array
-- along with the @i@ and @j@ index values used by the PRGA.
type RC4 = (S, SWord8, SWord8)


--------------------------
-- Swapping array values

-- | Swap two elements in an array, in this case, our RC4 @S@ array used 
-- in the PRGA/KSA.
swap :: SWord8 -> SWord8 -> S -> S
swap i j a
  = let tmp  = readArray a i
        a'   = writeArray a i (readArray a j)
    in writeArray a' j tmp

--------------------------
-- Key scheduling & PRGA

-- | Initial state table - this is the initial @S@ array used in the RC4 implementation,
-- and it is initially populated with 256 values from the range @[0,255]@.
initState :: S
initState = sw2arr [0..255]

-- | This implements the key-scheduling algorithm (KSA) and initializes
-- the RC4 @S@ array with a given key.
ksa :: Key -> S -> S
ksa key = ite (kl ./= 0) go id
  where kl :: SWord8
        kl = literal $ fromIntegral (length key)

        idx :: [a] -> SWord8 -> a
        idx arr i | Just x <- unliteral i = arr !! (fromIntegral x)
                  | otherwise = error "unsafeIdx: non-concrete argument"

        -- perform the key scheduling
        go :: S -> S
        go st = let (v,_,_) = k 0 (st, 0, 0) in v
          where k :: SWord16 -> (S, SWord8, SWord8) -> (S, SWord8, SWord8)
                k c v@(s, j, i)
                  = ite (c .== 256) v $
                      let lo  = snd $ split c -- truncate the low bits
                          j'  = ((key `idx` i) + (s .! lo) + j)
                          i'  = snd $ (i+1) `bvQuotRem` kl
                          s' = swap lo j' s
                      in k (c+1) (s',j',i')


-- | The psuedo-random-generation-algorithm (PRGA) generates the RC4
-- keystream one byte at a time as well as the new context for further
-- generation.
prga :: RC4 -> (SWord8, RC4)
prga (st,i,j)
  = let i'  = (i + 1)
        j'  = ((st .! i') + j)
        st' = swap i' j' st
        k  = (st' .! i') + (st' .! j')
    in (st' .! k, (st', i', j'))


----------------------------------------
-- Interface

-- | Initialize an RC4 context by supplying the encryption key. This routine performs
-- key exchange.
initCtx :: Key -> RC4
initCtx k = (ksa k initState, 0, 0)

-- | Encrypt some data using an encryption context. Returns the encrypted data,
-- and the updated key to use for further encryption. Do not use the contexts
-- you have already used to encrypt future data.
encrypt :: RC4 -> [SWord8] -> ([SWord8], RC4)
encrypt c plaintxt = k ([],c) plaintxt
  where k ::  ([SWord8], RC4) -> [SWord8] -> ([SWord8], RC4)
        k v [] = v
        k (out,ctx) (pt:pt')
          = let (ks,ctx') = prga ctx
                ct        = pt `xor` ks
            in k (out ++ [ct],ctx') pt'

-- | Decrypt some data with the given context, and return the decrypted data
-- and new context. Do not use the old context to decrypt any data in the future.
decrypt :: RC4 -> [SWord8] -> ([SWord8], RC4)
decrypt = encrypt


--------------------------
-- Verification & Tests

-- | Basic quickcheck properties for the crypto-api interface and some checks against
-- @cryptocipher@'s RC4 implementation.
-- 
--  * Tests our key-scheduling algorithm against cryptocipher's implementation.
-- 
--  * Tests our encryption algorithm against cryptocipher's implementation.
-- 
--  * Tests our decryption algorithm against cryptocipher's implementation.
-- 
--  * Checks all the test vectors described in <http://tools.ietf.org/html/draft-josefsson-rc4-test-vectors-02>
-- 
checkProps :: IO ()
checkProps = sequence_ [ test "cryptocipher ksa equivalence" $ quickCheck prop_crypto_ksa_eq
                       , test "cryptocipher encrypt equivalence" $ quickCheck prop_crypto_enc_eq
                       , test "cryptocipher decrypt equivalence" $ quickCheck prop_crypto_dec_eq
                       -- Test vectors
                       , test "all test vectors are correct" check_all_test_vectors
                       ]
  where prop_crypto_ksa_eq :: [Word8] -> Bool
        prop_crypto_ksa_eq key = (length key) > 1 ==> k1 == k2
          where k1 = let (v,_,_) = initCtx' key in sw2w $ arr2sw v
                k2 = let (v,_,_) = Crypto.initCtx key in V.toList v

        prop_crypto_enc_eq :: [Word8] -> [Word8] -> Bool
        prop_crypto_enc_eq key pt = (length key) > 1 ==> enc1 == enc2
          where (enc1,_) = encryptBS (initCtx' key) $ B.pack pt
                (_,enc2) = Crypto.encrypt (Crypto.initCtx key) $ B.pack pt
        
        prop_crypto_dec_eq :: [Word8] -> [Word8] -> Bool
        prop_crypto_dec_eq key pt = (length key) > 1 ==> dec1 == dec2
          where dec1 = let k       = initCtx' key
                           (enc,_) = encryptBS k $ B.pack pt
                           (dec,_) = decryptBS k enc
                       in dec
                dec2 = let k       = Crypto.initCtx key
                           (_,enc) = Crypto.encrypt k $ B.pack pt
                           (_,dec) = Crypto.decrypt k enc
                       in dec
        
        -- Test vectors
        check_test_vector :: RC4 -> Int -> [Word8] -> Bool
        check_test_vector st offset v = v == sw2w (take vl $ drop offset ks)
          where ks = keystream st
                vl = length v

        check_key_vectors :: [Word8] -> [(Int,[Word8])] -> IO () 
        check_key_vectors key vectors = do
          putStrLn $ "checking key " ++ show key ++ " (" ++ show (length key * 8) ++ "-bit)"
          let ctx = initCtx' key
          forM_ vectors $ \idx -> do
            let v = uncurry (check_test_vector ctx) idx
            unless v $ putStrLn $ "FAILURE: idx = " ++ show idx ++ ", vector = " ++ show vectors
        
        check_all_test_vectors :: IO ()
        check_all_test_vectors = mapM_ (uncurry check_key_vectors) vecs
          where vecs = [ ([1..5], 
                            [ (0x0,    [0xb2, 0x39, 0x63, 0x05, 0xf0, 0x3d, 0xc0, 0x27, 0xcc, 0xc3, 0x52, 0x4a, 0x0a, 0x11, 0x18, 0xa8])
                            , (0x10,   [0x69, 0x82, 0x94, 0x4f, 0x18, 0xfc, 0x82, 0xd5, 0x89, 0xc4, 0x03, 0xa4, 0x7a, 0x0d, 0x09, 0x19])
                            , (0xf0,   [0x28, 0xcb, 0x11, 0x32, 0xc9, 0x6c, 0xe2, 0x86, 0x42, 0x1d, 0xca, 0xad, 0xb8, 0xb6, 0x9e, 0xae])
                            , (0x100,  [0x1c, 0xfc, 0xf6, 0x2b, 0x03, 0xed, 0xdb, 0x64, 0x1d, 0x77, 0xdf, 0xcf, 0x7f, 0x8d, 0x8c, 0x93])
                            , (0x1f0,  [0x42, 0xb7, 0xd0, 0xcd, 0xd9, 0x18, 0xa8, 0xa3, 0x3d, 0xd5, 0x17, 0x81, 0xc8, 0x1f, 0x40, 0x41])
                            , (0x200,  [0x64, 0x59, 0x84, 0x44, 0x32, 0xa7, 0xda, 0x92, 0x3c, 0xfb, 0x3e, 0xb4, 0x98, 0x06, 0x61, 0xf6])
                            , (0x2f0,  [0xec, 0x10, 0x32, 0x7b, 0xde, 0x2b, 0xee, 0xfd, 0x18, 0xf9, 0x27, 0x76, 0x80, 0x45, 0x7e, 0x22])
                            , (0x300,  [0xeb, 0x62, 0x63, 0x8d, 0x4f, 0x0b, 0xa1, 0xfe, 0x9f, 0xca, 0x20, 0xe0, 0x5b, 0xf8, 0xff, 0x2b])
                            , (0x3f0,  [0x45, 0x12, 0x90, 0x48, 0xe6, 0xa0, 0xed, 0x0b, 0x56, 0xb4, 0x90, 0x33, 0x8f, 0x07, 0x8d, 0xa5])
                            , (0x400,  [0x30, 0xab, 0xbc, 0xc7, 0xc2, 0x0b, 0x01, 0x60, 0x9f, 0x23, 0xee, 0x2d, 0x5f, 0x6b, 0xb7, 0xdf])
                            , (0x5f0,  [0x32, 0x94, 0xf7, 0x44, 0xd8, 0xf9, 0x79, 0x05, 0x07, 0xe7, 0x0f, 0x62, 0xe5, 0xbb, 0xce, 0xea])
                            , (0x600,  [0xd8, 0x72, 0x9d, 0xb4, 0x18, 0x82, 0x25, 0x9b, 0xee, 0x4f, 0x82, 0x53, 0x25, 0xf5, 0xa1, 0x30])
                            , (0x7f0,  [0x1e, 0xb1, 0x4a, 0x0c, 0x13, 0xb3, 0xbf, 0x47, 0xfa, 0x2a, 0x0b, 0xa9, 0x3a, 0xd4, 0x5b, 0x8b])
                            , (0x800,  [0xcc, 0x58, 0x2f, 0x8b, 0xa9, 0xf2, 0x65, 0xe2, 0xb1, 0xbe, 0x91, 0x12, 0xe9, 0x75, 0xd2, 0xd7])
                            , (0xbf0,  [0xf2, 0xe3, 0x0f, 0x9b, 0xd1, 0x02, 0xec, 0xbf, 0x75, 0xaa, 0xad, 0xe9, 0xbc, 0x35, 0xc4, 0x3c])
                            , (0xc00,  [0xec, 0x0e, 0x11, 0xc4, 0x79, 0xdc, 0x32, 0x9d, 0xc8, 0xda, 0x79, 0x68, 0xfe, 0x96, 0x56, 0x81])
                            , (0xff0,  [0x06, 0x83, 0x26, 0xa2, 0x11, 0x84, 0x16, 0xd2, 0x1f, 0x9d, 0x04, 0xb2, 0xcd, 0x1c, 0xa0, 0x50])
                            , (0x1000, [0xff, 0x25, 0xb5, 0x89, 0x95, 0x99, 0x67, 0x07, 0xe5, 0x1f, 0xbd, 0xf0, 0x8b, 0x34, 0xd8, 0x75])
                            ])
                         {-
                       , ([1..7],
                            [ (0x0,    [])
                            , (0x10,   [])
                            , (0xf0,   [])
                            , (0x100,  [])
                            , (0x1f0,  [])
                            , (0x200,  [])
                            , (0x2f0,  [])
                            , (0x300,  [])
                            , (0x3f0,  [])
                            , (0x400,  [])
                            , (0x5f0,  [])
                            , (0x600,  [])
                            , (0x7f0,  [])
                            , (0x800,  [])
                            , (0xbf0,  [])
                            , (0xc00,  [])
                            , (0xff0,  [])
                            , (0x1000, [])
                            ])
                       , ([1..8],
                            [ (0x0,    [])
                            , (0x10,   [])
                            , (0xf0,   [])
                            , (0x100,  [])
                            , (0x1f0,  [])
                            , (0x200,  [])
                            , (0x2f0,  [])
                            , (0x300,  [])
                            , (0x3f0,  [])
                            , (0x400,  [])
                            , (0x5f0,  [])
                            , (0x600,  [])
                            , (0x7f0,  [])
                            , (0x800,  [])
                            , (0xbf0,  [])
                            , (0xc00,  [])
                            , (0xff0,  [])
                            , (0x1000, [])
                            ])
                       , ([1..0x0a],
                            [ (0x0,    [])
                            , (0x10,   [])
                            , (0xf0,   [])
                            , (0x100,  [])
                            , (0x1f0,  [])
                            , (0x200,  [])
                            , (0x2f0,  [])
                            , (0x300,  [])
                            , (0x3f0,  [])
                            , (0x400,  [])
                            , (0x5f0,  [])
                            , (0x600,  [])
                            , (0x7f0,  [])
                            , (0x800,  [])
                            , (0xbf0,  [])
                            , (0xc00,  [])
                            , (0xff0,  [])
                            , (0x1000, [])
                            ])
                       , ([1..0x10],
                            [ (0x0,    [])
                            , (0x10,   [])
                            , (0xf0,   [])
                            , (0x100,  [])
                            , (0x1f0,  [])
                            , (0x200,  [])
                            , (0x2f0,  [])
                            , (0x300,  [])
                            , (0x3f0,  [])
                            , (0x400,  [])
                            , (0x5f0,  [])
                            , (0x600,  [])
                            , (0x7f0,  [])
                            , (0x800,  [])
                            , (0xbf0,  [])
                            , (0xc00,  [])
                            , (0xff0,  [])
                            , (0x1000, [])
                            ])
                       , ([1..0x18],
                            [ (0x0,    [])
                            , (0x10,   [])
                            , (0xf0,   [])
                            , (0x100,  [])
                            , (0x1f0,  [])
                            , (0x200,  [])
                            , (0x2f0,  [])
                            , (0x300,  [])
                            , (0x3f0,  [])
                            , (0x400,  [])
                            , (0x5f0,  [])
                            , (0x600,  [])
                            , (0x7f0,  [])
                            , (0x800,  [])
                            , (0xbf0,  [])
                            , (0xc00,  [])
                            , (0xff0,  [])
                            , (0x1000, [])
                            ])
                       , ([1..0x20],
                            [ (0x0,    [])
                            , (0x10,   [])
                            , (0xf0,   [])
                            , (0x100,  [])
                            , (0x1f0,  [])
                            , (0x200,  [])
                            , (0x2f0,  [])
                            , (0x300,  [])
                            , (0x3f0,  [])
                            , (0x400,  [])
                            , (0x5f0,  [])
                            , (0x600,  [])
                            , (0x7f0,  [])
                            , (0x800,  [])
                            , (0xbf0,  [])
                            , (0xc00,  [])
                            , (0xff0,  [])
                            , (0x1000, [])
                            ])
                         
                       , ([0x83,0x32,0x22,0x77,0x2a],
                            [ (0x0,    [])
                            , (0x10,   [])
                            , (0xf0,   [])
                            , (0x100,  [])
                            , (0x1f0,  [])
                            , (0x200,  [])
                            , (0x2f0,  [])
                            , (0x300,  [])
                            , (0x3f0,  [])
                            , (0x400,  [])
                            , (0x5f0,  [])
                            , (0x600,  [])
                            , (0x7f0,  [])
                            , (0x800,  [])
                            , (0xbf0,  [])
                            , (0xc00,  [])
                            , (0xff0,  [])
                            , (0x1000, [])
                            ])
                       , ([0x19, 0x10, 0x83, 0x32, 0x22, 0x77, 0x2a],
                            [ (0x0,    [])
                            , (0x10,   [])
                            , (0xf0,   [])
                            , (0x100,  [])
                            , (0x1f0,  [])
                            , (0x200,  [])
                            , (0x2f0,  [])
                            , (0x300,  [])
                            , (0x3f0,  [])
                            , (0x400,  [])
                            , (0x5f0,  [])
                            , (0x600,  [])
                            , (0x7f0,  [])
                            , (0x800,  [])
                            , (0xbf0,  [])
                            , (0xc00,  [])
                            , (0xff0,  [])
                            , (0x1000, [])
                            ])
                       , ([0x64, 0x19, 0x10, 0x83, 0x32, 0x22, 0x77, 0x2a],
                            [ (0x0,    [])
                            , (0x10,   [])
                            , (0xf0,   [])
                            , (0x100,  [])
                            , (0x1f0,  [])
                            , (0x200,  [])
                            , (0x2f0,  [])
                            , (0x300,  [])
                            , (0x3f0,  [])
                            , (0x400,  [])
                            , (0x5f0,  [])
                            , (0x600,  [])
                            , (0x7f0,  [])
                            , (0x800,  [])
                            , (0xbf0,  [])
                            , (0xc00,  [])
                            , (0xff0,  [])
                            , (0x1000, [])
                            ])
                       , ([0x8b, 0x37, 0x64, 0x19, 0x10, 0x83, 0x32, 0x22, 0x77, 0x2a],
                            [ (0x0,    [])
                            , (0x10,   [])
                            , (0xf0,   [])
                            , (0x100,  [])
                            , (0x1f0,  [])
                            , (0x200,  [])
                            , (0x2f0,  [])
                            , (0x300,  [])
                            , (0x3f0,  [])
                            , (0x400,  [])
                            , (0x5f0,  [])
                            , (0x600,  [])
                            , (0x7f0,  [])
                            , (0x800,  [])
                            , (0xbf0,  [])
                            , (0xc00,  [])
                            , (0xff0,  [])
                            , (0x1000, [])
                            ])
                       , ([0xeb, 0xb4, 0x62, 0x27, 0xc6, 0xcc, 0x8b, 0x37, 0x64, 0x19, 0x10, 0x83, 0x32, 0x22, 0x77, 0x2a],
                            [ (0x0,    [])
                            , (0x10,   [])
                            , (0xf0,   [])
                            , (0x100,  [])
                            , (0x1f0,  [])
                            , (0x200,  [])
                            , (0x2f0,  [])
                            , (0x300,  [])
                            , (0x3f0,  [])
                            , (0x400,  [])
                            , (0x5f0,  [])
                            , (0x600,  [])
                            , (0x7f0,  [])
                            , (0x800,  [])
                            , (0xbf0,  [])
                            , (0xc00,  [])
                            , (0xff0,  [])
                            , (0x1000, [])
                            ])
                       , ([0xc1, 0x09, 0x16, 0x39, 0x08, 0xeb, 0xe5, 0x1d, 0xeb, 0xb4, 0x62, 0x27, 0xc6, 0xcc, 0x8b, 0x37, 0x64, 0x19, 0x10, 0x83, 0x32, 0x22, 0x77, 0x2a],
                            [ (0x0,    [])
                            , (0x10,   [])
                            , (0xf0,   [])
                            , (0x100,  [])
                            , (0x1f0,  [])
                            , (0x200,  [])
                            , (0x2f0,  [])
                            , (0x300,  [])
                            , (0x3f0,  [])
                            , (0x400,  [])
                            , (0x5f0,  [])
                            , (0x600,  [])
                            , (0x7f0,  [])
                            , (0x800,  [])
                            , (0xbf0,  [])
                            , (0xc00,  [])
                            , (0xff0,  [])
                            , (0x1000, [])
                            ])
                       , ([0x1a, 0xda, 0x31, 0xd5, 0xcf, 0x68, 0x82, 0x21, 0xc1, 0x09, 0x16, 0x39, 0x08, 0xeb, 0xe5, 0x1d, 0xeb, 0xb4, 0x62, 0x27, 0xc6, 0xcc, 0x8b, 0x37, 0x64, 0x19, 0x10, 0x83, 0x32, 0x22, 0x77, 0x2a],
                            [ (0x0,    [])
                            , (0x10,   [])
                            , (0xf0,   [])
                            , (0x100,  [])
                            , (0x1f0,  [])
                            , (0x200,  [])
                            , (0x2f0,  [])
                            , (0x300,  [])
                            , (0x3f0,  [])
                            , (0x400,  [])
                            , (0x5f0,  [])
                            , (0x600,  [])
                            , (0x7f0,  [])
                            , (0x800,  [])
                            , (0xbf0,  [])
                            , (0xc00,  [])
                            , (0xff0,  [])
                            , (0x1000, [])
                            ])
-}
                       ]
                
-- lazy keystream generation
keystream :: RC4 -> [SWord8]
keystream st = let (z,st') = prga st in z:(keystream st')

-- ByteString interface, used for testing.
initCtx' :: [Word8] -> RC4
initCtx' = initCtx . w2sw

encryptBS :: RC4 -> B.ByteString -> (B.ByteString, RC4)
encryptBS ctx bs
  = let (s,ctx') = encrypt ctx $ w2sw $ B.unpack bs
    in (toBS s,ctx')
  where toBS = B.pack . sw2w

decryptBS :: RC4 -> B.ByteString -> (B.ByteString, RC4)
decryptBS = encryptBS


-- | This gives a correctness theorem for 'swap' and proves it via the
-- SMT solver: if we 'swap' the same elements of an array twice in an
-- imperative fashion, the initial array and the resulting array
-- values are equivalent (i.e. @swap i j (swap i j a) == a@).
proveSwapIsCorrect :: IO ThmResult
proveSwapIsCorrect 
  = proveWith timingSMTCfg $ forAll_ $ \i j -> swapIsCorrect i j initState
  where swapIsCorrect :: SWord8 -> SWord8 -> S -> SBool
        swapIsCorrect i j a
          = let (x,y)   = (a .! i, a .! j)
                a1      = swap i j a
                a2      = swap i j a1
                (x',y') = (a2 .! i, a2 .! j)
            in (x .== x' &&& y .== y')

-- | Ensures encryption followed by decryption is the identity
-- function for 40bit keys and 40bit plaintext, and proves it via the
-- SMT solver.
proveRc4IsCorrect :: IO ThmResult
proveRc4IsCorrect
  = proveWith timingSMTCfg $ forAll_ $ \plaintext key -> rc4IsCorrect plaintext key
  where rc4IsCorrect :: (SWord8,SWord8,SWord8,SWord8,SWord8) -> (SWord8,SWord8,SWord8,SWord8,SWord8) -> SBool
        rc4IsCorrect (pt1,pt2,pt3,pt4,pt5) (k1,k2,k3,k4,k5)
          = let ctx     = initCtx [k1,k2,k3,k4,k5]
                (enc,_) = encrypt ctx [pt1,pt2,pt3,pt4,pt5]
                (dec,_) = decrypt ctx enc
            in dec .== [pt1,pt2,pt3,pt4,pt5]

-- | Run all tests and verification functions:
--  
--  * Runs all QuickCheck tests
-- 
--  * Verifies our 'swap' implementation is correct, via the SMT solver.
-- 
--  * Verifies that @decrypt . encrypt == id@, via the SMT solver.
-- 
-- The results:
-- 
-- @
--     *Data.SBV.Examples.CodeGeneration.RC4> doAllTests
--     testing: cryptocipher ksa equivalence
--     +++ OK, passed 100 tests.
--     testing: cryptocipher encrypt equivalence
--     +++ OK, passed 100 tests.
--     testing: cryptocipher decrypt equivalence
--     +++ OK, passed 100 tests.
--     verifying: swap is correct
--     ** Elapsed problem construction time: 0.960s
--     ** Elapsed translation time: 0.000s
--     ** Elapsed Yices time: 1.801s
--     verifying: rc4 is correct
--     ** Elapsed problem construction time: 15.578s
--     ** Elapsed translation time: 0.000s
--     ** Elapsed Yices time: 36.656s
--     *Data.SBV.Examples.CodeGeneration.RC4>
-- @
-- 
doAllTests :: IO ()
doAllTests = sequence_ [ checkProps
                       , verif "swap is correct" proveSwapIsCorrect
                       , verif "rc4 is correct"  proveRc4IsCorrect
                       ]

test, verif :: String -> IO a -> IO ()
test x f = putStrLn ("testing: "++x) >> f >> return ()
verif x f = putStrLn ("verifying: "++x) >> f >> return ()

--------------------------
-- Code generation

-- | Generate a C library, containing functions for doing RC4 encryption/decryption.
-- It generates a similar API to the one above: a function for initializing the RC4
-- context and key scheduling, as well as a single 'cipher' function that performs
-- both encryption and decryption. It uses 40bit keys and takes 64 byte inputs at
-- a time.
codegenRC4 :: IO ()
codegenRC4 = compileToCLib (Just "rc4_out") "rc4Lib" [ ("rc4_cipher_128", rc4_cipher)
                                                     , ("init_ctx_128", init_ctx)
                                                     ]
  where -- context initialization
        init_ctx = do key <- cgInputArr 5 "key"
                      let (s,i,j) = initCtx key
                      cgOutputArr "S" (arr2sw s)
                      cgOutput "i" i
                      cgOutput "j" j
        -- the cipher, which does both encryption and decryption
        rc4_cipher = do (pt::[SWord8]) <- cgInputArr 64 "plaintext"
                        (s::[SWord8])  <- cgInputArr 128 "S"
                        (i::SWord8)    <- cgInput "i"
                        (j::SWord8)    <- cgInput "j"
                        let (ct,(s',i',j')) = encrypt (sw2arr s,i,j) pt
                        cgOutputArr "S_out" (arr2sw s')
                        cgOutput "i_out" i'
                        cgOutput "j_out" j'
                        cgOutputArr "ciphertext" ct

--------------------------
-- Utilities
(.!) :: S -> SWord8 -> SWord8
(.!) = readArray

sw2w :: [SWord8] -> [Word8]
sw2w = map (fromJust . unliteral)

w2sw :: [Word8] -> [SWord8]
w2sw = map literal

arr2sw :: S -> [SWord8]
arr2sw st = fst $ foldr k ([],st) [0..255]
  where k i (o,v) = let x = readArray v (literal i) 
                    in (x:o,v)

sw2arr :: [SWord8] -> S
sw2arr = foldr (\i a -> writeArray a i i) (mkSFunArray 0)
