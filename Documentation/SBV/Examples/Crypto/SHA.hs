-----------------------------------------------------------------------------
-- |
-- Module    : Documentation.SBV.Examples.Crypto.SHA
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Implementation of SHA2 class of algorithms, closely following the spec
-- <http://nvlpubs.nist.gov/nistpubs/FIPS/NIST.FIPS.180-4.pdf>.
--
-- We support all variants of SHA in the spec, except for SHA1. Note that
-- this implementation is really useful for code-generation purposes from
-- SBV, as it is hard to state (or prove!) any particular properties of
-- these algorithms that is suitable for SMT solving.
-----------------------------------------------------------------------------

{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE NamedFieldPuns      #-}
{-# LANGUAGE Rank2Types          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications    #-}

{-# OPTIONS_GHC -Wall -Werror -Wno-incomplete-uni-patterns #-}

module Documentation.SBV.Examples.Crypto.SHA where

import Data.SBV
import Data.SBV.Tools.CodeGen

import Prelude hiding (Foldable(..))
import Data.Char (ord, toLower)
import Data.List (genericLength, length, foldl')
import Numeric   (showHex)

import Data.Proxy (Proxy(..))

-----------------------------------------------------------------------------
-- * Parameterizing SHA
-----------------------------------------------------------------------------

-- | Parameterized SHA representation, that captures all the differences
-- between variants of the algorithm. @w@ is the word-size type.
data SHA w = SHA { wordSize           :: Int              -- ^ Section 1           : Word size we operate with
                 , blockSize          :: Int              -- ^ Section 1           : Block size for messages
                 , sum0Coefficients   :: (Int, Int, Int)  -- ^ Section 4.1.2-3     : Coefficients of the Sum0 function
                 , sum1Coefficients   :: (Int, Int, Int)  -- ^ Section 4.1.2-3     : Coefficients of the Sum1 function
                 , sigma0Coefficients :: (Int, Int, Int)  -- ^ Section 4.1.2-3     : Coefficients of the sigma0 function
                 , sigma1Coefficients :: (Int, Int, Int)  -- ^ Section 4.1.2-3     : Coefficients of the sigma1 function
                 , shaConstants       :: [w]              -- ^ Section 4.2.2-3     : Magic SHA constants
                 , h0                 :: [w]              -- ^ Section 5.3.2-6     : Initial hash value
                 , shaLoopCount       :: Int              -- ^ Section 6.2.2, 6.4.2: How many iterations are there in the inner loop
                 }

-----------------------------------------------------------------------------
-- * Section 4.1.2, SHA functions
-----------------------------------------------------------------------------

-- | The choose function.
ch :: Bits a => a -> a -> a -> a
ch x y z = (x .&. y) `xor` (complement x .&. z)

-- | The majority function.
maj :: Bits a => a -> a -> a -> a
maj x y z = (x .&. y) `xor` (x .&. z) `xor` (y .&. z)

-- | The sum-0 function. We parameterize over the rotation amounts as different
-- variants of SHA use different rotation amounts.
sum0 :: Bits a => SHA w -> a -> a
sum0 SHA{sum0Coefficients = (a, b, c)} x = (x `rotateR` a) `xor` (x `rotateR` b) `xor` (x `rotateR` c)

-- | The sum-1 function. Again, parameterized.
sum1 :: Bits a => SHA w -> a -> a
sum1 SHA{sum1Coefficients = (a, b, c)} x = (x `rotateR` a) `xor` (x `rotateR` b) `xor` (x `rotateR` c)

-- | The sigma0 function. Parameterized.
sigma0 :: Bits a => SHA w -> a -> a
sigma0 SHA{sigma0Coefficients = (a, b, c)} x = (x `rotateR` a) `xor` (x `rotateR` b) `xor` (x `shiftR` c)

-- | The sigma1 function. Parameterized.
sigma1 :: Bits a => SHA w -> a -> a
sigma1 SHA{sigma1Coefficients = (a, b, c)} x = (x `rotateR` a) `xor` (x `rotateR` b) `xor` (x `shiftR` c)

-----------------------------------------------------------------------------
-- * SHA variants
-----------------------------------------------------------------------------

-- | Parameterization for SHA224.
sha224P :: SHA (SWord 32)
sha224P = SHA { wordSize           = 32
              , blockSize          = 512
              , sum0Coefficients   = ( 2, 13, 22)
              , sum1Coefficients   = ( 6, 11, 25)
              , sigma0Coefficients = ( 7, 18,  3)
              , sigma1Coefficients = (17, 19, 10)
              , shaConstants       = [ 0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5
                                     , 0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174
                                     , 0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da
                                     , 0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967
                                     , 0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85
                                     , 0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070
                                     , 0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3
                                     , 0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2
                                     ]
              , h0                 = [ 0xc1059ed8, 0x367cd507, 0x3070dd17, 0xf70e5939
                                     , 0xffc00b31, 0x68581511, 0x64f98fa7, 0xbefa4fa4
                                     ]
              , shaLoopCount       = 64
              }

-- | Parameterization for SHA256. Inherits mostly from SHA224.
sha256P :: SHA (SWord 32)
sha256P = sha224P { h0 = [ 0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a
                         , 0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19
                         ]
                  }

-- | Parameterization for SHA384.
sha384P :: SHA (SWord 64)
sha384P = SHA { wordSize           = 64
              , blockSize          = 1024
              , sum0Coefficients   = (28, 34, 39)
              , sum1Coefficients   = (14, 18, 41)
              , sigma0Coefficients = ( 1,  8,  7)
              , sigma1Coefficients = (19, 61,  6)
              , shaConstants       = [ 0x428a2f98d728ae22, 0x7137449123ef65cd, 0xb5c0fbcfec4d3b2f, 0xe9b5dba58189dbbc
                                     , 0x3956c25bf348b538, 0x59f111f1b605d019, 0x923f82a4af194f9b, 0xab1c5ed5da6d8118
                                     , 0xd807aa98a3030242, 0x12835b0145706fbe, 0x243185be4ee4b28c, 0x550c7dc3d5ffb4e2
                                     , 0x72be5d74f27b896f, 0x80deb1fe3b1696b1, 0x9bdc06a725c71235, 0xc19bf174cf692694
                                     , 0xe49b69c19ef14ad2, 0xefbe4786384f25e3, 0x0fc19dc68b8cd5b5, 0x240ca1cc77ac9c65
                                     , 0x2de92c6f592b0275, 0x4a7484aa6ea6e483, 0x5cb0a9dcbd41fbd4, 0x76f988da831153b5
                                     , 0x983e5152ee66dfab, 0xa831c66d2db43210, 0xb00327c898fb213f, 0xbf597fc7beef0ee4
                                     , 0xc6e00bf33da88fc2, 0xd5a79147930aa725, 0x06ca6351e003826f, 0x142929670a0e6e70
                                     , 0x27b70a8546d22ffc, 0x2e1b21385c26c926, 0x4d2c6dfc5ac42aed, 0x53380d139d95b3df
                                     , 0x650a73548baf63de, 0x766a0abb3c77b2a8, 0x81c2c92e47edaee6, 0x92722c851482353b
                                     , 0xa2bfe8a14cf10364, 0xa81a664bbc423001, 0xc24b8b70d0f89791, 0xc76c51a30654be30
                                     , 0xd192e819d6ef5218, 0xd69906245565a910, 0xf40e35855771202a, 0x106aa07032bbd1b8
                                     , 0x19a4c116b8d2d0c8, 0x1e376c085141ab53, 0x2748774cdf8eeb99, 0x34b0bcb5e19b48a8
                                     , 0x391c0cb3c5c95a63, 0x4ed8aa4ae3418acb, 0x5b9cca4f7763e373, 0x682e6ff3d6b2b8a3
                                     , 0x748f82ee5defb2fc, 0x78a5636f43172f60, 0x84c87814a1f0ab72, 0x8cc702081a6439ec
                                     , 0x90befffa23631e28, 0xa4506cebde82bde9, 0xbef9a3f7b2c67915, 0xc67178f2e372532b
                                     , 0xca273eceea26619c, 0xd186b8c721c0c207, 0xeada7dd6cde0eb1e, 0xf57d4f7fee6ed178
                                     , 0x06f067aa72176fba, 0x0a637dc5a2c898a6, 0x113f9804bef90dae, 0x1b710b35131c471b
                                     , 0x28db77f523047d84, 0x32caab7b40c72493, 0x3c9ebe0a15c9bebc, 0x431d67c49c100d4c
                                     , 0x4cc5d4becb3e42b6, 0x597f299cfc657e2a, 0x5fcb6fab3ad6faec, 0x6c44198c4a475817
                                     ]
              , h0                 = [ 0xcbbb9d5dc1059ed8, 0x629a292a367cd507, 0x9159015a3070dd17, 0x152fecd8f70e5939
                                     , 0x67332667ffc00b31, 0x8eb44a8768581511, 0xdb0c2e0d64f98fa7, 0x47b5481dbefa4fa4
                                     ]
              , shaLoopCount       = 80
              }

-- | Parameterization for SHA512. Inherits mostly from SHA384.
sha512P :: SHA (SWord 64)
sha512P = sha384P { h0 = [ 0x6a09e667f3bcc908, 0xbb67ae8584caa73b, 0x3c6ef372fe94f82b, 0xa54ff53a5f1d36f1
                         , 0x510e527fade682d1, 0x9b05688c2b3e6c1f, 0x1f83d9abfb41bd6b, 0x5be0cd19137e2179
                         ]
                  }

-- | Parameterization for SHA512_224. Inherits mostly from SHA512
sha512_224P :: SHA (SWord 64)
sha512_224P = sha512P { h0 = [ 0x8C3D37C819544DA2, 0x73E1996689DCD4D6, 0x1DFAB7AE32FF9C82, 0x679DD514582F9FCF
                             , 0x0F6D2B697BD44DA8, 0x77E36F7304C48942, 0x3F9D85A86A1D36C8, 0x1112E6AD91D692A1
                             ]
                      }

-- | Parameterization for SHA512_256. Inherits mostly from SHA512
sha512_256P :: SHA (SWord 64)
sha512_256P = sha512P { h0 = [ 0x22312194FC2BF72C, 0x9F555FA3C84C64C2, 0x2393B86B6F53B151, 0x963877195940EABD
                             , 0x96283EE2A88EFFE3, 0xBE5E1E2553863992, 0x2B0199FC2C85B8AA, 0x0EB72DDC81C52CA2
                             ]
                      }

-----------------------------------------------------------------------------
-- * Section 5, Preprocessing
-----------------------------------------------------------------------------

-- | 'Block' is a  synonym for lists, but makes the intent clear.
newtype Block a = Block [a]

-- | Prepare the message by turning it into blocks. We also check for the message
-- size requirement here. Note that this won't actually happen in practice as the input
-- length would be > 2^64 (or 2^128), and you'd run out of memory first!
prepareMessage :: forall w. (Num w, ByteConverter w) => SHA w -> String -> [Block w]
prepareMessage SHA{wordSize, blockSize} s
  | msgLen >= maxLen
  = error $ "Message is too big! Size: " ++ show msgLen ++ " Max: " ++ show maxLen
  | True
  = parse $ chunkBy (wordSize `div` 8) fromBytes padded
  where -- Maximum message size supported by the algorithm
        maxLen :: Integer
        maxLen = 2^(2 * fromIntegral wordSize :: Integer)

        -- Size of the input in bits
        msgLen :: Integer
        msgLen = 8 * genericLength s

        -- In all variants, we have 16-element blocks:
        --    SHA 224, 256                  :  512-bit block size with 32-bit word size: Total 16 words to a block
        --    SHA 384, 512, 512_224, 512_256: 1024-bit block size with 64-bit word size: Total 16 words to a block
        parse = chunkBy 16 Block

        msgSizeAsBytes :: [SWord 8]
        msgSizeAsBytes
          | wordSize == 32 = toBytes (fromIntegral msgLen :: SWord  64)
          | wordSize == 64 = toBytes (fromIntegral msgLen :: SWord 128)
          | True           = error $ "prepareMessage: Unexpected word size: " ++ show wordSize

        -- kLen is how many bits extra we need in the padding
        kLen :: Int
        kLen = blockSize - fromIntegral ((msgLen + fromIntegral (2 * wordSize)) `mod` fromIntegral blockSize)

        -- Since message is always a multiple of 8, we need to pad it with the byte 0x80 for the first byte
        -- after it (1000 0000), and then enough bytes to fill to make it a multiple of the block size.
        padded :: [SWord 8]
        padded = map (fromIntegral . ord) s ++ [0x80] ++ replicate ((kLen `div` 8) - 1) 0 ++ msgSizeAsBytes

-----------------------------------------------------------------------------
-- * Section 6.2.2 and 6.4.2, Hash computation
-----------------------------------------------------------------------------

-- | Hash one block of message, starting from a previous hash. This function
-- corresponds to body of the for-loop in the spec. This function always
-- produces a list of length 8, corresponding to the final 8 values of the @H@.
hashBlock :: (Num w, Bits w) => SHA w -> [w] -> Block w -> [w]
hashBlock p@SHA{shaLoopCount, shaConstants} hPrev (Block m) = step4
   where lim = shaLoopCount - 1

         -- Step 1: Prepare the message schedule:
         w t
          | 0  <= t && t <= 15  = m !! t
          | 16 <= t && t <= lim = sigma1 p (w (t-2)) + w (t-7) + sigma0 p (w (t-15)) + w (t-16)
          | True                = error $ "hashBlock, unexpected t: " ++ show t

         -- Step 2: Initialize working variables
         -- No code needed!

         -- Step 3 Body:
         step3Body [a, b, c, d, e, f, g, h] t = [t1 + t2, a, b, c, d + t1, e, f, g]
           where t1   = h + sum1 p e + ch e f g + shaConstants !! t + w t
                 t2   = sum0 p a + maj a b c
         step3Body xs t = error $ "Impossible! step3Body received a list of length " ++ show (length xs) ++ ", iteration: " ++ show t

         -- Step 3 simply folds the body for the required loop-count
         step3 = foldl' step3Body hPrev [0 .. lim]

         -- Step 4
         step4 = zipWith (+) step3 hPrev

-- | Compute the hash of a given string using the specified parameterized hash algorithm.
shaP :: (Num w, Bits w, ByteConverter w) => SHA w -> String -> [w]
shaP p@SHA{h0} = foldl' (hashBlock p) h0 . prepareMessage p

-----------------------------------------------------------------------------
-- * Computing the digest
-----------------------------------------------------------------------------

-- | SHA224 digest.
sha224 :: String -> SWord 224
sha224 s = h0 # h1 # h2 # h3 # h4 # h5 # h6
  where [h0, h1, h2, h3, h4, h5, h6, _] = shaP sha224P s

-- | SHA256 digest.
sha256 :: String -> SWord 256
sha256 s = h0 # h1 # h2 # h3 # h4 # h5 # h6 # h7
  where [h0, h1, h2, h3, h4, h5, h6, h7] = shaP sha256P s

-- | SHA384 digest.
sha384 :: String -> SWord 384
sha384 s = h0 # h1 # h2 # h3 # h4 # h5
  where [h0, h1, h2, h3, h4, h5, _, _] = shaP sha384P s

-- | SHA512 digest.
sha512 :: String -> SWord 512
sha512 s = h0 # h1 # h2 # h3 # h4 # h5 # h6 # h7
  where [h0, h1, h2, h3, h4, h5, h6, h7] = shaP sha512P s

-- | SHA512_224 digest.
sha512_224 :: String -> SWord 224
sha512_224 s = h0 # h1 # h2 # h3Top
  where [h0, h1, h2, h3, _, _, _, _] = shaP sha512_224P s
        h3Top                        = bvExtract (Proxy @63) (Proxy @32) h3

-- | SHA512_256 digest.
sha512_256 :: String -> SWord 256
sha512_256 s = h0 # h1 # h2 # h3
  where [h0, h1, h2, h3, _, _, _, _] = shaP sha512_256P s

-----------------------------------------------------------------------------
-- * Testing
-----------------------------------------------------------------------------

-- | Collection of known answer tests for SHA. Since these tests take too long during regular
-- regression runs, we pass as an argument how many to run. Increase the below number to 24 to run all tests.
-- We have:
--
-- >>> knownAnswerTests 1
-- True
knownAnswerTests :: Int -> Bool
knownAnswerTests nTest = and $  take nTest $  [showHash (sha224     t) == map toLower r | (t, r) <- sha224Kats    ]
                                           ++ [showHash (sha256     t) == map toLower r | (t, r) <- sha256Kats    ]
                                           ++ [showHash (sha384     t) == map toLower r | (t, r) <- sha384Kats    ]
                                           ++ [showHash (sha512     t) == map toLower r | (t, r) <- sha512Kats    ]
                                           ++ [showHash (sha512_224 t) == map toLower r | (t, r) <- sha512_224Kats]
                                           ++ [showHash (sha512_256 t) == map toLower r | (t, r) <- sha512_256Kats]

  where -- | From <http://github.com/bcgit/bc-java/blob/master/core/src/test/java/org/bouncycastle/crypto/test/SHA224DigestTest.java>
        sha224Kats :: [(String, String)]
        sha224Kats = [ (""                                                        , "d14a028c2a3a2bc9476102bb288234c415a2b01f828ea62ac5b3e42f")
                     , ("a"                                                       , "abd37534c7d9a2efb9465de931cd7055ffdb8879563ae98078d6d6d5")
                     , ("abc"                                                     , "23097d223405d8228642a477bda255b32aadbce4bda0b3f7e36c9da7")
                     , ("abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq", "75388b16512776cc5dba5da1fd890150b0c6455cb4f58b1952522525")
                     ]

        -- | From: <http://github.com/bcgit/bc-java/blob/master/core/src/test/java/org/bouncycastle/crypto/test/SHA256DigestTest.java>
        sha256Kats :: [(String, String)]
        sha256Kats = [ (""                                                        , "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855")
                     , ("a"                                                       , "ca978112ca1bbdcafac231b39a23dc4da786eff8147c4e72b9807785afee48bb")
                     , ("abc"                                                     , "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad")
                     , ("abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq", "248d6a61d20638b8e5c026930c3e6039a33ce45964ff2167f6ecedd419db06c1")
                     ]

        -- | From: <http://github.com/bcgit/bc-java/blob/master/core/src/test/java/org/bouncycastle/crypto/test/SHA384DigestTest.java>
        sha384Kats :: [(String, String)]
        sha384Kats = [ (""                                                                                                                , "38b060a751ac96384cd9327eb1b1e36a21fdb71114be07434c0cc7bf63f6e1da274edebfe76f65fbd51ad2f14898b95b")
                     , ("a"                                                                                                               , "54a59b9f22b0b80880d8427e548b7c23abd873486e1f035dce9cd697e85175033caa88e6d57bc35efae0b5afd3145f31")
                     , ("abc"                                                                                                             , "cb00753f45a35e8bb5a03d699ac65007272c32ab0eded1631a8b605a43ff5bed8086072ba1e7cc2358baeca134c825a7")
                     , ("abcdefghbcdefghicdefghijdefghijkefghijklfghijklmghijklmnhijklmnoijklmnopjklmnopqklmnopqrlmnopqrsmnopqrstnopqrstu", "09330c33f71147e83d192fc782cd1b4753111b173b3b05d22fa08086e3b0f712fcc7c71a557e2db966c3e9fa91746039")
                     ]

        -- | From: <http://github.com/bcgit/bc-java/blob/master/core/src/test/java/org/bouncycastle/crypto/test/SHA512DigestTest.java>
        sha512Kats :: [(String, String)]
        sha512Kats = [ (""                                                                                                                , "cf83e1357eefb8bdf1542850d66d8007d620e4050b5715dc83f4a921d36ce9ce47d0d13c5d85f2b0ff8318d2877eec2f63b931bd47417a81a538327af927da3e")
                     , ("a"                                                                                                               , "1f40fc92da241694750979ee6cf582f2d5d7d28e18335de05abc54d0560e0f5302860c652bf08d560252aa5e74210546f369fbbbce8c12cfc7957b2652fe9a75")
                     , ("abc"                                                                                                             , "ddaf35a193617abacc417349ae20413112e6fa4e89a97ea20a9eeee64b55d39a2192992a274fc1a836ba3c23a3feebbd454d4423643ce80e2a9ac94fa54ca49f")
                     , ("abcdefghbcdefghicdefghijdefghijkefghijklfghijklmghijklmnhijklmnoijklmnopjklmnopqklmnopqrlmnopqrsmnopqrstnopqrstu", "8e959b75dae313da8cf4f72814fc143f8f7779c6eb9f7fa17299aeadb6889018501d289e4900f7e4331b99dec4b5433ac7d329eeb6dd26545e96e55b874be909")
                     ]

        -- | From: <http://github.com/bcgit/bc-java/blob/master/core/src/test/java/org/bouncycastle/crypto/test/SHA512t224DigestTest.java>
        sha512_224Kats :: [(String, String)]
        sha512_224Kats = [ (""                                                                                                                , "6ed0dd02806fa89e25de060c19d3ac86cabb87d6a0ddd05c333b84f4")
                         , ("a"                                                                                                               , "d5cdb9ccc769a5121d4175f2bfdd13d6310e0d3d361ea75d82108327")
                         , ("abc"                                                                                                             , "4634270F707B6A54DAAE7530460842E20E37ED265CEEE9A43E8924AA")
                         , ("abcdefghbcdefghicdefghijdefghijkefghijklfghijklmghijklmnhijklmnoijklmnopjklmnopqklmnopqrlmnopqrsmnopqrstnopqrstu", "23FEC5BB94D60B23308192640B0C453335D664734FE40E7268674AF9")
                         ]

        -- | From: <http://github.com/bcgit/bc-java/blob/master/core/src/test/java/org/bouncycastle/crypto/test/SHA512t256DigestTest.java>
        sha512_256Kats :: [(String, String)]
        sha512_256Kats = [ (""                                                                                                                , "c672b8d1ef56ed28ab87c3622c5114069bdd3ad7b8f9737498d0c01ecef0967a")
                         , ("a"                                                                                                               , "455e518824bc0601f9fb858ff5c37d417d67c2f8e0df2babe4808858aea830f8")
                         , ("abc"                                                                                                             , "53048E2681941EF99B2E29B76B4C7DABE4C2D0C634FC6D46E0E2F13107E7AF23")
                         , ("abcdefghbcdefghicdefghijdefghijkefghijklfghijklmghijklmnhijklmnoijklmnopjklmnopqklmnopqrlmnopqrsmnopqrstnopqrstu", "3928E184FB8690F840DA3988121D31BE65CB9D3EF83EE6146FEAC861E19B563A")
                         ]

-----------------------------------------------------------------------------
-- * Code generation
-- ${codeGenIntro}
-----------------------------------------------------------------------------
{- $codeGenIntro
   It is not practical to generate SBV code for hashing an entire string, as it would
   require handling of a fixed size string. Instead we show how to generate code
   for hashing one block, which can then be incorporated into a larger program
   by providing the appropriate loop.
-}

-- | Generate code for one block of SHA256 in action, starting from an arbitrary hash value.
cgSHA256 :: IO ()
cgSHA256 = compileToC Nothing "sha256" $ do

        let algorithm = sha256P

        hInBytes   <- cgInputArr 32 "hIn"
        blockBytes <- cgInputArr 64 "block"

        let hIn   = chunkBy 4 fromBytes hInBytes
            block = chunkBy 4 fromBytes blockBytes

            result = hashBlock algorithm hIn (Block block)

        cgOutputArr "hash" $ concatMap toBytes result

-- | Generate code for one block of SHA512 in action, starting from an arbitrary hash value.
cgSHA512 :: IO ()
cgSHA512 = compileToC Nothing "sha512" $ do

        let algorithm = sha512P

        hInBytes   <- cgInputArr  64 "hIn"
        blockBytes <- cgInputArr 128 "block"

        let hIn   = chunkBy 8 fromBytes hInBytes
            block = chunkBy 8 fromBytes blockBytes

            result = hashBlock algorithm hIn (Block block)

        cgOutputArr "hash" $ concatMap toBytes result

-----------------------------------------------------------------------------
-- * Helpers
-----------------------------------------------------------------------------

-- | Helper for chunking a list by given lengths and combining each chunk with a function
chunkBy :: Int -> ([a] -> b) -> [a] -> [b]
chunkBy i f = go
  where go [] = []
        go xs
         | length first /= i = error $ "chunkBy: Not a multiple of " ++ show i ++ ", got: " ++ show (length first)
         | True              = f first : go rest
         where (first, rest) = splitAt i xs

-- | Nicely lay out a hash value as a string
showHash :: (Show a, Integral a, SymVal a) => SBV a -> String
showHash x = case (kindOf x, unliteral x) of
               (KBounded False n, Just v)  -> pad (n `div` 4) $ showHex v ""
               _                           -> error $ "Impossible happened: Unexpected hash value: " ++ show x
  where pad l s = reverse $ take l $ reverse s ++ repeat '0'
