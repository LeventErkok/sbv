-----------------------------------------------------------------------------
-- |
-- Module      :  Data.SBV.Examples.CodeGeneration.AES
-- Copyright   :  (c) Levent Erkok
-- License     :  BSD3
-- Maintainer  :  erkokl@gmail.com
-- Stability   :  experimental
-- Portability :  portable
--
-- An implementation of AES (Advanced Encryption Standard), using SBV.
-- For details on AES, see FIPS-197: <http://csrc.nist.gov/publications/fips/fips197/fips-197.pdf>.
--
-- We do a T-box implementation, which leads to good C code as we can take
-- advantage of look-up tables. Note that our program encodes look-up tables
-- programmatically using ordinary Haskell lists, which are turned to constant-time
-- access C arrays by the code generator automatically.
--
-- All 3 valid key sizes (128, 192, and 256) as required by the FIPS-197 standard
-- are supported.
-----------------------------------------------------------------------------

{-# LANGUAGE ParallelListComp #-}

module Data.SBV.Examples.CodeGeneration.AES where

import Data.SBV
import Data.List (transpose)
import Test.QuickCheck hiding ((==>))

-----------------------------------------------------------------------------
-- * AES API
-----------------------------------------------------------------------------

-- | Block encryption. The first argument is the plain-text, which must have
-- precisely 4 elements, for a total of 128-bits of input. The second
-- argument is the key, which must have 4 (for 128-bit key), 6 (for 192-bit
-- key), or 8 (for 256-bit key) elements. These lengths are enforced by
-- the function. The output will always have 4 32-bit words, which is the cipher-text.
aesEncrypt :: [SWord32] -> [SWord32] -> [SWord32]
aesEncrypt pt key
  | length pt == 4 && length key `elem` [4, 6, 8]
  = doRounds aesRound encKS pt
  | True
  = error "aesEncrypt: Received invalid input"
  where (encKS, _) = keySchedule key

-- | Block decryption. The arguments are the same as in 'aesEncrypt', except
-- the first argument is the cipher-text and the output is the corresponding
-- plain-text.
aesDecrypt :: [SWord32] -> [SWord32] -> [SWord32]
aesDecrypt ct key
  | length ct == 4 && length key `elem` [4, 6, 8]
  = doRounds aesInvRound decKS ct
  | True
  = error "aesDecrypt: Received invalid input"
  where (_, decKS) = keySchedule key

-----------------------------------------------------------------------------
-- * Formalizing GF(2^8)
-----------------------------------------------------------------------------

-- | An element of the Galois Field 2^8, which are essentially polynomials with
-- maximum degree 7. They are conveniently represented as values between 0 and 255.
type GF28 = SWord8

-- | Addition in GF(2^8). Addition corresponds to simple 'xor'. Note that we
-- define it for vectors of GF(2^8) values, as that version is more convenient to
-- use in AES.
gf28Add :: [GF28] -> [GF28] -> [GF28]
gf28Add = zipWith xor

-- | Multiplication in GF(2^8). This is simple polynomial multipliation, followed
-- by the irreducible polynomial @x^8+x^5+x^3+x^1+1@. We simply use the 'pMult'
-- function exported by SBV to do the operation. 
gf28Mult :: GF28 -> GF28 -> GF28
gf28Mult x y = pMult (x, y, [8, 4, 3, 1, 0])

-- | Exponentiation by a constant in GF(2^8). The implementation uses the usual
-- square-and-multiply trick to speed up the computation.
gf28Pow :: GF28 -> Int -> GF28
gf28Pow n k = pow k
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
-- >>> prove $ \x -> x ./= 0 ==> x `gf28Mult` gf28Inverse x .== 1
-- Q.E.D.
--
-- Note that we exclude @0@ in our theorem, as it does not have a
-- multiplicative inverse.
gf28Inverse :: GF28 -> GF28
gf28Inverse x = x `gf28Pow` 254

-- | Multiplication by 2 in GF(2^8). We use the standard bit-blasting trick
-- to obtain fast code.
gtimes2 :: GF28 -> GF28
gtimes2 g = fromBitsLE [b7, b0 <+> b7, b1, b2 <+> b7, b3 <+> b7, b4, b5, b6]
  where [b0, b1, b2, b3, b4, b5, b6, b7] = blastLE g

-- | Multiplication by 3 in GF(2^8)
gtimes3 g = gtimes2 g `xor` g
gtimesE g = select (map (`gf28Mult` 0xE) [0..255]) 0 g
gtimesB g = select (map (`gf28Mult` 0xB) [0..255]) 0 g
gtimesD g = select (map (`gf28Mult` 0xD) [0..255]) 0 g
gtimes9 g = select (map (`gf28Mult` 0x9) [0..255]) 0 g
-----------------------------------------------------------------------------
-- * Implementing AES
-----------------------------------------------------------------------------

-----------------------------------------------------------------------------
-- ** Types and basic operations
-----------------------------------------------------------------------------
-- | AES state. The state consists of four 32-bit words, each of which is in turn treated
-- as four GF28's, i.e., 4 bytes. The T-Box implementation keeps the four-bytes together
-- for efficient representation.
type State = [SWord32]

-- | The key, which can be 128, 192, or 256 bits. Represented as a sequence of 32-bit words.
type Key = [SWord32]

-- | The key schedule. AES executes in rounds, and it treats first and last round keys slightly
-- differently than the middle ones. We reflect that choice by being explicit about it in our type.
-- The length of the middle list of keys depends on the key-size, which in turn determines
-- the number of rounds.
type KS = (Key, [Key], Key)

-- | Conversion from 32-bit words to 4 constituent bytes.
toBytes :: SWord32 -> [GF28]
toBytes x = [x1, x2, x3, x4]
        where (h,  l)  = split x
              (x1, x2) = split h
              (x3, x4) = split l

-- | Conversion from 4 bytes, back to a 32-bit row, inverse of 'toBytes' above. We
-- have the following simple theorems stating this relationship formally:
--
-- >>> prove $ \a b c d -> toBytes (fromBytes [a, b, c, d]) .== [a, b, c, d]
-- Q.E.D.
--
-- >>> prove $ \r -> fromBytes (toBytes r) .== r
-- Q.E.D.
fromBytes :: [GF28] -> SWord32
fromBytes [x1, x2, x3, x4] = (x1 # x2) # (x3 # x4)
fromBytes xs               = error $ "fromBytes: Unexpected input: " ++ show xs

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
rcon :: Int -> [GF28]
rcon i = [roundConstants !! i, 0, 0, 0]
 where roundConstants :: [GF28]
       roundConstants = 0 : [ gf28Pow 2 (i-1) | i <- [1 .. ] ]

-- | The @SubWord@ function, as specified in Section 5.2 of the AES standard.
subWord :: [GF28] -> [GF28]
subWord = map sbox

-- | The @RotWord@ function, as specified in Section 5.2 of the AES standard.
rotWord :: [GF28] -> [GF28]
rotWord [a, b, c, d] = [b, c, d, a]
rotWord xs           = error $ "rotWord: Unexpected input: " ++ show xs

-- | Given a key, construct the key-schedules for encryption an decryption.
keySchedule :: Key -> (KS, KS)
keySchedule key = (encKS, decKS)
  where nk = length key
        nr = nk + 6
        encKS@(f, m, l) = (head rKeys, take (nr-1) (tail rKeys), rKeys !! nr)
        decKS = (l, map invMixColumns (reverse m), f)
        rKeys = keyExpansion nk key

-- | Key expansion. Starting with the given key, returns an infinite sequence of
-- words, as described by the AES standard.
keyExpansion :: Int -> Key -> [Key]
keyExpansion nk key = chop4 (map fromBytes keys)
   where keys :: [[GF28]]
         keys = map toBytes key ++ [nextWord i prev old | i <- [nk ..] | prev <- drop (nk-1) keys | old <- keys]
         chop4 :: [a] -> [[a]]
         chop4 xs = let (f, r) = splitAt 4 xs in f : chop4 r
         nextWord :: Int -> [GF28] -> [GF28] -> [GF28]
         nextWord i prev old
           | i `mod` nk == 0           = old `gf28Add` (subWord (rotWord prev) `gf28Add` rcon (i `div` nk))
           | i `mod` nk == 4 && nk > 6 = old `gf28Add` (subWord prev)
           | True                      = old `gf28Add` prev

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

-- | T-box table generation function.for encryption
t0Func :: GF28 -> [GF28]
t0Func a = [gtimes2 s, s, s, gtimes3 s] where s = sbox a

-- | First look-up table used in encryption
t0 :: GF28 -> SWord32
t0 = select t0Table 0 where t0Table = [fromBytes (t0Func a)          | a <- [0..255]]

-- | Second look-up table used in encryption
t1 :: GF28 -> SWord32
t1 = select t1Table 0 where t1Table = [fromBytes (t0Func a `rotR` 1) | a <- [0..255]]

-- | Third look-up table used in encryption
t2 :: GF28 -> SWord32
t2 = select t2Table 0 where t2Table = [fromBytes (t0Func a `rotR` 2) | a <- [0..255]]

-- | Fourth look-up table used in encryption
t3 :: GF28 -> SWord32
t3 = select t3Table 0 where t3Table = [fromBytes (t0Func a `rotR` 3) | a <- [0..255]]

-----------------------------------------------------------------------------
-- ** Tables for T-Box decryption
-----------------------------------------------------------------------------

-- | T-box table generating function for decryption
u0Func :: GF28 -> [GF28]
u0Func a = [gtimesE s, gtimes9 s, gtimesD s, gtimesB s] where s = unSBox a

-- | First look-up table used in decryption
u0 :: GF28 -> SWord32
u0 = select t0Table 0 where t0Table = [fromBytes (u0Func a)          | a <- [0..255]]

-- | Second look-up table used in decryption
u1 :: GF28 -> SWord32
u1 = select t1Table 0 where t1Table = [fromBytes (u0Func a `rotR` 1) | a <- [0..255]]

-- | Third look-up table used in decryption
u2 :: GF28 -> SWord32
u2 = select t2Table 0 where t2Table = [fromBytes (u0Func a `rotR` 2) | a <- [0..255]]

-- | Fourth look-up table used in decryption
u3 :: GF28 -> SWord32
u3 = select t3Table 0 where t3Table = [fromBytes (u0Func a `rotR` 3) | a <- [0..255]]


invMixColumns :: State -> State
invMixColumns state = map fromBytes $ transpose $ mmult m (map toBytes state)
 where dot v = foldr1 xor . zipWith ($) v
       mmult m n = [map (dot r) n | r <- m]

       m = [ [gtimesE, gtimesB, gtimesD, gtimes9]
           , [gtimes9, gtimesE, gtimesB, gtimesD]
           , [gtimesD, gtimes9, gtimesE, gtimesB]
           , [gtimesB, gtimesD, gtimes9, gtimesE]
           ]

-----------------------------------------------------------------------------
-- ** AES rounds
-----------------------------------------------------------------------------

-- | Generic round function. Given the function to perform one round, a key-schedule,
-- and a starting state, it performs the AES rounds.
doRounds :: (Bool -> State -> Key -> State) -> KS -> State -> State
doRounds round (ikey, rkeys, fkey) s = round True (last rs) fkey
  where s0 = ikey `addRoundKey` s
        rs = s0 : [round False s k | s <- rs | k <- rkeys ]

-- | One encryption round. The first argument indicates whether this is the final round
-- or not, in which case the construction is slightly different.
aesRound :: Bool -> State -> Key -> State
aesRound isFinal s key = d `addRoundKey` key
  where d = map (f isFinal) [0..3]
        a = map toBytes s
        f True j = e0 `xor` e1 `xor` e2 `xor` e3
              where e0 = fromBytes [sbox (a !! ((j+0) `mod` 4) !! 0), 0, 0, 0]
                    e1 = fromBytes [0, sbox (a !! ((j+1) `mod` 4) !! 1), 0, 0]
                    e2 = fromBytes [0, 0, sbox (a !! ((j+2) `mod` 4) !! 2), 0]
                    e3 = fromBytes [0, 0, 0, sbox (a !! ((j+3) `mod` 4) !! 3)]
        f False j = e0 `xor` e1 `xor` e2 `xor` e3
              where e0 = t0 (a !! ((j+0) `mod` 4) !! 0)
                    e1 = t1 (a !! ((j+1) `mod` 4) !! 1)
                    e2 = t2 (a !! ((j+2) `mod` 4) !! 2)
                    e3 = t3 (a !! ((j+3) `mod` 4) !! 3)

-- | One decryption round. The first argument indicates whether this is the final round
-- or not, in which case the construction is slightly different.
aesInvRound :: Bool -> State -> Key -> State
aesInvRound isFinal s key = d `addRoundKey` key
  where d = map (f isFinal) [0..3]
        a = map toBytes s
        f True j = e0 `xor` e1 `xor` e2 `xor` e3
              where e0 = fromBytes [unSBox (a !! ((j+0) `mod` 4) !! 0), 0, 0, 0]
                    e1 = fromBytes [0, unSBox (a !! ((j+3) `mod` 4) !! 1), 0, 0]
                    e2 = fromBytes [0, 0, unSBox (a !! ((j+2) `mod` 4) !! 2), 0]
                    e3 = fromBytes [0, 0, 0, unSBox (a !! ((j+1) `mod` 4) !! 3)]
        f False j = e0 `xor` e1 `xor` e2 `xor` e3
              where e0 = u0 (a !! ((j+0) `mod` 4) !! 0)
                    e1 = u1 (a !! ((j+3) `mod` 4) !! 1)
                    e2 = u2 (a !! ((j+2) `mod` 4) !! 2)
                    e3 = u3 (a !! ((j+1) `mod` 4) !! 3)

-- test stuff
t = do mapM_ hex2 (zip ct ctEx)
       print $ ct == ctEx
       mapM_ hex2 (zip ptGot pt)
       print $ pt == ptGot
  where key   = [0x00010203, 0x04050607, 0x08090a0b, 0x0c0d0e0f]
        pt    = [0x00112233, 0x44556677, 0x8899aabb, 0xccddeeff]
        ctEx  = [0x69c4e0d8, 0x6a7b0430, 0xd8cdb780, 0x70b4c55a]
        ct    = aesEncrypt pt key
        ptGot = aesDecrypt ct key
        hex2 (a, b) = putStrLn $ hex a ++ " " ++ hex b

cg = compileToC True (Just "aes") "aesEncrypt" ["pt0", "pt1", "pt2", "pt3", "key0", "key1", "key2", "key3"] enc
  where enc (a, b, c, d, e, f, g, h) = let [o0, o1, o2, o3] = aesEncrypt [a, b, c, d] [e, f, g, h]
                                       in (o0, o1, o2, o3)

cg' = compileToC True Nothing "aesEncrypt" ["pt0", "pt1", "pt2", "pt3", "key0", "key1", "key2", "key3"] enc
  where enc (a, b, c, d, e, f, g, h) = let [o0, o1, o2, o3] = aesEncrypt [a, b, c, d] [e, f, g, h]
                                       in (o0, o1, o2, o3)

roundtrip (i0, i1, i2, i3) (k0, k1, k2, k3) =  aesDecrypt (aesEncrypt i k) k .== i
  where i = [i0, i1, i2, i3]
        k = [k0, k1, k2, k3]
-- end test stuff

