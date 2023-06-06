-----------------------------------------------------------------------------
-- |
-- Module    : Documentation.SBV.Examples.Crypto.Prince
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Implementation of Prince encryption and decrytion, following the spec
-- <https://eprint.iacr.org/2012/529.pdf>
-----------------------------------------------------------------------------

{-# LANGUAGE DataKinds        #-}
{-# LANGUAGE ParallelListComp #-}

{-# OPTIONS_GHC -Wno-incomplete-uni-patterns #-}

module Documentation.SBV.Examples.Crypto.Prince where

import Prelude hiding(round)
import Numeric

import Data.SBV
import Data.SBV.Tools.CodeGen

-- $setup
-- >>> -- For doctest purposes only:
-- >>> import Data.SBV

-- * Types
-- | Section 2: Prince is essentially a 64-bit cipher, with 128-bit key, coming in two parts.
type Block = SWord 64

-- | Plantext is simply a block.
type PT = Block

-- | Key is again a 64-bit block.
type Key = Block

-- | Cypher text is another 64-bit block.
type CT = Block

-- | A nibble is 4-bits. Ideally, we would like to represent a nibble by @SWord 4@; and indeed SBV can do that for
-- verification purposes just fine. Unfortunately, the SBV's C compiler doesn't support 4-bit bit-vectors, as
-- there's nothing meaningful in the C-land that we can map it to. Thus, we represent a nibble with 8-bits. The
-- top 4 bits will always be 0.
type Nibble = SWord 8

-- * Key expansion

-- | Expanding a key, from Section 3.4 of the spec.
expandKey :: Key -> Key
expandKey k = (k `rotateR` 1) `xor` (k `shiftR` 63)

-- | expandKey(x) = x has a unique solution. We have:
--
-- >>> prop_ExpandKey
-- Q.E.D.
prop_ExpandKey :: IO ()
prop_ExpandKey = do let lim = 10
                    ms <- extractModels <$> allSatWith z3{allSatMaxModelCount = Just lim}
                                                       (\x -> x .== expandKey x)
                    case length ms of
                      0 -> putStrLn "No solutions to equation `x == expandKey x`!"
                      1 -> putStrLn "Q.E.D."
                      n -> do let qual = if n == lim then "at least " else ""
                              putStrLn $ "Failed. There are " ++ qual ++ show n ++ " solutions to `x == expandKey x`!"
                              mapM_ (\i -> putStrLn ("    " ++ show i)) (ms :: [WordN 64])


-- | Section 2: Encryption
encrypt :: PT -> Key -> Key -> CT
encrypt pt k0 k1 = prince k0 k0' k1 pt
   where k0' = expandKey k0

-- | Decryption
decrypt :: CT -> Key -> Key -> PT
decrypt ct k0 k1 = prince k0' k0 (k1 `xor` alpha) ct
  where k0'   = expandKey k0
        alpha = 0xc0ac29b7c97c50dd

-- * Main algorithm

-- | Basic prince algorithm
prince :: Block -> Key -> Key -> Key -> Block
prince k0 k0' k1 inp = out
   where start = inp `xor` k0
         end   = princeCore k1 start
         out   = end `xor` k0'

-- | Core prince. It's essentially folding of 12 rounds stitched together:
princeCore :: Key -> Block -> Block
princeCore k1 inp = end
   where start    = inp `xor` k1 `xor` rConstants 0
         front5   = foldl (round k1) start    [1 .. 5]
         midPoint = sBoxInv . m' . sBox $ front5
         back5    = foldl (invRound k1) midPoint [6..10]
         end      = back5 `xor` rConstants 11 `xor` k1

-- | Forward round.
round :: Key -> Block -> Int -> Block
round k1 b i = k1 `xor` rConstants i `xor` m (sBox b)

-- | Backend round.
invRound :: Key -> Block -> Int -> Block
invRound k1 b i = sBoxInv (mInv (rConstants i `xor` (b `xor` k1)))

-- | M transformation.
m :: Block -> Block
m = sr . m'

-- | Inverse of M.
mInv :: Block -> Block
mInv = m' . srInv

-- | SR.
sr :: Block -> Block
sr b = fromNibbles [n0, n5, n10, n15, n4, n9, n14, n3, n8, n13, n2, n7, n12, n1, n6, n11]
  where [n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15] = toNibbles b

-- | Inverse of SR:
srInv :: Block -> Block
srInv b = fromNibbles [n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15]
  where [n0, n5, n10, n15, n4, n9, n14, n3, n8, n13, n2, n7, n12, n1, n6, n11] = toNibbles b

-- | Prove sr and srInv are inverses: We have:
--
-- >>> prove prop_sr
-- Q.E.D.
prop_sr :: Predicate
prop_sr = do b <- free "block"
             return $   b .== sr (srInv b)
                    .&& b .== srInv (sr b)

-- | M' transformation
m' :: Block -> Block
m' = mMult

-- | The matrix as described in Section 3.3
mat :: [[Int]]
mat = res
  where m0 = [[0, 0, 0, 0], [0, 1, 0, 0], [0, 0, 1, 0], [0, 0, 0, 1]]
        m1 = [[1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 1, 0], [0, 0, 0, 1]]
        m2 = [[1, 0, 0, 0], [0, 1, 0, 0], [0, 0, 0, 0], [0, 0, 0, 1]]
        m3 = [[1, 0, 0, 0], [0, 1, 0, 0], [0, 0, 1, 0], [0, 0, 0, 0]]

        rows as bs cs ds = [a ++ b ++ c ++ d | a <- as | b <- bs | c <- cs | d <- ds ]

        m0' = concat [rows m0 m1 m2 m3, rows m1 m2 m3 m0, rows m2 m3 m0 m1, rows m3 m0 m1 m2]
        m1' = concat [rows m1 m2 m3 m0, rows m2 m3 m0 m1, rows m3 m0 m1 m2, rows m0 m1 m2 m3]

        zs  = replicate 16 (replicate 16 0)
        res = concat [rows m0' zs  zs  zs, rows zs  m1' zs  zs, rows zs  zs  m1' zs, rows zs  zs  zs  m0']

-- | Multiplication.
mMult :: Block -> Block
mMult b | length mat /= 64           = error $ "mMult: Expected 64 rows, got       : " ++ show (length mat)
        | any ((/= 64) . length) mat = error $ "mMult: Expected 64 on each row, got: " ++ show [p | p@(_, l) <- zip [(1::Int)..] (map length mat), l /= 64]
        | True                       = fromBitsBE $ map mult mat
  where bits = blastBE b

        mult :: [Int] -> SBool
        mult row = foldr (.<+>) sFalse $ zipWith mul row bits

        mul :: Int -> SBool -> SBool
        mul 0 _ = sFalse
        mul 1 v = v
        mul i _ = error $ "mMult: Unexpected constant: " ++ show i

-- | Non-linear transformation of a block
nonLinear :: [Nibble] -> Nibble -> Block -> Block
nonLinear box def = fromNibbles . map s . toNibbles
  where s :: Nibble -> Nibble
        s = select box def

-- | SBox transformation.
sBox :: Block -> Block
sBox = nonLinear [0xB, 0xF, 0x3, 0x2, 0xA, 0xC, 0x9, 0x1, 0x6, 0x7, 0x8, 0x0, 0xE, 0x5, 0xD, 0x4] 0x0

-- | Inverse SBox transformation.
sBoxInv :: Block -> Block
sBoxInv = nonLinear [0xB, 0x7, 0x3, 0x2, 0xF, 0xD, 0x8, 0x9, 0xA, 0x6, 0x4, 0x0, 0x5, 0xE, 0xC, 0x1] 0x0

-- | Prove that sbox and sBoxInv are inverses: We have:
--
-- >>> prove prop_SBox
-- Q.E.D.
prop_SBox :: Predicate
prop_SBox = do b <- free "block"
               return $   b .== sBoxInv (sBox b)
                      .&& b .== sBox (sBoxInv b)

-- * Round constants

-- | Round constants
rConstants :: Int -> SWord 64
rConstants  0 = 0x0000000000000000
rConstants  1 = 0x13198a2e03707344
rConstants  2 = 0xa4093822299f31d0
rConstants  3 = 0x082efa98ec4e6c89
rConstants  4 = 0x452821e638d01377
rConstants  5 = 0xbe5466cf34e90c6c
rConstants  6 = 0x7ef84f78fd955cb1
rConstants  7 = 0x85840851f1ac43aa
rConstants  8 = 0xc882d32f25323c54
rConstants  9 = 0x64a51195e0e3610d
rConstants 10 = 0xd3b5a399ca0c2399
rConstants 11 = 0xc0ac29b7c97c50dd
rConstants n  = error $ "rConstants called with invalid round number: " ++ show n

-- | Round-constants property: rc_i `xor` rc_{11-i} is constant. We have:
--
-- >>> prop_RoundKeys
-- True
prop_RoundKeys :: SBool
prop_RoundKeys = sAnd [magic .== rConstants i `xor` rConstants (11-i) | i <- [0 .. 11]]
  where magic = rConstants 11

-- | Convert a 64 bit word to nibbles
toNibbles :: SWord 64 -> [Nibble]
toNibbles = concatMap nibbles . toBytes
  where nibbles :: SWord 8 -> [Nibble]
        nibbles b = [b `shiftR` 4, b .&. 0xF]

-- | Convert from nibbles to a 64 bit word
fromNibbles :: [Nibble] -> SWord 64
fromNibbles xs
  | length xs /= 16 = error $ "fromNibbles: Incorrect number of nibbles, expected 16, got: " ++ show (length xs)
  | True            = fromBytes $ cvt xs
  where cvt (n1 : n2 : ns) = (n1 `shiftL` 4 .|. n2) : cvt ns
        cvt _              = []

-- * Test vectors

-- | From Appendix A of the spec. We have:
--
-- >>> testVectors
-- True
testVectors :: SBool
testVectors = sAnd $  [encrypt pt k0 k1 .== ct | (pt, k0, k1, ct) <- tvs]
                   ++ [decrypt ct k0 k1 .== pt | (pt, k0, k1, ct) <- tvs]
   where tvs :: [(SWord 64, SWord 64, SWord 64, SWord 64)]
         tvs = [ (0x0000000000000000, 0x0000000000000000, 0x0000000000000000, 0x818665aa0d02dfda)
               , (0xffffffffffffffff, 0x0000000000000000, 0x0000000000000000, 0x604ae6ca03c20ada)
               , (0x0000000000000000, 0xffffffffffffffff, 0x0000000000000000, 0x9fb51935fc3df524)
               , (0x0000000000000000, 0x0000000000000000, 0xffffffffffffffff, 0x78a54cbe737bb7ef)
               , (0x0123456789abcdef, 0x0000000000000000, 0xfedcba9876543210, 0xae25ad3ca8fa9ccf)
               ]

-- | Nicely show a concrete block.
showBlock :: Block -> String
showBlock b =  case unliteral b of
                 Just v  -> "0x" ++ pad (showHex v "")
                 Nothing -> error "showBlock: Symbolic input!"
  where pad s = reverse $ take 16 $ reverse s ++ repeat '0'

-- * Code generation

-- | Generating C code for the encryption block.
codeGen :: IO ()
codeGen = compileToC Nothing "enc" $ do
               input <- cgInput "inp"
               k0    <- cgInput "k0"
               k1    <- cgInput "k1"
               cgOverwriteFiles True
               cgOutput "ct"  $ encrypt input k0 k1
