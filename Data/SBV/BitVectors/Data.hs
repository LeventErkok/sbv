-----------------------------------------------------------------------------
-- |
-- Module      :  Data.SBV.BitVectors.Data
-- Copyright   :  (c) Levent Erkok
-- License     :  BSD3
-- Maintainer  :  erkokl@gmail.com
-- Stability   :  experimental
-- Portability :  portable
--
-- Internal data-structures for the sbv library
-----------------------------------------------------------------------------

{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Data.SBV.BitVectors.Data
 ( SBool, SWord8, SWord16, SWord32, SWord64
 , SInt8, SInt16, SInt32, SInt64
 , SymWord(..)
 , CW(..)
 , mkConstCW, liftCW2, mapCW, mapCW2
 , SW(..), trueSW, falseSW
 , SBV(..), NodeId(..), mkSymSBV
 , ArrayContext(..), ArrayInfo, SymArray(..), SFunArray(..), SArray(..)
 , sbvToSW
 , SBVExpr(..), newExpr
 , cache, uncache, HasSignAndSize(..)
 , Op(..), NamedSymVar, getTableIndex, Pgm, Symbolic, runSymbolic, State, Size, output, Result(..)
 ) where

import Control.Monad.Reader
import Control.DeepSeq(NFData(..))
import Data.Bits
import Data.Int
import Data.Word
import qualified Data.Foldable as F
import qualified Data.Sequence as S
import Data.SBV.BitVectors.Bit

import Data.IORef
import Data.List(intercalate, sortBy)
import qualified Data.Map    as Map
import qualified Data.IntMap as IMap

import Test.QuickCheck hiding(Result, output)

import System.IO.Unsafe -- see the note at the bottom of the file

-- | 'CW' represents a concrete word of a fixed size:
-- The unsigned variants are: 'W1', 'W8', 'W16', 'W32', and 'W64'
-- The signed variants are  : 'I8', 'I16', 'I32', I64'
-- Endianness is mostly irrelevant (see the 'FromBits' class).
-- For signed words, the most significant digit is considered to be the sign
data CW = W1  { wcToW1 :: Bit   }
        | W8  { wcToW8 :: Word8 }  | W16 { wcToW16 :: Word16} | W32 { wcToW32 :: Word32} | W64 { wcToW64 :: Word64 }
        | I8  { wcToI8 :: Int8  }  | I16 { wcToI16 :: Int16 } | I32 { wcToI32 :: Int32 } | I64 { wcToI64 :: Int64  }
        deriving (Eq, Ord)
type Size      = Int
newtype NodeId = NodeId Int
               deriving (Eq, Ord)
data SW        = SW (Bool, Size) NodeId
               deriving (Eq, Ord)

falseSW, trueSW :: SW
falseSW = SW (False, 1) $ NodeId (-2)
trueSW  = SW (False, 1) $ NodeId (-1)

data Op = Plus | Times | Minus
        | Quot | Rem -- quot and rem are unsigned only
        | Equal | NotEqual
        | LessThan | GreaterThan | LessEq | GreaterEq
        | Ite
        | And | Or  | XOr | Not
        | Shl Int | Shr Int | Rol Int | Ror Int
        | Extract Int Int -- Extract i j: extract bits i to j. Least significant bit is 0 (big-endian)
        | Join  -- Concat two words to form a bigger one, in the order given
        | LkUp (Int, Int, Int, Int) !SW !SW   -- (table-index, arg-type, res-type, length of the table) index out-of-bounds-value
        | ArrEq   Int Int
        | ArrRead Int
        deriving (Eq, Ord)
data SBVExpr = SBVApp {-# UNPACK #-} !Op {-# UNPACK #-} ![SW]
             deriving (Eq, Ord)

class HasSignAndSize a where
  sizeOf   :: a -> Size
  hasSign  :: a -> Bool
  showType :: a -> String
  showType a
    | not (hasSign a) && sizeOf a == 1 = "SBool"
    | True                             = if hasSign a then "SInt" else "SWord" ++ show (sizeOf a)

instance HasSignAndSize Bit    where {sizeOf _ =  1; hasSign _ = False}
instance HasSignAndSize Int8   where {sizeOf _ =  8; hasSign _ = True }
instance HasSignAndSize Word8  where {sizeOf _ =  8; hasSign _ = False}
instance HasSignAndSize Int16  where {sizeOf _ = 16; hasSign _ = True }
instance HasSignAndSize Word16 where {sizeOf _ = 16; hasSign _ = False}
instance HasSignAndSize Int32  where {sizeOf _ = 32; hasSign _ = True }
instance HasSignAndSize Word32 where {sizeOf _ = 32; hasSign _ = False}
instance HasSignAndSize Int64  where {sizeOf _ = 64; hasSign _ = True }
instance HasSignAndSize Word64 where {sizeOf _ = 64; hasSign _ = False}

liftCW :: (forall a. (Ord a, Bits a) => a -> b) -> CW -> b
liftCW f (W1  w) = f w
liftCW f (W8  w) = f w
liftCW f (W16 w) = f w
liftCW f (W32 w) = f w
liftCW f (W64 w) = f w
liftCW f (I8  w) = f w
liftCW f (I16 w) = f w
liftCW f (I32 w) = f w
liftCW f (I64 w) = f w

liftCW2 :: (forall a. (Ord a, Bits a) => a -> a -> b) -> CW -> CW -> b
liftCW2 f (W1  a) (W1  b) = a `f` b
liftCW2 f (W8  a) (W8  b) = a `f` b
liftCW2 f (W16 a) (W16 b) = a `f` b
liftCW2 f (W32 a) (W32 b) = a `f` b
liftCW2 f (W64 a) (W64 b) = a `f` b
liftCW2 f (I8  a) (I8  b) = a `f` b
liftCW2 f (I16 a) (I16 b) = a `f` b
liftCW2 f (I32 a) (I32 b) = a `f` b
liftCW2 f (I64 a) (I64 b) = a `f` b
liftCW2 _ a b = error $ "SBV.liftCW2: impossible, incompatible args received: " ++ show (a, b)

mapCW :: (forall a. (Ord a, Bits a) => a -> a) -> CW -> CW
mapCW f (W1  w) = W1  $ f w
mapCW f (W8  w) = W8  $ f w
mapCW f (W16 w) = W16 $ f w
mapCW f (W32 w) = W32 $ f w
mapCW f (W64 w) = W64 $ f w
mapCW f (I8  w) = I8  $ f w
mapCW f (I16 w) = I16 $ f w
mapCW f (I32 w) = I32 $ f w
mapCW f (I64 w) = I64 $ f w

mapCW2 :: (forall a. (Ord a, Bits a) => a -> a -> a) -> CW -> CW -> CW
mapCW2 f (W1  a) (W1  b) = W1   $ a `f` b
mapCW2 f (W8  a) (W8  b) = W8   $ a `f` b
mapCW2 f (W16 a) (W16 b) = W16  $ a `f` b
mapCW2 f (W32 a) (W32 b) = W32  $ a `f` b
mapCW2 f (W64 a) (W64 b) = W64  $ a `f` b
mapCW2 f (I8  a) (I8  b) = I8   $ a `f` b
mapCW2 f (I16 a) (I16 b) = I16  $ a `f` b
mapCW2 f (I32 a) (I32 b) = I32  $ a `f` b
mapCW2 f (I64 a) (I64 b) = I64  $ a `f` b
mapCW2 _ a       b       = error $ "SBV.mapCW2: impossible, incompatible args received: " ++ show (a, b)

instance HasSignAndSize CW where
  sizeOf  = liftCW bitSize
  hasSign = liftCW isSigned

instance HasSignAndSize SW where
  sizeOf  (SW (_, s) _) = s
  hasSign (SW (b, _) _) = b

instance Show CW where
  show (W1 b) = show (bit2Bool b)
  show w      = liftCW show w ++ " :: " ++ showType w

instance Show SW where
  show (SW _ (NodeId n))
    | n < 0 = "s_" ++ show (abs n)
    | True  = 's' : show n

instance Show Op where
  show (Shl i) = "<<"  ++ show i
  show (Shr i) = ">>"  ++ show i
  show (Rol i) = "<<<" ++ show i
  show (Ror i) = ">>>" ++ show i
  show (Extract i j) = "choose [" ++ show i ++ ":" ++ show j ++ "]"
  show (LkUp (ti, at, rt, l) i e)
        = "lookup(" ++ tinfo ++ ", " ++ show i ++ ", " ++ show e ++ ")"
        where tinfo = "table" ++ show ti ++ "(" ++ show at ++ " -> " ++ show rt ++ ", " ++ show l ++ ")"
  show (ArrEq i j)   = "array" ++ show i ++ " == array" ++ show j
  show (ArrRead i)   = "select array" ++ show i
  show op
    | Just s <- op `lookup` syms = s
    | True                       = error "impossible happened; can't find op!"
    where syms = [ (Plus, "+"), (Times, "*"), (Minus, "-")
                 , (Quot, "quot")
                 , (Rem,  "rem")
                 , (Equal, "=="), (NotEqual, "/=")
                 , (LessThan, "<"), (GreaterThan, ">"), (LessEq, "<"), (GreaterEq, ">")
                 , (Ite, "if_then_else")
                 , (And, "&"), (Or, "|"), (XOr, "^"), (Not, "~")
                 , (Join, "#")
                 ]

reorder :: SBVExpr -> SBVExpr
reorder s = case s of
              SBVApp op [a, b] | isCommutative op && a > b -> SBVApp op [b, a]
              _ -> s
  where isCommutative :: Op -> Bool
        isCommutative o = o `elem` [Plus, Times, Equal, NotEqual, And, Or, XOr]

instance Show SBVExpr where
  show (SBVApp Ite [t, a, b]) = unwords ["if", show t, "then", show a, "else", show b]
  show (SBVApp (Shl i) [a])   = unwords [show a, "<<", show i]
  show (SBVApp (Shr i) [a])   = unwords [show a, ">>", show i]
  show (SBVApp (Rol i) [a])   = unwords [show a, "<<<", show i]
  show (SBVApp (Ror i) [a])   = unwords [show a, ">>>", show i]
  show (SBVApp op  [a, b])    = unwords [show a, show op, show b]
  show (SBVApp op  args)      = unwords (show op : map show args)

-- | A program is a sequence of assignments
type Pgm         = S.Seq (SW, SBVExpr)

-- | 'NamedSymVar' pairs symbolic words and user given/automatically generated names
type NamedSymVar = (SW, String)

-- | Result of running a symbolic computation
data Result      = Result [NamedSymVar]                 -- inputs
                          [(SW, CW)]                    -- constants
                          [((Int, Int, Int), [SW])]     -- tables (automatically constructed)
                          [(Int, ArrayInfo)]            -- arrays (user specified)
                          Pgm                           -- assignments
                          [SW]                          -- outputs

instance Show Result where
  show (Result _ cs _ _ _ [r])
    | Just c <- r `lookup` cs
    = show c
  show (Result is cs ts as xs os)  = intercalate "\n" $
                   ["INPUTS"]
                ++ map shn is
                ++ ["CONSTANTS"]
                ++ map shc cs
                ++ ["TABLES"]
                ++ map sht ts
                ++ ["ARRAYS"]
                ++ map sha as
                ++ ["DEFINE"]
                ++ map (\(s, e) -> "  " ++ shs s ++ " = " ++ show e) (F.toList xs)
                ++ ["OUTPUTS"]
                ++ map (("  " ++) . show) os
    where shs sw = show sw ++ " :: " ++ showType sw
          sht ((i, at, rt), es)  = "  Table " ++ show i ++ " : " ++ show at ++ "->" ++ show rt ++ " = " ++ show es
          shc (sw, cw) = "  " ++ show sw ++ " = " ++ show cw
          shn (sw, nm) = "  " ++ ni ++ " :: " ++ showType sw ++ alias
            where ni = show sw
                  alias | ni == nm = ""
                        | True     = ", aliasing " ++ show nm
          sha (i, (nm, (ai, bi), ctx)) = "  " ++ ni ++ " :: " ++ mkT ai ++ " -> " ++ mkT bi ++ alias
                                       ++ "\n     Context: "     ++ show ctx
            where mkT (b, s)
                   | s == 1  = "SBool"
                   | True    = if b then "SInt" else "SWord" ++ show s
                  ni = "array" ++ show i
                  alias | ni == nm = ""
                        | True     = ", aliasing " ++ show nm

data ArrayContext = ArrayFree
                  | ArrayInit SW
                  | ArrayMutate Int SW SW
                  | ArrayMerge  SW Int Int

instance Show ArrayContext where
  show ArrayFree           = " initialized with random elements"
  show (ArrayInit s)       = " initialized with " ++ show s ++ ":: " ++ showType s
  show (ArrayMutate i a b) = " cloned from array" ++ show i ++ " with " ++ show a ++ " :: " ++ showType a ++ " |-> " ++ show b ++ " :: " ++ showType b
  show (ArrayMerge s i j)  = " merged arrays " ++ show i ++ " and " ++ show j ++ " on condition " ++ show s

type ExprMap    = Map.Map SBVExpr SW
type CnstMap    = Map.Map CW SW
type TableMap   = Map.Map [SW] (Int, Int, Int)
type ArrayInfo  = (String, ((Bool, Size), (Bool, Size)), ArrayContext)
type ArrayMap   = IMap.IntMap ArrayInfo

data State  = State { rctr       :: IORef Int
                    , rinps      :: IORef [NamedSymVar]
                    , routs      :: IORef [SW]
                    , rtblMap    :: IORef TableMap
                    , spgm       :: IORef Pgm
                    , rconstMap  :: IORef CnstMap
                    , rexprMap   :: IORef ExprMap
                    , rArrayMap  :: IORef ArrayMap
                    }

-- | The "Symbolic" value. Either a constant (@Left@) or a symbolic
-- value (@Right Cached@). Note that caching is essential for making
-- sure sharing is preserved. The parameter 'a' is phantom, but is
-- extremely important in keeping the user interface strongly typed.
data SBV a = SBV !(Bool, Size) !(Either CW (Cached SW))

-- | A symbolic boolean/bit
type SBool   = SBV Bool

-- | 8-bit unsigned symbolic value
type SWord8  = SBV Word8

-- | 16-bit unsigned symbolic value
type SWord16 = SBV Word16

-- | 32-bit unsigned symbolic value
type SWord32 = SBV Word32

-- | 64-bit unsigned symbolic value
type SWord64 = SBV Word64

-- | 8-bit signed symbolic value, 2's complement representation
type SInt8   = SBV Int8

-- | 16-bit signed symbolic value, 2's complement representation
type SInt16  = SBV Int16

-- | 32-bit signed symbolic value, 2's complement representation
type SInt32  = SBV Int32

-- | 64-bit signed symbolic value, 2's complement representation
type SInt64  = SBV Int64

-- Needed to satisfy the Num hierarchy
instance Show (SBV a) where
  show (SBV _         (Left c))  = show c
  show (SBV (sgn, sz) (Right _)) = "<SBV> :: [" ++ show sz ++ (if sgn then "S" else "U") ++ "]"

instance Eq (SBV a) where
  SBV _ (Left a) == SBV _ (Left b) = a == b
  a == b = error $ "Comparing symbolic bit-vectors; Use (.==) instead. Received: " ++ show (a, b)
  SBV _ (Left a) /= SBV _ (Left b) = a /= b
  a /= b = error $ "Comparing symbolic bit-vectors; Use (./=) instead. Received: " ++ show (a, b)

instance HasSignAndSize (SBV a) where
  sizeOf  (SBV (_, s) _) = s
  hasSign (SBV (b, _) _) = b

incCtr :: State -> IO Int
incCtr s = do ctr <- readIORef (rctr s)
              let i = ctr + 1
              i `seq` writeIORef (rctr s) i
              return ctr

-- Create a new constant; hash-cons as necessary
newConst :: State -> CW -> IO SW
newConst st c = do
  constMap <- readIORef (rconstMap st)
  case c `Map.lookup` constMap of
    Just sw -> return sw
    Nothing -> do ctr <- incCtr st
                  let sw = SW (hasSign c, sizeOf c) (NodeId ctr)
                  modifyIORef (rconstMap st) (Map.insert c sw)
                  return sw

-- Create a new table; hash-cons as necessary
getTableIndex :: State -> Int -> Int -> [SW] -> IO Int
getTableIndex st at rt elts = do
  tblMap <- readIORef (rtblMap st)
  case elts `Map.lookup` tblMap of
    Just (i, _, _)  -> return i
    Nothing         -> do let i = Map.size tblMap
                          modifyIORef (rtblMap st) (Map.insert elts (i, at, rt))
                          return i

mkConstCW :: Integral a => (Bool, Size) -> a -> CW
mkConstCW (False, 1)  0 = W1  Zero
mkConstCW (False, 1)  1 = W1  One
mkConstCW (False, 8)  i = W8  (fromIntegral i)
mkConstCW (True,  8)  i = I8  (fromIntegral i)
mkConstCW (False, 16) i = W16 (fromIntegral i)
mkConstCW (True,  16) i = I16 (fromIntegral i)
mkConstCW (False, 32) i = W32 (fromIntegral i)
mkConstCW (True,  32) i = I32 (fromIntegral i)
mkConstCW (False, 64) i = W64 (fromIntegral i)
mkConstCW (True,  64) i = I64 (fromIntegral i)
mkConstCW sgnsz       i = error $ "SBV.mkConstCW: Received unexpected input: " ++ show (sgnsz, i)

-- Create a new expression; hash-cons as necessary
newExpr :: State -> (Bool, Size) -> SBVExpr -> IO SW
newExpr st sgnsz app = do
   let e = reorder app
   exprMap <- readIORef (rexprMap st)
   case e `Map.lookup` exprMap of
     Just sw -> return sw
     Nothing -> do ctr <- incCtr st
                   let sw = SW sgnsz (NodeId ctr)
                   modifyIORef (spgm st)     (flip (S.|>) (sw, e))
                   modifyIORef (rexprMap st) (Map.insert e sw)
                   return sw

sbvToSW :: State -> SBV a -> IO SW
sbvToSW st (SBV _ (Left c))  = newConst st c
sbvToSW st (SBV _ (Right f)) = uncache f st

-------------------------------------------------------------------------
-- * Symbolic Computations
-------------------------------------------------------------------------
-- | A Symbolic computation. Represented by a reader monad carrying the
-- state of the computation, layered on top of IO for creating unique
-- references to hold onto intermediate results.
newtype Symbolic a = Symbolic (ReaderT State IO a)
                   deriving (Monad, MonadIO, MonadReader State)

mkSymSBV :: (Bool, Size) -> Maybe String -> Symbolic (SBV a)
mkSymSBV sgnsz mbNm = do
        st <- ask
        ctr <- liftIO $ incCtr st
        let nm = maybe ('s':show ctr) id mbNm
            sw = SW sgnsz (NodeId ctr)
        liftIO $ modifyIORef (rinps st) ((sw, nm):)
        return $ SBV sgnsz $ Right $ cache (const (return sw))

-- | Mark an interim result as an output. Useful when constructing Symbolic programs
-- that return multiple values, or when the result is programmatically computed.
output :: SBV a -> Symbolic (SBV a)
output i@(SBV _ (Left c)) = do
        st <- ask
        sw <- liftIO $ newConst st c
        liftIO $ modifyIORef (routs st) (sw:)
        return i
output i@(SBV _ (Right f)) = do
        st <- ask
        sw <- liftIO $ uncache f st
        liftIO $ modifyIORef (routs st) (sw:)
        return i

-- | Run a symbolic computation and return a 'Result'
runSymbolic :: Symbolic a -> IO Result
runSymbolic (Symbolic c) = do
   ctr    <- newIORef (-2) -- start from -2; False and True will always occupy the first two elements
   pgm    <- newIORef S.empty
   emap   <- newIORef Map.empty
   cmap   <- newIORef Map.empty
   inps   <- newIORef []
   outs   <- newIORef []
   tables <- newIORef Map.empty
   arrays <- newIORef IMap.empty
   let st = State { rctr      = ctr
                  , rinps     = inps
                  , routs     = outs
                  , rtblMap   = tables
                  , spgm      = pgm
                  , rconstMap = cmap
                  , rArrayMap = arrays
                  , rexprMap  = emap
                  }
   _ <- newConst st $ W1 Zero -- s(-2) == falseSW
   _ <- newConst st $ W1 One  -- s(-1) == trueSW
   _ <- runReaderT c st
   rpgm  <- readIORef pgm
   inpsR <- readIORef inps
   outsR <- readIORef outs
   let swap (a, b) = (b, a)
       cmp  (a, _) (b, _) = a `compare` b
   cnsts <- (sortBy cmp . map swap . Map.toList) `fmap` readIORef (rconstMap st)
   tbls  <- (sortBy (\((x, _, _), _) ((y, _, _), _) -> x `compare` y) . map swap . Map.toList) `fmap` readIORef tables
   arrs  <- IMap.toAscList `fmap` readIORef arrays
   return $ Result (reverse inpsR) cnsts tbls arrs rpgm (reverse outsR)

-------------------------------------------------------------------------------
-- * Symbolic Words
-------------------------------------------------------------------------------
-- | A 'SymWord' is a potential symbolic bitvector that can be created instances of
-- to be fed to a symbolic program. Note that these methods are typically not needed
-- in casual uses with 'prove', 'sat', 'allSat' etc, as default instances automatically
-- provide the necessary bits.
class Ord a => SymWord a where
  -- | Create a user named input
  free       :: String -> Symbolic (SBV a)
  -- | Create an automatically named input
  free_      :: Symbolic (SBV a)
  -- | Turn a literal constant to symbolic
  literal    :: a -> SBV a
  -- | Extract a literal, if the value is concrete
  unliteral  :: SBV a -> Maybe a
  -- | Extract a literal, from a CW representation
  fromCW     :: CW -> a
  -- | Is the symbolic word concrete?
  isConcrete :: SBV a -> Bool
  -- | Is the symbolic word really symbolic?
  isSymbolic :: SBV a -> Bool

  -- | minimal complete definiton: free, free_, literal, fromCW
  unliteral (SBV _ (Left c))  = Just $ fromCW c
  unliteral _                 = Nothing
  isConcrete (SBV _ (Left _)) = True
  isConcrete _                = False
  isSymbolic = not . isConcrete

---------------------------------------------------------------------------------
-- * Symbolic Arrays
---------------------------------------------------------------------------------

-- | Flat arrays of symbolic values
-- An @array a b@ is an array indexed by the type @'SBV' a@, with elements of type @'SBV' b@
-- If an initial value is not provided in 'newArray_' and 'newArray' methods, then the elements
-- are left unspecified, i.e., the solver is free to choose any value. This is the right thing
-- to do if arrays are used as inputs to functions to be verified, typically. Reading an
-- uninitilized entry is an error.
-- While it's certainly possible for user to create instances of 'SymArray', the
-- 'SArray' and 'SFunArray' instances already provided should cover most use cases
-- in practice.
--
-- Minimal complete definition: All methods are required, no defaults.
class SymArray array where
  -- | Create a new array, with an optional initial value
  newArray_      :: (HasSignAndSize a, HasSignAndSize b) => Maybe (SBV b) -> Symbolic (array a b)
  -- | Create a named new array with, with an optional initial value
  newArray       :: (HasSignAndSize a, HasSignAndSize b) => String -> Maybe (SBV b) -> Symbolic (array a b)
  -- | Read the array element at @a@
  readArray      :: array a b -> SBV a -> SBV b
  -- | Reset all the elements of the array to the value @b@
  resetArray     :: SymWord b => array a b -> SBV b -> array a b
  -- | Update the element at @a@ to be @b@
  writeArray     :: SymWord b => array a b -> SBV a -> SBV b -> array a b
  -- | Merge two given arrays on the symbolic condition
  -- Intuitively: @mergeArrays cond a b = if cond then a else b@.
  -- Merging pushes the if-then-else choice down on to elements
  mergeArrays    :: SymWord b => SBV Bool -> array a b -> array a b -> array a b

-- | Arrays implemented in terms of SMT-arrays: <http://goedel.cs.uiowa.edu/smtlib/theories/ArraysEx.smt2>
data SArray a b = SArray ((Bool, Size), (Bool, Size)) (Cached ArrayIndex)
type ArrayIndex = Int

instance (HasSignAndSize a, HasSignAndSize b) => Show (SArray a b) where
  show (SArray{}) = "SArray<" ++ showType (undefined :: a) ++ ":" ++ showType (undefined :: b) ++ ">"

instance SymArray SArray where
  newArray_  = declNewSArray (\t -> "array" ++ show t)
  newArray n = declNewSArray (const n)
  readArray (SArray (_, bsgnsz) f) a = SBV bsgnsz $ Right $ cache r
     where r st = do arr <- uncache f st
                     i   <- sbvToSW st a
                     newExpr st bsgnsz (SBVApp (ArrRead arr) [i])
  resetArray (SArray ainfo _) b = SArray ainfo $ cache g
     where g st = do amap <- readIORef (rArrayMap st)
                     val <- sbvToSW st b
                     let j = IMap.size amap
                     j `seq` modifyIORef (rArrayMap st) (IMap.insert j ("array" ++ show j, ainfo, ArrayInit val))
                     return j
  writeArray (SArray ainfo f) a b = SArray ainfo $ cache g
     where g st = do arr  <- uncache f st
                     addr <- sbvToSW st a
                     val  <- sbvToSW st b
                     amap <- readIORef (rArrayMap st)
                     let j = IMap.size amap
                     j `seq` modifyIORef (rArrayMap st) (IMap.insert j ("array" ++ show j, ainfo, ArrayMutate arr addr val))
                     return j
  mergeArrays t (SArray ainfo a) (SArray _ b) = SArray ainfo $ cache h
    where h st = do ai <- uncache a st
                    bi <- uncache b st
                    ts <- sbvToSW st t
                    amap <- readIORef (rArrayMap st)
                    let k = IMap.size amap
                    k `seq` modifyIORef (rArrayMap st) (IMap.insert k ("array" ++ show k, ainfo, ArrayMerge ts ai bi))
                    return k

declNewSArray :: forall a b. (HasSignAndSize a, HasSignAndSize b) => (Int -> String) -> Maybe (SBV b) -> Symbolic (SArray a b)
declNewSArray mkNm mbInit = do
   let asgnsz = (hasSign (undefined :: a), sizeOf (undefined :: a))
       bsgnsz = (hasSign (undefined :: b), sizeOf (undefined :: b))
   st <- ask
   amap <- liftIO $ readIORef $ rArrayMap st
   let i = IMap.size amap
       nm = mkNm i
   actx <- case mbInit of
             Nothing   -> return ArrayFree
             Just ival -> liftIO $ ArrayInit `fmap` sbvToSW st ival
   liftIO $ modifyIORef (rArrayMap st) (IMap.insert i (nm, (asgnsz, bsgnsz), actx))
   return $ SArray (asgnsz, bsgnsz) $ cache $ const $ return i

-- | Arrays implemented internally as functions, and rendered as SMT-Lib functions
data SFunArray a b = SFunArray (SBV a -> SBV b)

instance (HasSignAndSize a, HasSignAndSize b) => Show (SFunArray a b) where
  show (SFunArray _) = "SFunArray<" ++ showType (undefined :: a) ++ ":" ++ showType (undefined :: b) ++ ">"

---------------------------------------------------------------------------------
-- * Cached values
---------------------------------------------------------------------------------

-- We implement a peculiar caching mechanism, applicable to the use case in
-- implementation of SBV's.  Whenever an SBV is used, we do not want to keep on
-- evaluating it in the then-current state. That will produce essentially a
-- semantically equivalent value. Thus, we want to run it only once, and reuse
-- that result.
--
-- Note that this is *not* a general memo utility!

newtype Cached a = Cached { uncache :: (State -> IO a) }

{-# NOINLINE cache #-}
cache :: (State -> IO a) -> Cached a
cache f = unsafePerformIO $ do
             storage <- newIORef Nothing
             return $ Cached (g storage)
  where g storage s = do mbb <- readIORef storage
                         case mbb of
                           Just x  -> return x
                           Nothing -> do r <- f s
                                         writeIORef storage (Just r)
                                         return r

{- The following would be a perfectly good definition of cache,
   except for performance:

cache = Cached
-}

-- Technicalities..
instance NFData CW where
  rnf (W1  w) = rnf w `seq` ()
  rnf (W8  w) = rnf w `seq` ()
  rnf (W16 w) = rnf w `seq` ()
  rnf (W32 w) = rnf w `seq` ()
  rnf (W64 w) = rnf w `seq` ()
  rnf (I8  w) = rnf w `seq` ()
  rnf (I16 w) = rnf w `seq` ()
  rnf (I32 w) = rnf w `seq` ()
  rnf (I64 w) = rnf w `seq` ()

instance NFData Result where
  rnf (Result inps consts tbls arrs pgm outs) = rnf inps `seq` rnf consts `seq` rnf tbls `seq` rnf arrs `seq` rnf pgm `seq` rnf outs

instance NFData ArrayContext
instance NFData Pgm
instance NFData SW

-- Quickcheck interface on symbolic-booleans..
instance Testable SBool where
  property (SBV _ (Left (W1 b))) = property . bit2Bool $ b
  property s                     = error $ "BV.Testable.SBool: impossible: quickcheck with non-constant bit: " ++ show s
