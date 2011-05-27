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

{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE TypeSynonymInstances       #-}
{-# LANGUAGE TypeOperators              #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE PatternGuards              #-}

module Data.SBV.BitVectors.Data
 ( SBool, SWord8, SWord16, SWord32, SWord64
 , SInt8, SInt16, SInt32, SInt64
 , SymWord(..)
 , CW, cwVal, cwSameType, cwIsBit, cwToBool
 , mkConstCW ,liftCW2, mapCW, mapCW2
 , SW(..), trueSW, falseSW, trueCW, falseCW
 , SBV(..), NodeId(..), mkSymSBV
 , ArrayContext(..), ArrayInfo, SymArray(..), SFunArray(..), mkSFunArray, SArray(..), arrayUIKind
 , sbvToSW, sbvToSymSW
 , SBVExpr(..), newExpr
 , cache, uncache, uncacheAI, HasSignAndSize(..)
 , Op(..), NamedSymVar, UnintKind(..), getTableIndex, Pgm, Symbolic, runSymbolic, runSymbolic', State, Size, Outputtable(..), Result(..)
 , SBVType(..), newUninterpreted, unintFnUIKind, addAxiom
 ) where

import Control.DeepSeq                 (NFData(..))
import Control.Monad.Reader            (MonadReader, ReaderT, ask, runReaderT)
import Control.Monad.Trans             (MonadIO, liftIO)
import Data.Char                       (isAlpha, isAlphaNum)
import Data.Int                        (Int8, Int16, Int32, Int64)
import Data.Word                       (Word8, Word16, Word32, Word64)
import Data.IORef                      (IORef, newIORef, modifyIORef, readIORef, writeIORef)
import Data.List                       (intercalate, sortBy)

import qualified Data.IntMap   as IMap (IntMap, empty, size, toAscList, lookup, insert, insertWith)
import qualified Data.Map      as Map  (Map, empty, toList, size, insert, lookup)
import qualified Data.Foldable as F    (toList)
import qualified Data.Sequence as S    (Seq, empty, (|>))

import System.Mem.StableName
import Test.QuickCheck                 (Testable(..))

import Data.SBV.Utils.Lib

-- | 'CW' represents a concrete word of a fixed size:
-- Endianness is mostly irrelevant (see the 'FromBits' class).
-- For signed words, the most significant digit is considered to be the sign
data CW = CW { cwSigned :: !Bool, cwSize :: !Size, cwVal :: !Integer }
        deriving (Eq, Ord)

cwSameType :: CW -> CW -> Bool
cwSameType x y = cwSigned x == cwSigned y && cwSize x == cwSize y

cwIsBit :: CW -> Bool
cwIsBit x = not (cwSigned x) && cwSize x == 1

cwToBool :: CW -> Bool
cwToBool x = cwVal x /= 0

normCW :: CW -> CW
normCW x = x { cwVal = norm }
  where norm | cwSize x == 0  = 0
             | cwSigned x     = let rg = 2 ^ (cwSize x - 1)
                                in case divMod (cwVal x) rg of
                                    (a, b) | even a -> b
                                    (_, b)          -> b - rg
             | True           = cwVal x `mod` (2 ^ cwSize x)

type Size      = Int
newtype NodeId = NodeId Int deriving (Eq, Ord)
data SW        = SW (Bool, Size) NodeId deriving (Eq, Ord)

falseSW, trueSW :: SW
falseSW = SW (False, 1) $ NodeId (-2)
trueSW  = SW (False, 1) $ NodeId (-1)

falseCW, trueCW :: CW
falseCW = CW False 1 0
trueCW  = CW False 1 1

newtype SBVType = SBVType [(Bool, Size)]
             deriving (Eq, Ord)

-- how many arguments does the type take?
typeArity :: SBVType -> Int
typeArity (SBVType xs) = length xs - 1

instance Show SBVType where
  show (SBVType []) = error "SBV: internal error, empty SBVType"
  show (SBVType xs) = intercalate " -> " $ map sh xs
    where sh (False, 1) = "SBool"
          sh (s, sz)    = (if s then "SInt" else "SWord") ++ show sz

data Op = Plus | Times | Minus
        | Quot | Rem -- quot and rem are unsigned only
        | Equal | NotEqual
        | LessThan | GreaterThan | LessEq | GreaterEq
        | Ite
        | And | Or  | XOr | Not
        | Shl Int | Shr Int | Rol Int | Ror Int
        | Extract Int Int -- Extract i j: extract bits i to j. Least significant bit is 0 (big-endian)
        | Join  -- Concat two words to form a bigger one, in the order given
        | LkUp (Int, (Bool, Int), (Bool, Int), Int) !SW !SW   -- (table-index, arg-type, res-type, length of the table) index out-of-bounds-value
        | ArrEq   Int Int
        | ArrRead Int
        | Uninterpreted String
        deriving (Eq, Ord)
data SBVExpr = SBVApp !Op ![SW]
             deriving (Eq, Ord)

class HasSignAndSize a where
  sizeOf   :: a -> Size
  hasSign  :: a -> Bool
  showType :: a -> String
  showType a
    | not (hasSign a) && sizeOf a == 1 = "SBool"
    | True                             = (if hasSign a then "SInt" else "SWord") ++ show (sizeOf a)

instance HasSignAndSize Bool   where {sizeOf _ =  1; hasSign _ = False}
instance HasSignAndSize Int8   where {sizeOf _ =  8; hasSign _ = True }
instance HasSignAndSize Word8  where {sizeOf _ =  8; hasSign _ = False}
instance HasSignAndSize Int16  where {sizeOf _ = 16; hasSign _ = True }
instance HasSignAndSize Word16 where {sizeOf _ = 16; hasSign _ = False}
instance HasSignAndSize Int32  where {sizeOf _ = 32; hasSign _ = True }
instance HasSignAndSize Word32 where {sizeOf _ = 32; hasSign _ = False}
instance HasSignAndSize Int64  where {sizeOf _ = 64; hasSign _ = True }
instance HasSignAndSize Word64 where {sizeOf _ = 64; hasSign _ = False}

liftCW :: (Integer -> b) -> CW -> b
liftCW f x = f (cwVal x)

liftCW2 :: (Integer -> Integer -> b) -> CW -> CW -> b
liftCW2 f x y | cwSameType x y = f (cwVal x) (cwVal y)
liftCW2 _ a b = error $ "SBV.liftCW2: impossible, incompatible args received: " ++ show (a, b)

mapCW :: (Integer -> Integer) -> CW -> CW
mapCW f x  = normCW $ x { cwVal = f (cwVal x) }

mapCW2 :: (Integer -> Integer -> Integer) -> CW -> CW -> CW
mapCW2 f x y
  | cwSameType x y = normCW $ CW (cwSigned x) (cwSize y) (f (cwVal x) (cwVal y))
mapCW2 _ a b = error $ "SBV.mapCW2: impossible, incompatible args received: " ++ show (a, b)

instance HasSignAndSize CW where
  sizeOf  = cwSize
  hasSign = cwSigned

instance HasSignAndSize SW where
  sizeOf  (SW (_, s) _) = s
  hasSign (SW (b, _) _) = b

instance Show CW where
  show w | cwIsBit w = show (cwToBool w)
  show w             = liftCW show w ++ " :: " ++ showType w

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
  show (ArrEq i j)   = "array_" ++ show i ++ " == array_" ++ show j
  show (ArrRead i)   = "select array_" ++ show i
  show (Uninterpreted i) = "uninterpreted_" ++ i
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

-- | 'UnintKind' pairs array names and uninterpreted constants with their "kinds"
-- used mainly for printing counterexamples
data UnintKind = UFun Int String | UArr Int String      -- in each case, arity and the aliasing name
 deriving Show

-- | Result of running a symbolic computation
data Result = Result [NamedSymVar]                              -- inputs
                     [(SW, CW)]                                 -- constants
                     [((Int, (Bool, Int), (Bool, Int)), [SW])]  -- tables (automatically constructed) (tableno, index-type, result-type) elts
                     [(Int, ArrayInfo)]                         -- arrays (user specified)
                     [(String, SBVType)]                        -- uninterpreted constants
                     [(String, [String])]                       -- axioms
                     Pgm                                        -- assignments
                     [SW]                                       -- outputs

instance Show Result where
  show (Result _ cs _ _ [] [] _ [r])
    | Just c <- r `lookup` cs
    = show c
  show (Result is cs ts as uis axs xs os)  = intercalate "\n" $
                   ["INPUTS"]
                ++ map shn is
                ++ ["CONSTANTS"]
                ++ map shc cs
                ++ ["TABLES"]
                ++ map sht ts
                ++ ["ARRAYS"]
                ++ map sha as
                ++ ["UNINTERPRETED CONSTANTS"]
                ++ map shui uis
                ++ ["AXIOMS"]
                ++ map shax axs
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
                  ni = "array_" ++ show i
                  alias | ni == nm = ""
                        | True     = ", aliasing " ++ show nm
          shui (nm, t) = "  uninterpreted_" ++ nm ++ " :: " ++ show t
          shax (nm, ss) = "  -- user defined axiom: " ++ nm ++ "\n  " ++ intercalate "\n  " ss

data ArrayContext = ArrayFree (Maybe SW)
                  | ArrayReset Int SW
                  | ArrayMutate Int SW SW
                  | ArrayMerge  SW Int Int

instance Show ArrayContext where
  show (ArrayFree Nothing)  = " initialized with random elements"
  show (ArrayFree (Just s)) = " initialized with " ++ show s ++ " :: " ++ showType s
  show (ArrayReset i s)     = " reset array_" ++ show i ++ " with " ++ show s ++ " :: " ++ showType s
  show (ArrayMutate i a b)  = " cloned from array_" ++ show i ++ " with " ++ show a ++ " :: " ++ showType a ++ " |-> " ++ show b ++ " :: " ++ showType b
  show (ArrayMerge s i j)   = " merged arrays " ++ show i ++ " and " ++ show j ++ " on condition " ++ show s

type ExprMap   = Map.Map SBVExpr SW
type CnstMap   = Map.Map CW SW
type TableMap  = Map.Map [SW] (Int, (Bool, Int), (Bool, Int))
type ArrayInfo = (String, ((Bool, Size), (Bool, Size)), ArrayContext)
type ArrayMap  = IMap.IntMap ArrayInfo
type UIMap     = Map.Map String SBVType
type Cache a   = IMap.IntMap [(StableName (State -> IO a), a)]

unintFnUIKind :: (String, SBVType) -> (String, UnintKind)
unintFnUIKind (s, t) = (s, UFun (typeArity t) s)

arrayUIKind :: (Int, ArrayInfo) -> Maybe (String, UnintKind)
arrayUIKind (i, (nm, _, ctx)) 
  | external ctx = Just ("array_" ++ show i, UArr 1 nm) -- arrays are always 1-dimensional in the SMT-land. (Unless encoded explicitly)
  | True         = Nothing
  where external (ArrayFree{})   = True
        external (ArrayReset{})  = False
        external (ArrayMutate{}) = False
        external (ArrayMerge{})  = False

data State  = State { rctr       :: IORef Int
                    , rinps      :: IORef [NamedSymVar]
                    , routs      :: IORef [SW]
                    , rtblMap    :: IORef TableMap
                    , spgm       :: IORef Pgm
                    , rconstMap  :: IORef CnstMap
                    , rexprMap   :: IORef ExprMap
                    , rArrayMap  :: IORef ArrayMap
                    , rUIMap     :: IORef UIMap
                    , raxioms    :: IORef [(String, [String])]
                    , rSWCache   :: IORef (Cache SW)
                    , rAICache   :: IORef (Cache Int)
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
  show (SBV (sgn, sz) (Right _)) = "<symbolic> :: " ++ t
                where t | not sgn && sz == 1 = "SBool"
                        | True               = (if sgn then "SInt" else "SWord") ++ show sz

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

newUninterpreted :: State -> String -> SBVType -> IO ()
newUninterpreted st nm t
  | null nm || not (isAlpha (head nm)) || not (all isAlphaNum (tail nm))
  = error $ "Bad uninterpreted constant name: " ++ show nm ++ ". Must be a valid identifier."
  | True = do
        uiMap <- readIORef (rUIMap st)
        case nm `Map.lookup` uiMap of
          Just t' -> if t /= t'
                     then error $  "Uninterpreted constant " ++ show nm ++ " used at incompatible types\n"
                                ++ "      Current type      : " ++ show t ++ "\n"
                                ++ "      Previously used at: " ++ show t'
                     else return ()
          Nothing -> modifyIORef (rUIMap st) (Map.insert nm t)

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
getTableIndex :: State -> (Bool, Int) -> (Bool, Int) -> [SW] -> IO Int
getTableIndex st at rt elts = do
  tblMap <- readIORef (rtblMap st)
  case elts `Map.lookup` tblMap of
    Just (i, _, _)  -> return i
    Nothing         -> do let i = Map.size tblMap
                          modifyIORef (rtblMap st) (Map.insert elts (i, at, rt))
                          return i

-- Create a constant word
mkConstCW :: Integral a => (Bool, Size) -> a -> CW
mkConstCW (signed, size) a = normCW $ CW signed size (toInteger a)

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

sbvToSymSW :: SBV a -> Symbolic SW
sbvToSymSW sbv = do
        st <- ask
        liftIO $ sbvToSW st sbv

-- | Mark an interim result as an output. Useful when constructing Symbolic programs
-- that return multiple values, or when the result is programmatically computed.
class Outputtable a where
  output :: a -> Symbolic a

instance Outputtable (SBV a) where
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

instance (Outputtable a, Outputtable b) => Outputtable (a, b) where
  output = mlift2 (,) output output

instance (Outputtable a, Outputtable b, Outputtable c) => Outputtable (a, b, c) where
  output = mlift3 (,,) output output output

instance (Outputtable a, Outputtable b, Outputtable c, Outputtable d) => Outputtable (a, b, c, d) where
  output = mlift4 (,,,) output output output output

instance (Outputtable a, Outputtable b, Outputtable c, Outputtable d, Outputtable e) => Outputtable (a, b, c, d, e) where
  output = mlift5 (,,,,) output output output output output

instance (Outputtable a, Outputtable b, Outputtable c, Outputtable d, Outputtable e, Outputtable f) => Outputtable (a, b, c, d, e, f) where
  output = mlift6 (,,,,,) output output output output output output

instance (Outputtable a, Outputtable b, Outputtable c, Outputtable d, Outputtable e, Outputtable f, Outputtable g) => Outputtable (a, b, c, d, e, f, g) where
  output = mlift7 (,,,,,,) output output output output output output output

instance (Outputtable a, Outputtable b, Outputtable c, Outputtable d, Outputtable e, Outputtable f, Outputtable g, Outputtable h) => Outputtable (a, b, c, d, e, f, g, h) where
  output = mlift8 (,,,,,,,) output output output output output output output output

-- | Add a user specified axiom to the generated SMT-Lib file. Note that the input is a
-- mere string; we perform no checking on the input that it's well-formed or is sensical.
-- A separate formalization of SMT-Lib would be very useful here.
addAxiom :: String -> [String] -> Symbolic ()
addAxiom nm ax = do
        st <- ask
        liftIO $ modifyIORef (raxioms st) ((nm, ax) :)

-- | Run a symbolic computation and return a 'Result'
runSymbolic :: Symbolic a -> IO Result
runSymbolic c = do (_, r) <- runSymbolic' c
                   return r

-- | Run a symbolic computation, and return a extra value paired up with the 'Result'
runSymbolic' :: Symbolic a -> IO (a, Result)
runSymbolic' (Symbolic c) = do
   ctr     <- newIORef (-2) -- start from -2; False and True will always occupy the first two elements
   pgm     <- newIORef S.empty
   emap    <- newIORef Map.empty
   cmap    <- newIORef Map.empty
   inps    <- newIORef []
   outs    <- newIORef []
   tables  <- newIORef Map.empty
   arrays  <- newIORef IMap.empty
   uis     <- newIORef Map.empty
   axioms  <- newIORef []
   swCache <- newIORef IMap.empty
   aiCache <- newIORef IMap.empty
   let st = State { rctr      = ctr
                  , rinps     = inps
                  , routs     = outs
                  , rtblMap   = tables
                  , spgm      = pgm
                  , rconstMap = cmap
                  , rArrayMap = arrays
                  , rexprMap  = emap
                  , rUIMap    = uis
                  , raxioms   = axioms
                  , rSWCache  = swCache
                  , rAICache  = aiCache
                  }
   _ <- newConst st (mkConstCW (False,1) (0::Integer)) -- s(-2) == falseSW
   _ <- newConst st (mkConstCW (False,1) (1::Integer)) -- s(-1) == trueSW
   r <- runReaderT c st
   rpgm  <- readIORef pgm
   inpsR <- readIORef inps
   outsR <- readIORef outs
   let swap (a, b) = (b, a)
       cmp  (a, _) (b, _) = a `compare` b
   cnsts <- (sortBy cmp . map swap . Map.toList) `fmap` readIORef (rconstMap st)
   tbls  <- (sortBy (\((x, _, _), _) ((y, _, _), _) -> x `compare` y) . map swap . Map.toList) `fmap` readIORef tables
   arrs  <- IMap.toAscList `fmap` readIORef arrays
   unint <- Map.toList `fmap` readIORef uis
   axs   <- reverse `fmap` readIORef axioms
   return $ (r, Result (reverse inpsR) cnsts tbls arrs unint axs rpgm (reverse outsR))

-------------------------------------------------------------------------------
-- * Symbolic Words
-------------------------------------------------------------------------------
-- | A 'SymWord' is a potential symbolic bitvector that can be created instances of
-- to be fed to a symbolic program. Note that these methods are typically not needed
-- in casual uses with 'prove', 'sat', 'allSat' etc, as default instances automatically
-- provide the necessary bits.
--
-- Minimal complete definiton: free, free_, literal, fromCW
class (Bounded a, Ord a) => SymWord a where
  -- | Create a user named input
  free       :: String -> Symbolic (SBV a)
  -- | Create an automatically named input
  free_      :: Symbolic (SBV a)
  -- | Get a bunch of new words
  mkFreeVars   :: Int -> Symbolic [SBV a]
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
  -- | Does it concretely satisfy the given predicate?
  isConcretely :: SBV a -> (a -> Bool) -> Bool

  -- minimal complete definiton: free, free_, literal, fromCW
  mkFreeVars n = mapM (const free_) [1 .. n]
  unliteral (SBV _ (Left c))  = Just $ fromCW c
  unliteral _                 = Nothing
  isConcrete (SBV _ (Left _)) = True
  isConcrete _                = False
  isSymbolic = not . isConcrete
  isConcretely s p
    | Just i <- unliteral s = p i
    | True                  = False

---------------------------------------------------------------------------------
-- * Symbolic Arrays
---------------------------------------------------------------------------------

-- | Flat arrays of symbolic values
-- An @array a b@ is an array indexed by the type @'SBV' a@, with elements of type @'SBV' b@
-- If an initial value is not provided in 'newArray_' and 'newArray' methods, then the elements
-- are left unspecified, i.e., the solver is free to choose any value. This is the right thing
-- to do if arrays are used as inputs to functions to be verified, typically. 
--
-- While it's certainly possible for user to create instances of 'SymArray', the
-- 'SArray' and 'SFunArray' instances already provided should cover most use cases
-- in practice. (There are some differences between these models, however, see the corresponding
-- declaration.)
--
--
-- Minimal complete definition: All methods are required, no defaults.
class SymArray array where
  -- | Create a new array, with an optional initial value
  newArray_      :: (HasSignAndSize a, HasSignAndSize b) => Maybe (SBV b) -> Symbolic (array a b)
  -- | Create a named new array, with an optional initial value
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
--
--   * Maps directly to SMT-lib arrays
--
--   * Reading from an unintialized value is OK and yields an uninterpreted result
--
--   * Can check for equality of these arrays
--
--   * Cannot quick-check theorems using @SArray@ values
--
--   * Typically slower as it heavily relies on SMT-solving for the array theory
--
data SArray a b = SArray ((Bool, Size), (Bool, Size)) (Cached ArrayIndex)
type ArrayIndex = Int

instance (HasSignAndSize a, HasSignAndSize b) => Show (SArray a b) where
  show (SArray{}) = "SArray<" ++ showType (undefined :: a) ++ ":" ++ showType (undefined :: b) ++ ">"

instance SymArray SArray where
  newArray_  = declNewSArray (\t -> "array_" ++ show t)
  newArray n = declNewSArray (const n)
  readArray (SArray (_, bsgnsz) f) a = SBV bsgnsz $ Right $ cache r
     where r st = do arr <- uncacheAI f st
                     i   <- sbvToSW st a
                     newExpr st bsgnsz (SBVApp (ArrRead arr) [i])
  resetArray (SArray ainfo f) b = SArray ainfo $ cache g
     where g st = do amap <- readIORef (rArrayMap st)
                     val <- sbvToSW st b
                     i <- uncacheAI f st
                     let j = IMap.size amap
                     j `seq` modifyIORef (rArrayMap st) (IMap.insert j ("array_" ++ show j, ainfo, ArrayReset i val))
                     return j
  writeArray (SArray ainfo f) a b = SArray ainfo $ cache g
     where g st = do arr  <- uncacheAI f st
                     addr <- sbvToSW st a
                     val  <- sbvToSW st b
                     amap <- readIORef (rArrayMap st)
                     let j = IMap.size amap
                     j `seq` modifyIORef (rArrayMap st) (IMap.insert j ("array_" ++ show j, ainfo, ArrayMutate arr addr val))
                     return j
  mergeArrays t (SArray ainfo a) (SArray _ b) = SArray ainfo $ cache h
    where h st = do ai <- uncacheAI a st
                    bi <- uncacheAI b st
                    ts <- sbvToSW st t
                    amap <- readIORef (rArrayMap st)
                    let k = IMap.size amap
                    k `seq` modifyIORef (rArrayMap st) (IMap.insert k ("array_" ++ show k, ainfo, ArrayMerge ts ai bi))
                    return k

declNewSArray :: forall a b. (HasSignAndSize a, HasSignAndSize b) => (Int -> String) -> Maybe (SBV b) -> Symbolic (SArray a b)
declNewSArray mkNm mbInit = do
   let asgnsz = (hasSign (undefined :: a), sizeOf (undefined :: a))
       bsgnsz = (hasSign (undefined :: b), sizeOf (undefined :: b))
   st <- ask
   amap <- liftIO $ readIORef $ rArrayMap st
   let i = IMap.size amap
       nm = mkNm i
   actx <- liftIO $ case mbInit of
                     Nothing   -> return $ ArrayFree Nothing
                     Just ival -> sbvToSW st ival >>= \sw -> return $ ArrayFree (Just sw)
   liftIO $ modifyIORef (rArrayMap st) (IMap.insert i (nm, (asgnsz, bsgnsz), actx))
   return $ SArray (asgnsz, bsgnsz) $ cache $ const $ return i

-- | Arrays implemented internally as functions
--
--    * Internally handled by the library and not mapped to SMT-Lib
--
--    * Reading an uninitialized value is considered an error (will throw exception)
--
--    * Cannot check for equality (internally represented as functions)
--
--    * Can quick-check
--
--    * Typically faster as it gets compiled away during translation
--
data SFunArray a b = SFunArray (SBV a -> SBV b)

instance (HasSignAndSize a, HasSignAndSize b) => Show (SFunArray a b) where
  show (SFunArray _) = "SFunArray<" ++ showType (undefined :: a) ++ ":" ++ showType (undefined :: b) ++ ">"

-- | Lift a function to an array. Useful for creating arrays in a pure context. (Otherwise use `newArray`.)
mkSFunArray :: (SBV a -> SBV b) -> SFunArray a b
mkSFunArray = SFunArray

---------------------------------------------------------------------------------
-- * Cached values
---------------------------------------------------------------------------------

-- We implement a peculiar caching mechanism, applicable to the use case in
-- implementation of SBV's.  Whenever we do a state based computation, we do
-- not want to keep on evaluating it in the then-current state. That will
-- produce essentially a semantically equivalent value. Thus, we want to run
-- it only once, and reuse that result, capturing the sharing at the Haskell
-- level. This is similar to the "type-safe observable sharing" work, but also
-- takes into the account of how symbolic simulation executes.
--
-- Note that this is *not* a general memo utility!

newtype Cached a = Cached (State -> IO a)

cache :: (State -> IO a) -> Cached a
cache = Cached

uncache :: Cached SW -> State -> IO SW
uncache = uncacheGen rSWCache

uncacheAI :: Cached ArrayIndex -> State -> IO ArrayIndex
uncacheAI = uncacheGen rAICache

uncacheGen :: (State -> IORef (Cache a)) -> Cached a -> State -> IO a
uncacheGen getCache (Cached f) st = do
        let rCache = getCache st
        stored <- readIORef rCache
        sn <- f `seq` makeStableName f
        let h = hashStableName sn
        case maybe Nothing (sn `lookup`) (h `IMap.lookup` stored) of
          Just r  -> return r
          Nothing -> do r <- f st
                        r `seq` modifyIORef rCache (IMap.insertWith (++) h [(sn, r)])
                        return r

-- Technicalities..
instance NFData CW where
  rnf (CW x y z) = x `seq` y `seq` z `seq` ()

instance NFData Result where
  rnf (Result inps consts tbls arrs uis axs pgm outs)
        = rnf inps `seq` rnf consts `seq` rnf tbls `seq` rnf arrs `seq` rnf uis `seq` rnf axs `seq` rnf pgm `seq` rnf outs

instance NFData ArrayContext
instance NFData Pgm
instance NFData SW
instance NFData SBVType
instance NFData UnintKind
instance NFData a => NFData (Cached a) where
  rnf (Cached f) = f `seq` ()
instance NFData a => NFData (SBV a) where
  rnf (SBV x y) = rnf x `seq` rnf y `seq` ()

-- Quickcheck interface on symbolic-booleans..
instance Testable SBool where
  property (SBV _ (Left b)) = property (cwToBool b)
  property s                = error $ "Cannot quick-check in the presence of uninterpreted constants! (" ++ show s ++ ")"
