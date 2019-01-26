-----------------------------------------------------------------------------
-- |
-- Module    : Data.SBV.Utils.Lib
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- Misc helpers
-----------------------------------------------------------------------------

{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Data.SBV.Utils.Lib ( mlift2, mlift3, mlift4, mlift5, mlift6, mlift7, mlift8
                          , joinArgs, splitArgs
                          , stringToQFS, qfsToString
                          , isKString
                          )
                          where

import Data.Char    (isSpace, chr, ord)
import Data.Dynamic (fromDynamic, toDyn, Typeable)
import Data.Maybe   (fromJust, isJust, isNothing)

import Numeric (readHex, readOct, showHex)

-- | We have a nasty issue with the usual String/List confusion in Haskell. However, we can
-- do a simple dynamic trick to determine where we are. The ice is thin here, but it seems to work.
isKString :: forall a. Typeable a => a -> Bool
isKString _ = isJust (fromDynamic (toDyn (undefined :: a)) :: Maybe String)

-- | Monadic lift over 2-tuples
mlift2 :: Monad m => (a' -> b' -> r) -> (a -> m a') -> (b -> m b') -> (a, b) -> m r
mlift2 k f g (a, b) = f a >>= \a' -> g b >>= \b' -> return $ k a' b'

-- | Monadic lift over 3-tuples
mlift3 :: Monad m => (a' -> b' -> c' -> r) -> (a -> m a') -> (b -> m b') -> (c -> m c') -> (a, b, c) -> m r
mlift3 k f g h (a, b, c) = f a >>= \a' -> g b >>= \b' -> h c >>= \c' -> return $ k a' b' c'

-- | Monadic lift over 4-tuples
mlift4 :: Monad m => (a' -> b' -> c' -> d' -> r) -> (a -> m a') -> (b -> m b') -> (c -> m c') -> (d -> m d') -> (a, b, c, d) -> m r
mlift4 k f g h i (a, b, c, d) = f a >>= \a' -> g b >>= \b' -> h c >>= \c' -> i d >>= \d' -> return $ k a' b' c' d'

-- | Monadic lift over 5-tuples
mlift5 :: Monad m => (a' -> b' -> c' -> d' -> e' -> r) -> (a -> m a') -> (b -> m b') -> (c -> m c') -> (d -> m d') -> (e -> m e') -> (a, b, c, d, e) -> m r
mlift5 k f g h i j (a, b, c, d, e) = f a >>= \a' -> g b >>= \b' -> h c >>= \c' -> i d >>= \d' -> j e >>= \e' -> return $ k a' b' c' d' e'

-- | Monadic lift over 6-tuples
mlift6 :: Monad m => (a' -> b' -> c' -> d' -> e' -> f' -> r) -> (a -> m a') -> (b -> m b') -> (c -> m c') -> (d -> m d') -> (e -> m e') -> (f -> m f') -> (a, b, c, d, e, f) -> m r
mlift6 k f g h i j l (a, b, c, d, e, y) = f a >>= \a' -> g b >>= \b' -> h c >>= \c' -> i d >>= \d' -> j e >>= \e' -> l y >>= \y' -> return $ k a' b' c' d' e' y'

-- | Monadic lift over 7-tuples
mlift7 :: Monad m => (a' -> b' -> c' -> d' -> e' -> f' -> g' -> r) -> (a -> m a') -> (b -> m b') -> (c -> m c') -> (d -> m d') -> (e -> m e') -> (f -> m f') -> (g -> m g') -> (a, b, c, d, e, f, g) -> m r
mlift7 k f g h i j l m (a, b, c, d, e, y, z) = f a >>= \a' -> g b >>= \b' -> h c >>= \c' -> i d >>= \d' -> j e >>= \e' -> l y >>= \y' -> m z >>= \z' -> return $ k a' b' c' d' e' y' z'

-- | Monadic lift over 8-tuples
mlift8 :: Monad m => (a' -> b' -> c' -> d' -> e' -> f' -> g' -> h' -> r) -> (a -> m a') -> (b -> m b') -> (c -> m c') -> (d -> m d') -> (e -> m e') -> (f -> m f') -> (g -> m g') -> (h -> m h') -> (a, b, c, d, e, f, g, h) -> m r
mlift8 k f g h i j l m n (a, b, c, d, e, y, z, w) = f a >>= \a' -> g b >>= \b' -> h c >>= \c' -> i d >>= \d' -> j e >>= \e' -> l y >>= \y' -> m z >>= \z' -> n w >>= \w' -> return $ k a' b' c' d' e' y' z' w'

-- Command line argument parsing code courtesy of Neil Mitchell's cmdargs package: see
-- <http://github.com/ndmitchell/cmdargs/blob/master/System/Console/CmdArgs/Explicit/SplitJoin.hs>

-- | Given a sequence of arguments, join them together in a manner that could be used on
--   the command line, giving preference to the Windows @cmd@ shell quoting conventions.
--
--   For an alternative version, intended for actual running the result in a shell, see "System.Process.showCommandForUser"
joinArgs :: [String] -> String
joinArgs = unwords . map f
    where f x = q ++ g x ++ q
            where hasSpace = any isSpace x
                  q = ['\"' | hasSpace || null x]
                  g ('\\':'\"':xs)            = '\\':'\\':'\\':'\"': g xs
                  g "\\"           | hasSpace = "\\\\"
                  g ('\"':xs)                 = '\\':'\"': g xs
                  g (x':xs)                   = x' : g xs
                  g []                        = []

data State = Init -- either I just started, or just emitted something
           | Norm -- I'm seeing characters
           | Quot -- I've seen a quote

-- | Given a string, split into the available arguments. The inverse of 'joinArgs'.
-- Courtesy of the cmdargs package.
splitArgs :: String -> [String]
splitArgs = join . f Init
    where -- Nothing is start a new string
          -- Just x is accumulate onto the existing string
          join :: [Maybe Char] -> [String]
          join [] = []
          join xs = map fromJust a : join (drop 1 b)
            where (a,b) = break isNothing xs

          f Init (x:xs) | isSpace x = f Init xs
          f Init "\"\""             = [Nothing]
          f Init "\""               = [Nothing]
          f Init xs                 = f Norm xs
          f m ('\"':'\"':'\"':xs)   = Just '\"' : f m xs
          f m ('\\':'\"':xs)        = Just '\"' : f m xs
          f m ('\\':'\\':'\"':xs)   = Just '\\' : f m ('\"':xs)
          f Norm ('\"':xs)          = f Quot xs
          f Quot ('\"':'\"':xs)     = Just '\"' : f Norm xs
          f Quot ('\"':xs)          = f Norm xs
          f Norm (x:xs) | isSpace x = Nothing : f Init xs
          f m (x:xs)                = Just x : f m xs
          f _ []                    = []

-- | Given a QF_S string (i.e., one that works in the string theory), convert it to a Haskell equivalent
qfsToString :: String -> String
qfsToString = go
  where go ""                                                          = ""
        go ('\\':'n'       : rest)                                     = chr 10 : go rest
        go ('\\':'\\'       : rest)                                    = '\\'   : go rest
        go ('\\':'v'       : rest)                                     = chr 11 : go rest
        go ('\\':'f'       : rest)                                     = chr 12 : go rest
        go ('\\':'r'       : rest)                                     = chr 13 : go rest
        go ('\\':'x':c1:c2 : rest) | [(v, "")] <- readHex [c1, c2]     = chr  v : go rest
        go ('\\':c1:c2:c3  : rest) | [(v, "")] <- readOct [c1, c2, c3] = chr  v : go rest
        go (c              : rest)                                     = c      : go rest

-- | Given a Haskell, convert it to one that's understood by the QF_S logic
-- TODO: This function will require mods with the new String logic; as escapes
-- will completely be different!
stringToQFS :: String -> String
stringToQFS = concatMap cvt
  where -- strings are almost just show, but escapes are different. Sigh
        cvt c
         | 0 <= o && o < 32
         = escapeTable !! o
         | c == '\\'
         = "\\\\"
         | c == '"'
         = "\"\""
         | o >= 128 && o < 256
         = "\\x" ++ showHex (ord c) ""
         | o > 256
         = error $ "Data.SBV: stringToQFS: Haskell character: " ++ show c ++ " is not representable in QF_S"
         | True
         = [c]
         where o = ord c

        -- | First 32 values are coded in a custom way by Z3:
        escapeTable :: [String]
        escapeTable = [ "\\x00", "\\x01", "\\x02", "\\x03", "\\x04", "\\x05", "\\x06", "\\x07", "\\x08", "\\x09", "\\n",   "\\v",   "\\f",   "\\r",   "\\x0E", "\\x0F"
                      , "\\x10", "\\x11", "\\x12", "\\x13", "\\x14", "\\x15", "\\x16", "\\x17", "\\x18", "\\x19", "\\x1A", "\\x1B", "\\x1C", "\\x1D", "\\x1E", "\\x1F"
                      ]
