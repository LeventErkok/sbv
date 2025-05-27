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
{-# LANGUAGE TypeApplications    #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module Data.SBV.Utils.Lib ( mlift2, mlift3, mlift4, mlift5, mlift6, mlift7, mlift8
                          , joinArgs, splitArgs
                          , stringToQFS, qfsToString
                          , isKString
                          , checkObservableName
                          , needsBars, isEnclosedInBars
                          , noSurrounding, unQuote, unBar, nameSupply
                          , atProxy
                          ,   curry2,   curry3,   curry4,   curry5,   curry6,   curry7,   curry8,   curry9,   curry10,   curry11,   curry12
                          , uncurry2, uncurry3, uncurry4, uncurry5, uncurry6, uncurry7, uncurry8, uncurry9, uncurry10, uncurry11, uncurry12
                          )
                          where

import Data.Char    (isSpace, chr, ord, isDigit, isAscii, isAlphaNum)
import Data.List    (isPrefixOf, isSuffixOf)
import Data.Dynamic (fromDynamic, toDyn, Typeable)
import Data.Maybe   (fromJust, isJust, isNothing)
import Data.Proxy

import Type.Reflection (typeRep)

import Numeric (readHex, showHex)

import Data.SBV.SMT.SMTLibNames (isReserved)

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

-- | Given an SMTLib string (i.e., one that works in the string theory), convert it to a Haskell equivalent
qfsToString :: String -> String
qfsToString = go
  where go "" = ""

        go ('\\':'u':'{':d4:d3:d2:d1:d0:'}' : rest) | [(v, "")] <- readHex [d4, d3, d2, d1, d0] = chr v : go rest
        go ('\\':'u':       d3:d2:d1:d0     : rest) | [(v, "")] <- readHex [    d3, d2, d1, d0] = chr v : go rest
        go ('\\':'u':'{':   d3:d2:d1:d0:'}' : rest) | [(v, "")] <- readHex [    d3, d2, d1, d0] = chr v : go rest
        go ('\\':'u':'{':      d2:d1:d0:'}' : rest) | [(v, "")] <- readHex [        d2, d1, d0] = chr v : go rest
        go ('\\':'u':'{':         d1:d0:'}' : rest) | [(v, "")] <- readHex [            d1, d0] = chr v : go rest
        go ('\\':'u':'{':            d0:'}' : rest) | [(v, "")] <- readHex [                d0] = chr v : go rest

        -- Otherwise, just proceed; hopefully we covered everything above
        go (c : rest) = c : go rest

-- | Given a Haskell string, convert it to SMTLib. if ord is 0x00020 to 0x0007E, then we print it as is
-- to cover the printable ASCII range.
stringToQFS :: String -> String
stringToQFS = concatMap cvt
  where cvt c
         | c == '"'                 = "\"\""
         | oc >= 0x20 && oc <= 0x7E = [c]
         | True                     = "\\u{" ++ showHex oc "" ++ "}"
         where oc = ord c

-- | Check if an observable name is good.
checkObservableName :: String -> Maybe String
checkObservableName lbl
  | null lbl
  = Just "SBV.observe: Bad empty name!"
  | isReserved lbl
  = Just $ "SBV.observe: The name chosen is reserved, please change it!: " ++ show lbl
  | "s" `isPrefixOf` lbl && all isDigit (drop 1 lbl)
  = Just $ "SBV.observe: Names of the form sXXX are internal to SBV, please use a different name: " ++ show lbl
  | True
  = Nothing

-- Remove one pair of surrounding 'c's, if present
noSurrounding :: Char -> String -> String
noSurrounding c (c':cs@(_:_)) | c == c' && c == last cs  = init cs
noSurrounding _ s                                        = s

-- Remove a pair of surrounding quotes
unQuote :: String -> String
unQuote = noSurrounding '"'

-- Remove a pair of surrounding bars
unBar :: String -> String
unBar = noSurrounding '|'

-- Is this string surrounded by bars? NB. There shouldn't be any other bars or backslash anywhere
isEnclosedInBars :: String -> Bool
isEnclosedInBars nm =  "|" `isPrefixOf` nm
                    && "|" `isSuffixOf` nm
                    && length nm > 2
                    && not (any (`elem` ("|\\" :: String)) (drop 1 (init nm)))

-- Does this name need bar in SMTLib2?
needsBars :: String -> Bool
needsBars ""        = error "Impossible happened: needsBars received an empty name!"
needsBars nm@(h:tl) = not (isEnclosedInBars nm || (isAscii h && all validChar tl))
 where  validChar x = isAscii x && (isAlphaNum x || x `elem` ("_" :: String))

-- | Converts a proxy to a readable result. This is useful when you want to write a polymorphic
-- proof, so that the name contains the instantiated version properly.
atProxy :: forall a. Typeable a => Proxy a -> String -> String
atProxy _ nm = nm ++ " @" ++ show (typeRep @a)

-- An infinite supply of names, starting with a given set
nameSupply :: [String] -> [String]
nameSupply preSupply = preSupply ++ map mkUnique extras
  where extras =  ["x", "y", "z"]                           -- x y z
               ++ [[c] | c <- ['a' .. 'w']]                 -- a b c ... w
               ++ ['x' : show i | i <- [(1::Int) ..]]       -- x1 x2 x3 ...

        -- make sure extras are different than preSupply. Note that extras
        -- themselves are unique, so we only have to check the preSupply
        mkUnique x | x `elem` preSupply = mkUnique $ x ++ "'"
                   | True               = x

-- Different arities of curry/uncurry
curry2 :: ((a, b) -> z) -> a -> b -> z
curry2 fn a b = fn (a, b)

curry3 :: ((a, b, c) -> z) -> a -> b -> c -> z
curry3 fn a b c = fn (a, b, c)

curry4 :: ((a, b, c, d) -> z) -> a -> b -> c -> d -> z
curry4 fn a b c d = fn (a, b, c, d)

curry5 :: ((a, b, c, d, e) -> z) -> a -> b -> c -> d -> e -> z
curry5 fn a b c d e = fn (a, b, c, d, e)

curry6 :: ((a, b, c, d, e, f) -> z) -> a -> b -> c -> d -> e -> f -> z
curry6 fn a b c d e f = fn (a, b, c, d, e, f)

curry7 :: ((a, b, c, d, e, f, g) -> z) -> a -> b -> c -> d -> e -> f -> g -> z
curry7 fn a b c d e f g = fn (a, b, c, d, e, f, g)

curry8 :: ((a, b, c, d, e, f, g, h) -> z) -> a -> b -> c -> d -> e -> f -> g -> h -> z
curry8 fn a b c d e f g h = fn (a, b, c, d, e, f, g, h)

curry9 :: ((a, b, c, d, e, f, g, h, i) -> z) -> a -> b -> c -> d -> e -> f -> g -> h -> i -> z
curry9 fn a b c d e f g h i = fn (a, b, c, d, e, f, g, h, i)

curry10 :: ((a, b, c, d, e, f, g, h, i, j) -> z) -> a -> b -> c -> d -> e -> f -> g -> h -> i -> j -> z
curry10 fn a b c d e f g h i j = fn (a, b, c, d, e, f, g, h, i, j)

curry11 :: ((a, b, c, d, e, f, g, h, i, j, k) -> z) -> a -> b -> c -> d -> e -> f -> g -> h -> i -> j -> k -> z
curry11 fn a b c d e f g h i j k = fn (a, b, c, d, e, f, g, h, i, j, k)

curry12 :: ((a, b, c, d, e, f, g, h, i, j, k, l) -> z) -> a -> b -> c -> d -> e -> f -> g -> h -> i -> j -> k -> l -> z
curry12 fn a b c d e f g h i j k l = fn (a, b, c, d, e, f, g, h, i, j, k, l)

uncurry2 :: (a -> b -> z) -> (a, b) -> z
uncurry2 fn (a, b) = fn a b

uncurry3 :: (a -> b -> c -> z) -> (a, b, c) -> z
uncurry3 fn (a, b, c) = fn a b c

uncurry4 :: (a -> b -> c -> d -> z) -> (a, b, c, d) -> z
uncurry4 fn (a, b, c, d) = fn a b c d

uncurry5 :: (a -> b -> c -> d -> e -> z) -> (a, b, c, d, e) -> z
uncurry5 fn (a, b, c, d, e) = fn a b c d e

uncurry6 :: (a -> b -> c -> d -> e -> f -> z) -> (a, b, c, d, e, f) -> z
uncurry6 fn (a, b, c, d, e, f) = fn a b c d e f

uncurry7 :: (a -> b -> c -> d -> e -> f -> g -> z) -> (a, b, c, d, e, f, g) -> z
uncurry7 fn (a, b, c, d, e, f, g) = fn a b c d e f g

uncurry8 :: (a -> b -> c -> d -> e -> f -> g -> h -> z) -> (a, b, c, d, e, f, g, h) -> z
uncurry8 fn (a, b, c, d, e, f, g, h) = fn a b c d e f g h

uncurry9 :: (a -> b -> c -> d -> e -> f -> g -> h -> i -> z) -> (a, b, c, d, e, f, g, h, i) -> z
uncurry9 fn (a, b, c, d, e, f, g, h, i) = fn a b c d e f g h i

uncurry10 :: (a -> b -> c -> d -> e -> f -> g -> h -> i -> j -> z) -> (a, b, c, d, e, f, g, h, i, j) -> z
uncurry10 fn (a, b, c, d, e, f, g, h, i, j) = fn a b c d e f g h i j

uncurry11 :: (a -> b -> c -> d -> e -> f -> g -> h -> i -> j -> k -> z) -> (a, b, c, d, e, f, g, h, i, j, k) -> z
uncurry11 fn (a, b, c, d, e, f, g, h, i, j, k) = fn a b c d e f g h i j k

uncurry12 :: (a -> b -> c -> d -> e -> f -> g -> h -> i -> j -> k -> l -> z) -> (a, b, c, d, e, f, g, h, i, j, k, l) -> z
uncurry12 fn (a, b, c, d, e, f, g, h, i, j, k, l) = fn a b c d e f g h i j k l
