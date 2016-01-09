module Main (main) where

import Data.SBV
import Data.List
import Control.Monad
import System.Exit

main :: IO ()
main = do ss <- sbvAvailableSolvers
          let need  = sort ["ABC","Boolector","CVC4","MathSAT","Yices","Z3"]
              cur   = sort (map show ss)
              extra = filter (\e -> e `notElem` need) cur
              miss  = filter (\e -> e `notElem` cur ) need
          when (cur /= need) $ do
                putStrLn $ unlines [ "Bad solver list: " ++ show ss
                                   , "          Extra: " ++ show extra
                                   , "        Missing: " ++ show miss
                                   ]
                exitFailure
          mapM_ test ss
          putStrLn $ "Tested OK basic connection to: " ++ intercalate ", "  need
          exitSuccess

test :: SMTConfig -> IO ()
test s = do check  "t0" t0 (== Just False)
            check  "t1" t1 (== Just True)
            models "t2" t2 (== ([2,62,66,126,130,190,194,254]::[Word8]))
            models "t3" t3 (== ([]::[Word8]))
            models "t4" t4 (== [4::Word8])
  where check m p f = thm p >>= decide m f
        decide m f r
          | f r  = return ()
          | True = do putStrLn $ m ++ " FAIL. Got: " ++ show r
                      exitFailure
        thm = isTheoremWith s Nothing
        models m p f = (extractModels `fmap` allSat p) >>= decide m f . sort
        t0 x = x   .== x+(1::SWord8)
        t1 x = x*2 .== x+(x::SWord8)
        t2 x = x*x .== (4::SWord8)
        t3 x = x*x .== (3::SWord8)
        t4 x = x*3 .== (12::SWord8)
