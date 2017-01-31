module Main (main) where

import Data.SBV
import Data.List
import Control.Monad
import System.Exit

-- Known solvers with bugs! Should really be empty!
badSolvers :: [SMTConfig]
badSolvers = []

main :: IO ()
main = do ss  <- filter (not . skip) `fmap` sbvAvailableSolvers
          let req = filter (not . skip) [abc, boolector, cvc4, mathSAT, yices, z3]
              need  = sort $ map show req
              cur   = sort $ map show ss
              extra = filter (`notElem` need) cur
              miss  = filter (`notElem` cur ) need
          when (cur /= need) $ do
                putStrLn $ unlines [ "Bad solver list: " ++ show ss
                                   , "          Extra: " ++ show extra
                                   , "        Missing: " ++ show miss
                                   ]
                exitFailure
          mapM_ test ss
          putStrLn $ "Tested OK basic connection to: " ++ intercalate ", "  need
          unless (null badSolvers) $ putStrLn $ "*** NB: The following solvers are ignored: " ++ intercalate ", " (map show badSolvers)
          exitSuccess
  where skip :: SMTConfig -> Bool
        skip s = show s `elem` map show badSolvers


test :: SMTConfig -> IO ()
test s = do check  "t0" t0 (== Just False)
            check  "t1" t1 (== Just True)
            models "t2" t2 (== ([2,62,66,126,130,190,194,254]::[Word8]))
            models "t3" t3 (== ([]::[Word8]))
            models "t4" t4 (== [4::Word8])
  where check m p f = thm p >>= decide m f
        decide m f r
          | f r  = return ()
          | True = do putStrLn $ m ++ "[" ++ show s ++ "] FAIL. Got: " ++ show r
                      exitFailure
        thm = isTheoremWith s Nothing
        models m p f = (extractModels `fmap` allSat p) >>= decide m f . sort
        t0 x = x   .== x+(1::SWord8)
        t1 x = x*2 .== x+(x::SWord8)
        t2 x = x*x .== (4::SWord8)
        t3 x = x*x .== (3::SWord8)
        t4 x = x*3 .== (12::SWord8)
