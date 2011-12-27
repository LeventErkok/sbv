-----------------------------------------------------------------------------
-- |
-- Module      :  Data.SBV.BitVectors.GenTest
-- Copyright   :  (c) Levent Erkok
-- License     :  BSD3
-- Maintainer  :  erkokl@gmail.com
-- Stability   :  experimental
-- Portability :  portable
--
-- Test generation from symbolic programs
-----------------------------------------------------------------------------

module Data.SBV.BitVectors.GenTest (genTest) where

import Data.Maybe (fromMaybe)

import Data.SBV.BitVectors.Data

-- | Generate a set of concrete test values from a symbolic program. The output
-- can be rendered as test vectors in different languages as necessary. Use the
-- function 'output' call to indicate what fields should be in the test result.
-- (Also see 'constrain' and 'pConstrain' for filtering acceptable test values.)
genTest :: Int -> Symbolic () -> IO [([CW], [CW])]
genTest n m = gen 0 []
  where gen i sofar
         | i == n = return (reverse sofar)
         | True   = do mbT <- tc
                       case mbT of
                        Nothing -> gen i     sofar
                        Just t  -> gen (i+1) (t:sofar)
        tc = do (_, Result _ tvals _ _ cs _ _ _ _ _ cstrs os) <- runSymbolic' Concrete m
                let cval = fromMaybe (error "Cannot generate tests in the presence of uninterpeted constants!") . (`lookup` cs)
                    cond = all (cwToBool . cval) cstrs
                    io   = (map snd tvals, map cval os)
                if cond
                   then return $ Just io
                   else return Nothing
