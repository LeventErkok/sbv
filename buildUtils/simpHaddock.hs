{-# OPTIONS_GHC -Wall -Werror #-}

module Main where

import Data.Char
import Data.List
import System.Exit
import qualified Control.Exception as C

main :: IO ()
main = go False

nextLine :: Bool -> IO String
nextLine failed = do mbL <- (Just <$> getLine) `C.catch` (\(_ :: C.SomeException) -> return Nothing)
                     case mbL of
                       Nothing -> if failed then do putStrLn "*** There were haddock issues"
                                                    exitFailure
                                            else exitSuccess
                       Just l  -> pure l

-- If there's a percentage, it better be 100%!
bad :: String -> Bool
bad ln
  | '%' `notElem` ln
  = False
  | True
  = case words ln of
     "100%" : _ -> False
     _          -> True

trigger :: String -> Bool
trigger ln = "Warning: " `isPrefixOf` ln && ": could not find link destinations for:" `isInfixOf` ln

go :: Bool -> IO ()
go failed = do
    ln <- nextLine failed
    case () of
      () | trigger ln -> processWarns failed (Just ln)
      () | True       -> do putStrLn ln
                            go (failed || bad ln)

processWarns :: Bool -> Maybe String -> IO ()
processWarns failed mbTopLine = do
   ln <- nextLine failed
   case () of
     () | trigger  ln -> processWarns failed (Just ln)
        | ignore   ln -> processWarns failed mbTopLine
        | finalize ln -> go failed
        | True        -> do maybe (pure ()) putStrLn mbTopLine
                            putStrLn ln
                            processWarns True Nothing

finalize :: String -> Bool
finalize ln = "Documentation created:" `isInfixOf` ln

ignore :: String -> Bool
ignore s = haddockBug s || sbvIgnore s

-- These are haddock bugs..
haddockBug :: String -> Bool
haddockBug input
   | not ("-" `isPrefixOf` dropWhile isSpace input)
   = False
   | True
   = bug1 || bug2 || bug3
  where
   -- See: https://github.com/haskell/haddock/issues/1071 amongst others
   bug1 = ".R:"    `isInfixOf` input
   bug2 = ".D:R:"  `isInfixOf` input
   bug3 = ".Rep_"  `isInfixOf` input

-- These are things that SBV doesn't export so Haddock can't really link to
sbvIgnore :: String -> Bool
sbvIgnore input = any (`isPrefixOf` s) (map fmt patterns)
  where s     = dropWhile isSpace input
        fmt p = "- Data.SBV." ++ p

        patterns = [ "Core.Kind.BVZeroWidth"
                   , "Core.Kind.constructUKind"
                   , "Core.Kind.InvalidFloat"
                   , "Core.Symbolic.SMTEngine"
                   , "Core.Symbolic.UIName"
                   , "Core.Data.skolem"
                   , "Core.Data.GEqSymbolic"
                   , "Core.Model.UIKind"
                   , "Core.Model.GMergeable"
                   , "Core.Model.QSaturate"
                   , "Core.Symbolic.SMTDef"
                   , "Core.Symbolic.CnstMap"
                   , "Core.Symbolic.ProgInfo"
                   , "Core.Symbolic.ResultInp"
                   , "Core.Symbolic.Name"
                   , "Core.Symbolic.SetOp"
                   , "Core.Symbolic.SMTLambda"
                   , "Core.Symbolic.NROp"
                   , "Core.Symbolic.SpecialRelOp"
                   , "Core.Symbolic.SBVContext"
                   , "Core.Model.minimize"
                   , "Core.Model.maximize"
                   , "Client.BaseIO.ToSizedBV"
                   , "Client.BaseIO.FromSizedBV"
                   , "Control.Utils.SMTFunction"
                   , "Control.Query.Assignment"
                   , "List.SMap"
                   , "List.SFoldL"
                   , "List.SFoldR"
                   , "List.SZipWith"
                   , "TP.TP.ChainStep"
                   , "TP.TP.ChainsTo"
                   , "TP.TP.HintsTo"
                   , "TP.TP.Hinted"
                   , "TP.TP.TPProof"
                   , "TP.TP.ProofHint"
                   , "TP.TP.ProofStep"
                   , "TP.TP.Trivial"
                   , "TP.TP.Helper"
                   , "TP.TP.Instantiatable"
                   , "TP.TP.Inductive"
                   , "TP.TP.SInductive"
                   , "TP.TP.CalcLemma"
                   , "TP.TP.Contradiction"
                   , "Tools.STree.STreeInternal"
                   , "Tuple.Tuple"
                   , "Tuple.HasField"
                   , "Utils.SExpr.SExpr"
                   ]
