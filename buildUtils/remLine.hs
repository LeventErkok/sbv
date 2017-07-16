import System.Environment
import Data.List

main :: IO ()
main = do as <- getArgs
          case as of
           [p, f] -> do xs <- readFile f
                        let ys = walk p xs
                        if xs == ys then return ()
                                    else do writeFile (f ++ ".backup") xs
                                            writeFile f ys
           _      -> error "call with line header and one file name"

walk :: String -> String -> String
walk p = go
 where go [] = []
       go res@(h:t)
        | ('\n':p) `isPrefixOf` res = drop (length p + 1) res
        | True                      = h : go t
