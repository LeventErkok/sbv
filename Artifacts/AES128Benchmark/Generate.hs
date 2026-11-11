import Control.Monad (void)
import Data.SBV.Tools.CodeGen (compileToCLib, cgOverwriteFiles, cgSetDriverValues)
import Documentation.SBV.Examples.Crypto.AES (aesLibComponents)

main :: IO ()
main = void $ compileToCLib (Just "Artifacts/AES128Benchmark/generated") "aes128Lib"
  [(name, cgSetDriverValues values >> action >> cgOverwriteFiles True)
  | (name, values, action) <- aesLibComponents 128]
