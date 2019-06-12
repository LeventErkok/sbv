module Main(main) where

import System.Environment

travisFile, appveyorFile :: FilePath
travisFile   = "../.travis.yml"
appveyorFile = "../.appveyor.yml"

-- The version of z3 we test with
z3Version :: String
z3Version = "4.8.6"

ghcLatest :: String
ghcLatest = "8.6.5"

windowsGHCVersion :: String
windowsGHCVersion = ghcLatest

main :: IO ()
main = do as <- getArgs
          case as of
            ["travis"]   -> do writeFile travisFile $ unlines travis
                               putStrLn $ "Generated: " ++ travisFile
            ["appveyor"] -> do writeFile appveyorFile $ unlines appveyor
                               putStrLn $ "Generated: " ++ appveyorFile
            _            -> error $ "Call with either travis or appveyor"

header :: [String]
header = [ "#####################################################"
         , "# Automatically generated CI build file. Do not edit!"
         , "#####################################################"
         ]

footer :: [String]
footer = [ "#####################################################"
         , "# End of automatically generated CI build file."
         , "#####################################################"
         ]

travis :: [String]
travis = header ++ body ++ footer
 where body = [ ""
              , "Wish I knew how to generate travis"
              , ""
              ]

appveyor :: [String]
appveyor = header ++ body ++ footer
 where -- put tweaks here
       heavyTestPercentage :: Int
       heavyTestPercentage = 0

       z3Name :: String
       z3Name = "z3-" ++ z3Version ++ "-x64-win.zip"

       z3Path :: String
       z3Path = "https://github.com/Z3Prover/z3/releases/download/Nightly/z3-" ++ z3Version ++ "-x64-win.zip"

       -- No changes should be necessary below
       body = [ ""
              , "build: off"
              , ""
              , "environment:"
              , "    SBV_TEST_ENVIRONMENT: win"
              , "    SBV_HEAVYTEST_PERCENTAGE: " ++ show heavyTestPercentage
              , "    TASTY_HIDE_SUCCESSES: True"
              , ""
              , "before_build:"
              , "- curl -fsSL " ++ z3Path ++ " -o " ++ z3Name
              , "- 7z e " ++ z3Name ++ " -oc:\\projects\\sbv\\z3_downloaded -r -y"
              , "- choco install -y cabal"
              , "- choco install -y ghc --version " ++ windowsGHCVersion
              , "- refreshenv"
              , "- set PATH=C:\\projects\\sbv\\z3_downloaded;%PATH%"
              , "- ghc --version"
              , "- z3 --version"
              , ""
              , "skip_tags: true"
              , ""
              , "build_script:"
              , "- cabal update"
              , "- cabal install alex"
              , "- cabal install happy"
              , "- cabal install --only-dependencies --enable-tests --enable-benchmarks"
              , "- cabal build"
              , "- cabal test SBVTest"
              , "- cabal test SBVDocTest"
              , "- cabal test SBVHLint"
              , "- cabal check"
              , "- cabal sdist"
              ]
