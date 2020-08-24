-- We test with:
--     Z3 : Nightly release only
--     GHC:
--       - OSX:   Latest release
--       - Win:   Latest release
--       - Linux: Latest release
--                Previous release

{-# LANGUAGE NamedFieldPuns #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module Main(main) where

import System.Environment

---------------------------------------------------------------------------------
-- Modify the following section as new releases are made for these.
---------------------------------------------------------------------------------
-- Get this from latest z3 setting on github
z3Version :: String
z3Version = "4.8.9"

z3WindowsName, z3WindowsPath :: String
z3WindowsName = "z3-" ++ z3Version ++ "-x64-win.zip"
z3WindowsPath = "https://github.com/Z3Prover/z3/releases/download/Nightly/" ++ z3WindowsName

z3LinuxName, z3LinuxPath :: String
z3LinuxName = "z3-" ++ z3Version ++ "-x64-ubuntu-16.04.zip"
z3LinuxPath = "https://github.com/Z3Prover/z3/releases/download/Nightly/" ++ z3LinuxName

z3OSXName, z3OSXPath :: String
z3OSXName = "z3-" ++ z3Version ++ "-x64-osx-10.14.6.zip"
z3OSXPath = "https://github.com/Z3Prover/z3/releases/download/Nightly/" ++ z3OSXName

-- Get these from whatever the "official" latest GHC release is
-- Prev versions are what's available from ppa: https://launchpad.net/~hvr/+archive/ubuntu/ghc/
ghcLatest, cabalLatest, ghcPrev, cabalPrev :: String
ghcLatest   = "8.10.2"
cabalLatest = "3.2"
ghcPrev     = "8.8.4"
cabalPrev   = "3.2"

---------------------------------------------------------------------------------
-- Hopefully none of the below needs to change. At least that's the goal!
---------------------------------------------------------------------------------
travisFile, appveyorFile :: FilePath
travisFile   = "../.travis.yml"
appveyorFile = "../.appveyor.yml"

main :: IO ()
main = do as <- getArgs
          case as of
            ["appveyor"] -> do writeFile appveyorFile $ unlines appveyor
                               putStrLn $ "Generated: " ++ appveyorFile
            ["travis"]   -> do writeFile travisFile $ unlines travis
                               putStrLn $ "Generated: " ++ travisFile
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

data Tweaks = Tweaks { heavyTestPercentage :: Int
                     , ghcVersion          :: String
                     , cabalInstallVersion :: String
                     , z3Name              :: String
                     , z3Path              :: String
                     , extras              :: [String]
                     }

mkEnvs :: Int -> Bool -> String -> String -> String
mkEnvs perc extraChecks os suff =    "env: TASTY_HIDE_SUCCESSES=True"
                                  ++ " SBV_EXTRA_CHECKS=" ++ show extraChecks
                                  ++ " SBV_TEST_ENVIRONMENT=" ++ os
                                  ++ " SBV_HEAVYTEST_PERCENTAGE=" ++ show perc
                                  ++ " TASTY_HIDE_SUCCESSES=True"
                                  ++ s
  where s = case suff of
              "" -> ""
              _  -> ' ' : suff

winTweaks :: Tweaks
winTweaks = Tweaks { heavyTestPercentage = 0
                   , ghcVersion          = ghcLatest
                   , cabalInstallVersion = cabalLatest
                   , z3Name              = z3WindowsName
                   , z3Path              = z3WindowsPath
                   , extras              = []
                   }

stableLinTweaks :: Tweaks
stableLinTweaks = Tweaks { heavyTestPercentage = testPerc
                         , ghcVersion          = ghcLatest
                         , cabalInstallVersion = cabalLatest
                         , z3Name              = z3LinuxName
                         , z3Path              = z3LinuxPath
                         , extras              = [mkEnvs testPerc True "linux" ""]
                         }
  where testPerc     = 15

prevLinTweaks :: Tweaks
prevLinTweaks = Tweaks { heavyTestPercentage = testPerc
                       , ghcVersion          = ghcPrev
                       , cabalInstallVersion = cabalPrev
                       , z3Name              = z3LinuxName
                       , z3Path              = z3LinuxPath
                       , extras              = [mkEnvs testPerc True "linux" ""]
                       }
  where testPerc     = 30

osxTweaks :: Tweaks
osxTweaks = Tweaks { heavyTestPercentage = testPerc
                   , ghcVersion          = ghcLatest
                   , cabalInstallVersion = cabalLatest
                   , z3Name              = z3OSXName
                   , z3Path              = z3OSXPath
                   , extras              = ["os: osx", mkEnvs testPerc False "osx" ""]
                   }
  where testPerc     = 15

appveyor :: [String]
appveyor = header ++ body ++ footer
 where Tweaks{heavyTestPercentage, ghcVersion, z3Name, z3Path} = winTweaks

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
              , "- choco install -y ghc --version " ++ ghcVersion
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
              , "- cabal new-update"
              , "- cabal new-build --only-dependencies --enable-tests -f skipHLintTester"
              , "- cabal new-install all --lib"
              , "# Skipping tests till we find a CI solution that can handle it."
              , "# - cabal new-test"
              , "- cabal new-sdist"
              ]

-- The initial body of this script was generated by:
--
--     haskell-ci sbv.cabal --ghc-head --output .travis.yml --osx 8.6.5 --no-haddock
--
-- and then modified to install z3 and do other tweaks.
travis :: [String]
travis                              = header ++ body ++ footer
 where Tweaks{ ghcVersion           = lin1GHCVer
             , cabalInstallVersion  = lin1CabalVer
             , z3Name               = lin1Z3Name
             , z3Path               = lin1Z3Path
             , extras               = lin1Extras
             } = stableLinTweaks
       Tweaks{ ghcVersion           = lin2GHCVer
             , cabalInstallVersion  = lin2CabalVer
             , extras               = lin2Extras
             } = prevLinTweaks
       Tweaks{ ghcVersion           = osxGHCVer
             , cabalInstallVersion  = osxCabalVer
             , z3Name               = osxZ3Name
             , z3Path               = osxZ3Path
             , extras               = osxExtras
             } = osxTweaks

       body = [ "language: c"
              , "dist: xenial"
              , ""
              , "git:"
              , "  submodules: false"
              , ""
              , "cache:"
              , "  directories:"
              , "    - $HOME/.cabal/packages"
              , "    - $HOME/.cabal/store"
              , "    - $HOME/.ghc-install"
              , ""
              , "before_cache:"
              , "  - rm -fv $CABALHOME/packages/hackage.haskell.org/build-reports.log"
              , "  - rm -fv $CABALHOME/packages/hackage.haskell.org/00-index.*"
              , "  - rm -fv $CABALHOME/packages/hackage.haskell.org/*.json"
              , "  - rm -fv $CABALHOME/packages/hackage.haskell.org/01-index.cache"
              , "  - rm -fv $CABALHOME/packages/hackage.haskell.org/01-index.tar"
              , "  - rm -fv $CABALHOME/packages/hackage.haskell.org/01-index.tar.idx"
              , "  - rm -rfv $CABALHOME/packages/head.hackage"
              , ""
              , "notifications:"
              , "  email:"
              , "    - erkokl@gmail.com"
              , "  on_success: always"
              , "  on_failure: always"
              , ""
              , "matrix:"
              , "  include:"
              , "    - compiler: \"ghc-" ++ lin1GHCVer ++ "\""
              , "      addons: {apt: {packages: [ghc-ppa-tools,cabal-install-" ++ lin1CabalVer ++ ",ghc-" ++ lin1GHCVer ++ "], sources: [hvr-ghc]}}"
              ]
           ++ [ "      " ++ e | e <- lin1Extras]
           ++ [ "    - compiler: \"ghc-" ++ lin2GHCVer ++ "\""
              , "      addons: {apt: {packages: [ghc-ppa-tools,cabal-install-" ++ lin2CabalVer ++ ",ghc-" ++ lin2GHCVer ++ "], sources: [hvr-ghc]}}"
              ]
           ++ [ "      " ++ e | e <- lin2Extras]
           ++ [ "    - compiler: \"ghc-" ++ osxGHCVer ++ "\""
              , "      addons: {apt: {packages: [ghc-ppa-tools,cabal-install-" ++ osxCabalVer ++ ",ghc-"  ++ osxGHCVer  ++ "], sources: [hvr-ghc]}}"
              ]
           ++ [ "      " ++ e | e <- osxExtras]
           ++ [ ""
              , "before_install:"
              , "  - HC=/opt/ghc/bin/${CC}"
              , "  - HCPKG=${HC/ghc/ghc-pkg}"
              , "  - unset CC"
              , "  - CABAL=/opt/ghc/bin/cabal"
              , "  - CABALHOME=$HOME/.cabal"
              , "  - export PATH=\"$CABALHOME/bin:$PATH\""
              , "  - ROOTDIR=$(pwd)"
              , "  - if [ \"$TRAVIS_OS_NAME\" = \"linux\" ]; then curl -fsSL " ++ lin1Z3Path ++ " -o " ++ lin1Z3Name ++ "; unzip -j " ++ lin1Z3Name ++ " -d z3_downloaded; export PATH=$PATH:$(pwd)/z3_downloaded; z3 --version; fi"
              , "  - if [ \"$TRAVIS_OS_NAME\" = \"osx\" ]; then curl -fsSL " ++ osxZ3Path ++ " -o " ++ osxZ3Name ++ "; unzip -j " ++ osxZ3Name ++ " -d z3_downloaded; export PATH=$PATH:$(pwd)/z3_downloaded; z3 --version; fi"
              , "  - if [ \"$TRAVIS_OS_NAME\" = \"osx\" ]; then curl https://haskell.futurice.com/haskell-on-macos.py | python3 - --make-dirs --install-dir=$HOME/.ghc-install --cabal-alias=head install cabal-install-head ${TRAVIS_COMPILER}; fi"
              , "  - if [ \"$TRAVIS_OS_NAME\" = \"osx\" ]; then HC=$HOME/.ghc-install/ghc/bin/$TRAVIS_COMPILER; HCPKG=${HC/ghc/ghc-pkg}; CABAL=$HOME/.ghc-install/ghc/bin/cabal; fi"
              , "  - HCNUMVER=$(( $(${HC} --numeric-version|sed -E 's/([0-9]+)\\.([0-9]+)\\.([0-9]+).*/\\1 * 10000 + \\2 * 100 + \\3/') ))"
              , "  - echo $HCNUMVER"
              , ""
              , "install:"
              , "  - ${CABAL} --version"
              , "  - echo \"$(${HC} --version) [$(${HC} --print-project-git-commit-id 2> /dev/null || echo '?')]\""
              , "# - TEST=--enable-tests"
              , "  - TEST="
              , "# - BENCH=--enable-benchmarks"
              , "  - BENCH="
              , "  - GHCHEAD=${GHCHEAD-false}"
              , "  - travis_retry ${CABAL} update -v"
              , "  - sed -i.bak 's/^jobs:/-- jobs:/' $CABALHOME/config"
              , "  - rm -fv cabal.project cabal.project.local"
              , "  - grep -Ev -- '^\\s*--' $CABALHOME/config | grep -Ev '^\\s*$'"
              , "  - rm -f cabal.project"
              , "  - touch cabal.project"
              , "  - \"printf 'packages: \\\".\\\"\\\\n' >> cabal.project\""
              , "  - \"printf 'write-ghc-environment-files: always\\\\n' >> cabal.project\""
              , "  - touch cabal.project.local"
              , "  - \"for pkg in $($HCPKG list --simple-output); do echo $pkg | sed 's/-[^-]*$//' | grep -vE -- '^(sbv)$' | sed 's/^/constraints: /' | sed 's/$/ installed/' >> cabal.project.local; done\""
              , "  - cat cabal.project || true"
              , "  - cat cabal.project.local || true"
              , "  - if [ -f \"./configure.ac\" ]; then (cd \".\" && autoreconf -i); fi"
              , "  - rm -f cabal.project.freeze"
              , "  - ${CABAL} new-freeze -f skipHLintTester -w ${HC} ${TEST} ${BENCH} --project-file=\"cabal.project\" --dry"
              , "  - \"cat \\\"cabal.project.freeze\\\" | sed -E 's/^(constraints: *| *)//' | sed 's/any.//'\""
              , "  - rm  \"cabal.project.freeze\""
              , "  - ${CABAL} new-build -f skipHLintTester -w ${HC} ${TEST} ${BENCH} --project-file=\"cabal.project\" --dep -j2 all"
              , "  - rm -rf .ghc.environment.* \".\"/dist"
              , "  - DISTDIR=$(mktemp -d /tmp/dist-test.XXXX)"
              , ""
              , "script:"
              , "  - ${CABAL} new-install -f skipHLintTester -w ${HC} ${TEST} ${BENCH} all --lib"
              , "  # Skipping tests till we find a CI solution that can handle it."
              , "  # - if [ \"x$TEST\" = \"x--enable-tests\" ]; then ${CABAL} new-test -f skipHLintTester -w ${HC} ${TEST} ${BENCH} all; fi"
              , ""
              , "  # cabal check"
              , "  - ${CABAL} check"
              ]
