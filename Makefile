# (c) Copyright Levent Erkok. All rights reserved.
#
# The sbv library is distributed with the BSD3 license. See the LICENSE file
# in the distribution for details.

OS := $(shell uname)
SHELL := /usr/bin/env bash

CONFIGOPTS = "-Wall -fhide-source-paths"

ALLSOURCES := $(shell find Data/SBV -name "*.hs") $(shell find Documentation/SBV -name "*.hs")

ifeq ($(OS), Darwin)
# OSX tends to sleep for long jobs; so run through caffeinate
TIME        = /usr/bin/time caffeinate -dimsu
NO_OF_CORES = `sysctl hw.ncpu | awk '{print $$2}'`
else
TIME        = /usr/bin/time
NO_OF_CORES = `grep -c "^processor" /proc/cpuinfo`
endif

ifdef TGT
    TESTTARGET = -p ${TGT}
    TESTHIDE   = --hide-successes
else
    TESTTARGET =
    TESTHIDE   = --hide-successes
endif

ifdef ACCEPT
    TESTACCEPT = --accept
    TESTHIDE   = 
else
    TESTACCEPT = --no-create
    TESTHIDE   = --hide-successes
endif

# How long to wait for each doctest to run (in seconds)
DOCTESTTIMEOUT = 300

.PHONY: install docs testsuite release tags clean veryclean timeRelease

all: quick

quick: tags
	@$(TIME) cabal new-install --lib
	
install: tags
	@$(TIME) cabal new-configure --enable-tests --allow-newer --ghc-options=$(CONFIGOPTS)
	@$(TIME) cabal new-install --lib

docs:
	cabal new-haddock --haddock-option=--hyperlinked-source --haddock-option=--no-warnings

ghci:
	cabal new-repl --repl-options=-Wno-unused-packages

ghcid:
	ghcid --command="cabal new-repl --repl-options=-Wno-unused-packages"

ghci_SBVTest:
	cabal new-repl --repl-options=-Wno-unused-packages SBVTest

ghcid_SBVTest:
	ghcid --command="cabal new-repl --repl-options=-Wno-unused-packages SBVTest"

ghci_SBVDocTest:
	cabal new-repl --repl-options=-Wno-unused-packages SBVDocTest

ghcid_SBVDocTest:
	ghcid --command="cabal new-repl --repl-options=-Wno-unused-packages SBVDocTest"

ghci_HLint:
	cabal new-repl --repl-options=-Wno-unused-packages SBVHLint

ghcid_HLint:
	ghcid --command="cabal new-repl --repl-options=-Wno-unused-packages SBVHLint"

ghci_Bench:
	cabal new-repl --repl-options=-Wno-unused-packages SBVBench

ghcid_Bench:
	ghcid --command="cabal new-repl --repl-options=-Wno-unused-packages SBVBench"

bench:
	cabal new-bench

testsuite: lintTest docTest test

-- To do a faster hlint without compiling, use FAST=1 as a parameter: make lintTest FAST=1
lintTest:
ifdef FAST
	hlint Data SBVTestSuite -i "Use otherwise" -i "Parse error" --cpp-simple
else
	@$(TIME) cabal new-test SBVHLint
endif

testInterfaces:
	@$(TIME) cabal new-test SBVConnections

# If you specify TGT, it'll just run on that target. Give the full path to the haskell file with .hs extension
# If you also specify FAST, it won't compile first; good when you change the "comment" but not the code
docTest:
ifdef TGT
ifdef FAST
	cabal-docspec --timeout ${DOCTESTTIMEOUT} --module $(basename $(subst /,.,${TGT}))
else
	cabal new-run SBVDocTest -- --timeout ${DOCTESTTIMEOUT} --module $(basename $(subst /,.,${TGT}))
endif
else
	@$(TIME) cabal new-run SBVDocTest -- --timeout ${DOCTESTTIMEOUT}
endif

test:
	@$(TIME) cabal new-run SBVTest -- -j $(NO_OF_CORES) ${TESTTARGET} ${TESTACCEPT} ${TESTHIDE}

checkLinks:
	@brok --no-cache --only-failures $(ALLSOURCES) COPYRIGHT INSTALL LICENSE $(wildcard *.md)

mkDistro:
	$(TIME) cabal new-sdist

# Useful if we update z3 (or some other solver) but don't make any changes to SBV
releaseNoBuild: testsuite testInterfaces mkDistro checkLinks
	@echo "*** SBV is ready for release! -- no SBV build was done."

fullRelease: veryclean checkExtensions install docs testsuite testInterfaces mkDistro checkLinks
	@echo "*** SBV is ready for release!"

release:
	$(TIME) make fullRelease

checkExtensions:
	@ag LANGUAGE | awk '{print $$3}' | sort | uniq | grep -v LANGUAGE | grep -v ignore | grep -v note | grep -v "^\""| grep -v "<-" > ./required_extensions
	@ghc -package base -package process ./buildUtils/checkExtensions.hs -e main
	@/bin/rm -f required_extensions

tags:
	@fast-tags -R --nomerge .

ci:
	haskell-ci github sbv.cabal --no-tests --no-benchmarks

clean:
	@rm -rf dist dist-newstyle cabal.project.local*

veryclean: clean
	@make -C buildUtils clean
