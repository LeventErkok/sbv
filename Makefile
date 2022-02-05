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
    TESTTARGET =-p ${TGT}
    TESTHIDE   =
else
    TESTTARGET =
    TESTHIDE   = --hide-successes
endif

ifdef ACCEPT
    TESTACCEPT=--accept
    TESTHIDE  =
else
    TESTACCEPT=--no-create
endif

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

ghci_SBVTest:
	cabal new-repl --repl-options=-Wno-unused-packages SBVTest

ghci_SBVDocTest:
	cabal new-repl --repl-options=-Wno-unused-packages SBVDocTest

ghci_HLint:
	cabal new-repl --repl-options=-Wno-unused-packages SBVHLint

ghci_Bench:
	cabal new-repl --repl-options=-Wno-unused-packages SBVBench

ghcid:
	ghcid --command="cabal new-repl --repl-options=-Wno-unused-packages"

bench:
	cabal new-bench

testsuite: lintTest docTest test

lintTest:
	@$(TIME) cabal new-test SBVHLint

testInterfaces:
	@$(TIME) cabal new-test SBVConnections

docTest:
	@$(TIME) cabal new-run SBVDocTest

# Check a single module using doctest:
#   make docTestModule TGT=Documentation/SBV/Examples/Lists/CountOutAndTransfer
docTestModule:
	cabal-docspec --verbose --trace-process --timeout=100 --module $(basename $(subst /,.,${TGT}))

test:
	@$(TIME) cabal new-run SBVTest -- -j $(NO_OF_CORES) ${TESTTARGET} ${TESTACCEPT} ${TESTHIDE}

checkLinks:
	@brok --no-cache --only-failures $(ALLSOURCES) COPYRIGHT INSTALL LICENSE $(wildcard *.md)

mkDistro:
	$(TIME) cabal new-sdist

# Useful if we update z3 (or some other solver) but don't make any changes to SBV
releaseNoBuild: testsuite testInterfaces mkDistro checkLinks
	@echo "*** SBV is ready for release! -- no SBV build was done."

fullRelease: veryclean install docs testsuite testInterfaces mkDistro checkLinks
	@echo "*** SBV is ready for release!"

release:
	$(TIME) make fullRelease

tags:
	@fast-tags -R --nomerge .

ci:
	haskell-ci github sbv.cabal --no-tests --no-benchmarks

clean:
	@rm -rf dist dist-newstyle cabal.project.local*

veryclean: clean
	@make -C buildUtils clean
