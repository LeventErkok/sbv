# (c) Copyright Levent Erkok. All rights reserved.
#
# The sbv library is distributed with the BSD3 license. See the LICENSE file
# in the distribution for details.

OS := $(shell uname)

GHCVERSION := $(shell ghc --version | awk '{print $$NF}')
CONFIGOPTS = "-Wall -fhide-source-paths"
CBUILD=new-build
CINSTALL=new-install
CCONFIGURE=new-configure
CHADDOCK=new-haddock
CSDIST=new-sdist

SHELL := /usr/bin/env bash

export SBV_TEST_ENVIRONMENT := local

DOCTESTSOURCES := $(shell find Data/SBV -name "*.hs") $(shell find Documentation/SBV -name "*.hs")

ifeq ($(OS), Darwin)
# OSX tends to sleep for long jobs; so run through caffeinate
TIME        = /usr/bin/time caffeinate -dimsu
NO_OF_CORES = `sysctl hw.ncpu | awk '{print $$2}'`
else
TIME        = /usr/bin/time
NO_OF_CORES = `grep -c "^processor" /proc/cpuinfo`
endif

.PHONY: install docs test release testPattern tags clean veryclean

all: quick

quick: tags
	@$(TIME) cabal $(CBUILD)
	@$(TIME) cabal $(CINSTALL) --lib --force-reinstalls
	
install: tags
	@$(TIME) cabal $(CCONFIGURE) --enable-tests --ghc-options=$(CONFIGOPTS)
	@$(TIME) cabal $(CBUILD)
	@$(TIME) cabal $(CINSTALL) --lib --force-reinstalls

docs:
	cabal $(CHADDOCK) --haddock-option=--hyperlinked-source --haddock-option=--no-warnings

test: lintTest docTest regularTests

lintTest:
	@$(TIME) cabal new-test SBVHLint

docTest:
	@$(TIME) cabal new-run SBVDocTest -- --fast --no-magic

vdocTest:
	@$(TIME) cabal new-run SBVDocTest -- --verbose --fast --no-magic

regularTests:
	@$(TIME) cabal new-run SBVTest -- --hide-successes -j $(NO_OF_CORES)

checkLinks:
	@brok --no-cache --only-failures $(DOCTESTSOURCES) COPYRIGHT INSTALL LICENSE $(wildcard *.md)

testInterfaces:
	@make -C buildUtils veryclean
	@make -C buildUtils
	buildUtils/testInterfaces

mkDistro:
	$(TIME) cabal $(CSDIST)

release: veryclean install docs test testInterfaces mkDistro checkLinks
	@echo "*** SBV is ready for release!"

# use this as follows:
#         make testPattern TGT=U2Bridge
testPattern:
	$(TIME) cabal new-run SBVTest -- --hide-successes -p ${TGT}

# use this as follows:
#         make docTestPattern TGT=./Documentation/SBV/Examples/Puzzles/HexPuzzle.hs
docTestPattern:
	$(TIME) doctest --fast --no-magic --verbose ${TGT}

tags:
	@fast-tags -R --nomerge .

hlint: 
	@echo "Running HLint.."
	@hlint Data SBVTestSuite -i "Use otherwise" -i "Parse error"

ghcid:
	ghcid --lint

clean:
	@rm -rf dist dist-newstyle cabal.project.local*

veryclean: clean
	@make -C buildUtils clean
	@-ghc-pkg unregister sbv
