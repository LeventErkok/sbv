# (c) Copyright Levent Erkok. All rights reserved.
#
# The sbv library is distributed with the BSD3 license. See the LICENSE file
# in the distribution for details.

OS := $(shell uname)
SHELL := /usr/bin/env bash

CABAL_VERSION := $(shell cabal --numeric-version)

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

# how many quick-check tests to run (default of 100 might be too slow)
ifdef QC
    QCCOUNT = ${QC}
else
    QCCOUNT = 100
endif

# How long to wait for each doctest to run (in seconds)
DOCTESTTIMEOUT = 300

# Allow newer versions
CABAL_OPTS=--allow-newer

.PHONY: install docs testsuite release tags clean veryclean

all: quick

quick: tags
	@$(TIME) cabal install --lib ${CABAL_OPTS} --force-reinstalls
	
install: tags
	@$(TIME) cabal configure --enable-tests ${CABAL_OPTS} --ghc-options=$(CONFIGOPTS)
	@$(TIME) cabal install --lib ${CABAL_OPTS} --force-reinstalls


HADDOCK_OPTS=${CABAL_OPTS} --enable-documentation

docs:
	@cabal haddock ${HADDOCK_OPTS} --haddock-option=--hyperlinked-source      | ghc ./buildUtils/simpHaddock.hs -e main

# To upload docs to hackage, first run the below target (part of release), then run the next target..
hackage-docs:
	@cabal haddock ${HADDOCK_OPTS} --haddock-for-hackage | ghc ./buildUtils/simpHaddock.hs -e main
	@echo "*** If all is well, then run:"
	@echo "      cabal upload -d --publish ./dist-newstyle/sbv-XXX-docs.tar.gz"
	@echo "*** If the above fails for some reason, use the workaround in: https://github.com/haskell/cabal/issues/10252#issuecomment-2422130252"
	@echo "*** Don't forget to UPGRADE cabal version"

ghci:
ifdef TGT
	cabal repl ${CABAL_OPTS} --repl-options=-Wno-unused-packages ${TGT}
else
	cabal repl ${CABAL_OPTS} --repl-options=-Wno-unused-packages
endif

# Use to load in ghcid. Possibilities:
#     make ghcid
#     make ghcid TGT=SBVTest
#     make ghcid TGT=SBVConnections
#     make ghcid TGT=SBVHLint
#     make ghcid TGT=SBVBench
#     make ghcid TGT=SBVDocTest
ghcid:
ifdef TGT
	ghcid --command="cabal repl ${CABAL_OPTS} --repl-options=-Wno-unused-packages ${TGT}"
else
	ghcid --command="cabal repl ${CABAL_OPTS} --repl-options=-Wno-unused-packages ${TGT}"
endif

bench:
	cabal bench

# Run this target, which updates the golds for those tests that rely on version updates
# for SBV and Z3. Saves time before doing "make release"
updateForVersionChange:
	@cabal run SBVTest -- -p nested1 --accept --quiet
	@cabal run SBVTest -- -p nested2 --accept --quiet
	@cabal run SBVTest -- -p nested3 --accept --quiet
	@cabal run SBVTest -- -p nested4 --accept --quiet
	@cabal run SBVTest -- -p allSat8 --accept --quiet
	@cabal run SBVTest -- -p query1  --accept --quiet
	@cabal run SBVTest -- -p noOpt1  --accept --quiet
	@cabal run SBVTest -- -p noOpt2  --accept --quiet

testsuite: updateForVersionChange lintTest test testInterfaces benchBuild docTest mkDistro checkLinks

lintTest:
	@$(TIME) cabal test SBVHLint

testInterfaces:
	@$(TIME) cabal test SBVConnections

benchBuild:
	@$(TIME) cabal build SBVBench

DOCTEST_GOLD = SBVTestSuite/GoldFiles/doctest_sanity.gold

# If you specify TGT, it'll just run on that target. Give the full path to the haskell file with .hs extension
docTest:
ifdef TGT
	cabal run SBVDocTest ${CABAL_OPTS} -fdoctest_is_running -- --timeout ${DOCTESTTIMEOUT} --module $(basename $(subst /,.,${TGT}))
else
	@/bin/rm -f ${DOCTEST_GOLD}_temp
	@$(TIME) cabal run SBVDocTest ${CABAL_OPTS} -fdoctest_is_running -- --timeout ${DOCTESTTIMEOUT} 2>&1 | tee ${DOCTEST_GOLD}_temp
	@ghc -package process buildUtils/checkDocSpec.hs -e "start \"${DOCTEST_GOLD} ${ACCEPT}\""
endif

test:
	@$(TIME) cabal run ${CABAL_OPTS} SBVTest -- -j $(NO_OF_CORES) ${TESTTARGET} ${TESTACCEPT} ${TESTHIDE} --quickcheck-tests ${QCCOUNT}

checkLinks:
	@brok --no-cache --only-failures $(ALLSOURCES) COPYRIGHT INSTALL LICENSE $(wildcard *.md)

mkDistro:
	$(TIME) cabal sdist

fullRelease: veryclean checkExtensions install docs testsuite
	@echo "*** SBV is ready for release!"
	git status

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

# Just test the TP output for doctest. We give it a shorter wait time as well.
TP_FILES          = $(addprefix --module ,$(basename $(subst /,.,$(wildcard Data/SBV/TP/*.hs)))) 	       \
	            $(addprefix --module ,$(basename $(subst /,.,$(wildcard Documentation/SBV/Examples/TP/*.hs))))
TP_MODULES        = ${TP_FILES}
TP_DOCTESTTIMEOUT = 20
tpDocTest:
	cabal run SBVDocTest ${CABAL_OPTS} -fdoctest_is_running -- --timeout ${TP_DOCTESTTIMEOUT} ${TP_MODULES}
