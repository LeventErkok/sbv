# (c) Copyright Levent Erkok. All rights reserved.
#
# The sbv library is distributed with the BSD3 license. See the LICENSE file
# in the distribution for details.

OS := $(shell uname)

SHELL := /usr/bin/env bash

export SBV_TEST_ENVIRONMENT := local

ifeq ($(OS), Darwin)
# OSX tends to sleep for long jobs; so run through caffeinate
TIME        = /usr/bin/time caffeinate
NO_OF_CORES = `sysctl hw.ncpu | awk '{print $$2}'`
else
TIME        = /usr/bin/time
NO_OF_CORES = `grep -c "^processor" /proc/cpuinfo`
endif

.PHONY: install docs test release testPattern tags uploadDocs clean veryclean

all: install

install: tags
	@$(TIME) cabal configure --enable-tests --ghc-options="-Werror -Wall -fhide-source-paths"
	@$(TIME) cabal build
	@$(TIME) cabal install --force-reinstalls

docs:
	cabal haddock --haddock-option=--hyperlinked-source --haddock-option=--no-warnings

test:
	@$(TIME) ./dist/build/SBVTest/SBVTest --hide-successes -j $(NO_OF_CORES)
	# @$(TIME) ./dist/build/SBVDocTest/SBVDocTest
	doctest Data
	@$(TIME) ./dist/build/SBVHLint/SBVHLint

release: veryclean install docs test
	cabal sdist
	@make -C buildUtils veryclean
	@make -C buildUtils
	buildUtils/testInterfaces
	buildUtils/checkLinks
	@echo "*** SBV is ready for release!"

# use this as follows:
#         make testPattern TGT=U2Bridge
testPattern:
	./dist/build/SBVTest/SBVTest -p ${TGT}

tags:
	@fast-tags -R --nomerge .

uploadDocs:
	@buildUtils/hackage-docs

hlint: 
	@echo "Running HLint.."
	@hlint Data SBVTestSuite -i "Use otherwise" -i "Parse error" -i "Use fewer imports" -i "Use module export list" -i "Use import/export shortcut"

clean:
	@rm -rf dist

veryclean: clean
	@make -C buildUtils clean
	@-ghc-pkg unregister sbv
