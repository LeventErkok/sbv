# (c) Copyright Levent Erkok. All rights reserved.
#
# The sbv library is distributed with the BSD3 license. See the LICENSE file
# in the distribution for details.

OS := $(shell uname)

SHELL   := /usr/bin/env bash
TSTSRCS = $(shell find . -name '*.hs' | grep -v SBVUnitTest | grep -v buildUtils | grep -v sandbox | grep -v GHC/SrcLoc/Compat.hs)

ifeq ($(OS), Darwin)
# OSX tends to sleep for long jobs; so run through caffeinate
TIME      = /usr/bin/time caffeinate
else
TIME      = /usr/bin/time
endif

.PHONY: all install test doctest internaltest sdist clean docs gold hlint tags checkLinks testInterfaces

all: install

install: 
	@tput rmam
	@(make -s -C buildUtils testInterfaces)
	@fast-tags -R --nomerge .
	@cabal configure --enable-tests --ghc-options="-Werror -Wall"
	@cabal build
	@cabal install --force-reinstalls
	@tput smam

# NB. Don't use cabal test in this target; we want to see the verbose output.
test: install doctest
	@tput rmam
	@SBV_Z3=doesnotexist $(TIME) ./dist/build/SBVBasicTests/SBVBasicTests
	@                    $(TIME) ./dist/build/int-test-extended/int-test-extended -p '**' -j 4
	@tput smam

# use this as follows:
#          /bin/rm SBVUnitTest/GoldFiles/U2Bridge.gold
#          make gold TGT="U2Bridge"
gold: 
	./dist/build/int-test-extended/int-test-extended -p ${TGT}


# use this as follows:
#         make testPattern TGT="U2Bridge"
testPattern:
	./dist/build/int-test-extended/int-test-extended -p ${TGT}

doctest:
	@tput rmam
	@echo "*** Starting inline tests.."
	@$(TIME) doctest ${TSTSRCS}
	@tput smam

sdist: install
	@tput rmam
	cabal sdist
	@tput smam

veryclean: clean
	@make -C buildUtils clean
	@-ghc-pkg unregister sbv

clean:
	@rm -rf dist $(STAMPFILE)

docs:
	@tput rmam
	cabal haddock --haddock-option=--hyperlinked-source --haddock-option=--no-warnings
	@tput smam

release: clean checkLinks install sdist testInterfaces hlint docs test
	@echo "*** SBV is ready for release!"

# same as release really, but doesn't check links and tests fewer solver connections.
# suitable to use when we're in more poverished environment.
limitedRelease: clean install sdist limitedTestInterfaces hlint docs test
	@echo "*** SBV is looking OK, but you should really run the 'release' target!"

hlint: 
	@echo "Running HLint.."
	@hlint Data SBVUnitTest -i "Use otherwise" -i "Parse error" -i "Use fewer imports" -i "Use module export list" -i "Use import/export shortcut"

uploadDocs:
	@buildUtils/hackage-docs

checkLinks:
	@tput rmam
	@buildUtils/checkLinks
	@tput smam

testInterfaces:
	make -C buildUtils
	@buildUtils/testInterfaces

# only test connection to a few solvers
limitedTestInterfaces:
	make -C buildUtils
	@buildUtils/testInterfaces Yices Z3 CVC4

tags:
	@fast-tags -R --nomerge .
