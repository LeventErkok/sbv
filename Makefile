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

.PHONY: all install test doctest externaltest internaltest sdist clean docs gold stamp hlint tags checkLinks testInterfaces

all: install

install: 
	@tput rmam
	@(make -s -C buildUtils testInterfaces)
	@fast-tags -R --nomerge .
	@cabal configure --enable-tests --ghc-options="-Werror -Wall"
	@cabal build
	@cabal install
	@tput smam

test: install doctest externaltest internaltest

doctest:
	@tput rmam
	@echo "*** Starting inline tests.."
	@$(TIME) doctest ${TSTSRCS}
	@tput smam

externaltest:
	@tput rmam
	@echo "*** Starting external test suite.."
	@# Note we use "-s" here skipping no-solver tests; which are covered
	@# in the cabal test suite right below.
	@$(TIME) dist/build/SBVUnitTests/SBVUnitTests -s
	@tput smam

internaltest:
	@tput rmam
	@echo "*** Starting internal cabal test suite.."
	@SBV_Z3=doesnotexist $(TIME) cabal test SBVBasicTets
	@cat dist/test/sbv*SBVBasicTests.log
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

# use this as follows: make gold TGTS="cgUSB5"
# where the tag is one (or many) given in the SBVUnitTest.hs file
# if TGTS is not specified, then all gold files are regenerated
gold: install
	dist/build/SBVUnitTests/SBVUnitTests -c ${TGTS}

hlint: 
	@rm -f hlintReport.html
	@echo "Running HLint.."
	@hlint Data SBVUnitTest -q -rhlintReport.html -i "Use otherwise" -i "Parse error" -i "Use fewer imports" -i "Use module export list"

checkLinks:
	@buildUtils/checkLinks

testInterfaces:
	make -C buildUtils
	@buildUtils/testInterfaces

tags:
	@fast-tags -R --nomerge .
