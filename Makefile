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

test: install doctest
	@tput rmam
	@SBV_Z3=doesnotexist $(TIME) cabal test SBVBasicTests
	@                    $(TIME) ./dist/build/int-test-extended/int-test-extended -j 4
	@tput smam

# use this as follows: make gold TGT="cgUSB5"
gold: 
	./dist/build/int-test-extended/int-test-extended -p ${TGT} --accept

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

hlint: 
	@echo "Running HLint.."
	@hlint Data SBVUnitTest -i "Use otherwise" -i "Parse error" -i "Use fewer imports" -i "Use module export list"

uploadDocs:
	@buildUtils/hackage-docs

checkLinks:
	@buildUtils/checkLinks

testInterfaces:
	make -C buildUtils
	@buildUtils/testInterfaces

tags:
	@fast-tags -R --nomerge .
