# (c) Copyright Levent Erkok. All rights reserved.
#
# The sbv library is distributed with the BSD3 license. See the LICENSE file
# in the distribution for details.
SHELL     := /usr/bin/env bash
TSTSRCS   = $(shell find . -name '*.hs' -or -name '*.lhs' | grep -v SBVUnitTest/SBVUnitTest.hs | grep -v SBVUnitTest/SBVBasicTests.hs | grep -v buildUtils/testInterfaces.hs | grep -v sandbox | grep -v GHC/SrcLoc/Compat.hs)
# OSX tends to sleep for long jobs; so run through caffeinate
TIME      = /usr/bin/time caffeinate

define mkTags
	@find . -name \*.\*hs | xargs fast-tags
endef

.PHONY: all install test doctest externaltest internaltest sdist clean docs gold stamp hlint tags checkLinks testInterfaces

all: install

install: 
	@(make -s -C buildUtils testInterfaces)
	$(call mkTags)
	@cabal configure --enable-tests --ghc-options="-Werror -Wall"
	@cabal build
	@cabal install

test: install doctest externaltest internaltest

doctest:
	@echo "*** Starting inline tests.."
	$(TIME) doctest ${TSTSRCS}

externaltest:
	@echo "*** Starting external test suite.."
	@# Note we use "-s" here skipping no-solver tests; which are covered
	@# in the cabal test suite right below.
	@$(TIME) dist/build/SBVUnitTests/SBVUnitTests -s

internaltest:
	@echo "*** Starting internal cabal test suite.."
	@SBV_Z3=doesnotexist $(TIME) cabal test
	@cat dist/test/sbv*SBVBasicTests.log

sdist: install
	cabal sdist

veryclean: clean
	@make -C buildUtils clean
	@-ghc-pkg unregister sbv

clean:
	@rm -rf dist $(STAMPFILE)

docs:
	cabal haddock --haddock-option=--no-warnings --hyperlink-source

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
	$(call mkTags)
