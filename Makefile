# (c) Copyright Levent Erkok. All rights reserved.
#
# The sbv library is distributed with the BSD3 license. See the LICENSE file
# in the distribution for details.
SHELL     := /usr/bin/env bash
TSTSRCS   = $(shell find . -name '*.hs' -or -name '*.lhs' | grep -v SBVUnitTest/SBVUnitTest.hs | grep -v SBVUnitTest/SBVBasicTests.hs | grep -v buildUtils/simplify.hs)
STAMPFILE = SBVUnitTest/SBVUnitTestBuildTime.hs
DEPSRCS   = $(shell find . -name '*.hs' -or -name '*.lhs' -or -name '*.cabal' | grep -v Paths_sbv.hs | grep -v $(STAMPFILE))
CABAL     = cabal
SIMPLIFY  = ./buildUtils/simplify
TIME      = /usr/bin/time

define mkStamp
	@echo "-- Auto-generated, don't edit"		       >  ${STAMPFILE}
	@echo "module SBVUnitTestBuildTime (buildTime) where"  >> ${STAMPFILE}
	@echo ""					       >> ${STAMPFILE}
	@echo "buildTime :: String"			       >> ${STAMPFILE}
	@echo "buildTime = \"$(shell date)\""		       >> ${STAMPFILE}
endef

define mkTags
	@find . -name \*.\*hs | xargs fast-tags
endef

.PHONY: all install test sdist clean docs gold stamp hlint tags

all: install

install: $(STAMPFILE)

$(STAMPFILE): $(DEPSRCS) Makefile
	@-ghc-pkg unregister sbv
	@(make -s -C buildUtils)
	$(call mkStamp)
	$(call mkTags)
	@$(CABAL) configure --disable-library-profiling --enable-tests
	@((set -o pipefail; $(CABAL) build --ghc-options=-Werror 2>&1 | $(SIMPLIFY)) || (rm $(STAMPFILE) && false))
	@$(CABAL) copy
	@$(CABAL) register

test: install
	@echo "*** Starting inline tests.."
	@(set -o pipefail; $(TIME) doctest ${TSTSRCS} 2>&1)
	@echo "*** Starting external test suite.."
	@$(TIME) dist/build/SBVUnitTests/SBVUnitTests -s
	@echo "*** Starting internal cabal test suite.."
	@SBV_Z3=doesnotexist $(TIME) $(CABAL) test
	@cat dist/test/sbv*SBVBasicTests.log

sdist: install
	@(set -o pipefail; $(CABAL) sdist | $(SIMPLIFY))

veryclean: clean
	@make -C buildUtils clean
	@-ghc-pkg unregister sbv

clean:
	@rm -rf dist $(STAMPFILE)

docs:
	@(set -o pipefail; $(CABAL) haddock --haddock-option=--no-warnings --hyperlink-source 2>&1 | $(SIMPLIFY))

release: clean install sdist hlint test docs
	@echo "*** SBV is ready for release!"

# use this as follows: make gold TGTS="cgUSB5"
# where the tag is one (or many) given in the SBVUnitTest.hs file
# if TGTS is not specified, then all gold files are regenerated
gold: install
	dist/build/SBVUnitTests/SBVUnitTests -c ${TGTS}

hlint: install
	@echo "Running HLint.."
	@hlint Data SBVUnitTest -q -rhlintReport.html -i "Use otherwise" -i "Parse error"

tags:
	$(call mkTags)
