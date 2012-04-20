# (c) Copyright Levent Erkok. All rights reserved.
#
# The sbv library is distributed with the BSD3 license. See the LICENSE file
# in the distribution for details.
SHELL     := /usr/bin/env bash
SRCS      = $(shell find . -name '*.hs' -or -name '*.lhs' | grep -v SBVUnitTest/SBVUnitTest.hs | grep -v buildUtils/simplify.hs)
LINTSRCS  = $(shell find . -name '*.hs' -or -name '*.lhs' | grep -v Paths_sbv.hs)
STAMPFILE = SBVUnitTest/SBVUnitTestBuildTime.hs
DEPSRCS   = $(shell find . -name '*.hs' -or -name '*.lhs' -or -name '*.cabal' | grep -v Paths_sbv.hs | grep -v $(STAMPFILE))
CABAL     = cabal
CABPFLAGS = --disable-library-profiling --enable-documentation --ghc-options=-Werror
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

$(STAMPFILE): $(DEPSRCS)
	@(make -s -C buildUtils)
	$(call mkStamp)
	$(call mkTags)
	@((set -o pipefail; $(CABAL) $(CABPFLAGS) install 2>&1 | $(SIMPLIFY)) || (rm $(STAMPFILE) && false))

test: install
	@echo "Executing inline tests.."
	@(set -o pipefail; $(TIME) doctest ${SRCS} 2>&1)
	@echo "Starting external test suite.."
	@$(TIME) SBVUnitTests

sdist: install
	@(set -o pipefail; $(CABAL) sdist | $(SIMPLIFY))

veryclean: clean
	make -C buildUtils clean
clean:
	rm -rf dist $(STAMPFILE)

docs:
	@(set -o pipefail; $(CABAL) haddock --haddock-option=--no-warnings --hyperlink-source 2>&1 | $(SIMPLIFY))

release: clean install sdist hlint test
	@echo "*** SBV is ready for release!"

# use this as follows: make gold TGTS="cgUSB5"
# where the tag is one (or many) given in the SBVUnitTest.hs file
# if TGTS is not specified, then all gold files are regenerated
gold: install
	dist/build/SBVUnitTests/SBVUnitTests -c ${TGTS}

hlint: install
	@echo "Running HLint.."
	@hlint ${LINTSRCS} -q -rhlintReport.html -i "Use otherwise" -i "Parse error"

tags:
	$(call mkTags)
