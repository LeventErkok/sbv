# (c) Copyright Levent Erkok. All rights reserved.
#
# The sbv library is distributed with the BSD3 license. See the LICENSE file
# in the distribution for details.
SHELL     := /usr/bin/env bash
SRCS      = $(shell find . -name '*.hs' -or -name '*.lhs' | grep -v SBVUnitTest/SBVUnitTest.hs | grep -v buildUtils/simplify.hs)
LINTSRCS  = $(shell find . -name '*.hs' -or -name '*.lhs' | grep -v Paths_sbv.hs)
STAMPFILE = SBVUnitTest/SBVUnitTestBuildTime.hs
DEPSRCS   = $(shell find . -name '*.hs' -or -name '*.lhs' | grep -v Paths_sbv.hs | grep -v $(STAMPFILE))
CABAL     = cabal
CABPFLAG  = --disable-library-profiling --disable-documentation --force-reinstalls --ghc-options=-Werror
SIMPLIFY  = ./buildUtils/simplify
TIME      = /usr/bin/time

.PHONY: all install test sdist clean docs gold stamp hlint simplify

all: simplify install

simplify:
	@(make -s -C buildUtils)

install: $(STAMPFILE)

$(STAMPFILE): $(DEPSRCS)
	@echo "-- Auto-generated, don't edit"		       >  ${STAMPFILE}
	@echo "module SBVUnitTestBuildTime (buildTime) where"  >> ${STAMPFILE}
	@echo ""					       >> ${STAMPFILE}
	@echo "buildTime :: String"			       >> ${STAMPFILE}
	@echo "buildTime = \"$(shell date)\""		       >> ${STAMPFILE}
	@find . -name \*.\*hs | xargs hasktags -c
	@sort -o tags tags
	@((set -o pipefail; $(CABAL) $(CABPFLAG) install 2>&1 | $(SIMPLIFY)) || (rm $(STAMPFILE) && false))

test:
	@echo "Executing inline tests.."
	@$(TIME) (doctest ${SRCS} | grep -v "Could not find documentation" | exit 0)
	@echo "Starting external test suite.."
	@$(TIME) SBVUnitTests

sdist:
	@(set -o pipefail; $(CABAL) sdist | $(SIMPLIFY))

clean:
	rm -rf dist $(STAMPFILE)

docs:
	@(set -o pipefail; $(CABAL) haddock --hyperlink-source 2>&1 | $(SIMPLIFY))

release: clean install sdist docs hlint test
	@echo "*** SBV is ready for release!"

# use this as follows: make gold TGTS="cgUSB5"
# where the tag is one (or many) given in the SBVUnitTest.hs file
# if TGTS is not specified, then all gold files are regenerated
gold:
	ghc -idist/build/autogen/ SBVUnitTest/SBVUnitTest.hs -e "createGolds \"${TGTS}\""

hlint:
	@echo "Running HLint.."
	@hlint ${LINTSRCS} -q -rhlintReport.html -i "Use otherwise" -i "Parse error"
