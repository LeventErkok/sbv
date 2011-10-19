# (c) Copyright Levent Erkok. All rights reserved.
#
# The sbv library is distributed with the BSD3 license. See the LICENSE file
# in the distribution for details.

SRCS = $(shell find . -name '*.hs' -or -name '*.lhs' | grep -v SBVUnitTest/SBVUnitTest.hs)
STAMPFILE=SBVUnitTest/SBVUnitTestBuildTime.hs

.PHONY: all install test sdist clean docs gold tags stamp

all: install test sdist

install: stamp
	cabal install

stamp:
	@echo "-- Auto-generated, don't edit"				  >  ${STAMPFILE}
	@echo "module SBVUnitTest.SBVUnitTestBuildTime (buildTime) where" >> ${STAMPFILE}
	@echo ""							  >> ${STAMPFILE}
	@echo "buildTime :: String"					  >> ${STAMPFILE}
	@echo "buildTime = \"$(shell date)\""				  >> ${STAMPFILE}

test:
	@echo "Executing inline tests.."
	@time (doctest ${SRCS} | grep -v "Could not find documentation" | exit 0)
	@echo "Starting external test suite.."
	@time (SBVUnitTests | cat)

sdist:
	cabal sdist

clean:
	rm -rf dist
	cabal clean

docs:
	cabal haddock --hyperlink-source

configure:
	cabal configure

release: tags clean all docs

# use this as follows: make gold TGTS="cgUSB5"
# where the tag is one (or many) given in the SBVUnitTest.hs file
# if TGTS is not specified, then all gold files are regenerated
gold:
	ghc -idist/build/autogen/ SBVUnitTest/SBVUnitTest.hs -e "createGolds \"${TGTS}\""

tags:
	find . -name \*.\*hs | xargs hasktags -c
	sort -o tags tags
