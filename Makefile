# (c) Copyright Levent Erkok. All rights reserved.
#
# The sbv library is distributed with the BSD3 license. See the LICENSE file
# in the distribution for details.

SRCS = $(shell find . -name '*.hs' -or -name '*.lhs' | grep -v SBVUnitTest/SBVUnitTest.hs)

.PHONY: all install test sdist clean docs gold

all: install test sdist

install:
	cabal install

test:
	@echo "Executing inline tests.."
	@doctest ${SRCS} | grep -v "Could not find documentation" | exit 0
	@echo "Starting external test suite.."
	SBVUnitTests

sdist:
	cabal sdist

clean:
	cabal clean

docs:
	cabal haddock --hyperlink-source

release: clean all docs

gold:
	ghc -idist/build/autogen/ SBVUnitTest/SBVUnitTest.hs -e createGolds
