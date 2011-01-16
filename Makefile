# (c) Copyright Levent Erkok. All rights reserved.
#
# The sbv library is distributed with the BSD3 license. See the LICENSE file
# in the distribution for details.

.PHONY: all install test sdist clean docs gold

all: install test sdist

install:
	cabal install

test:
	cabal test

sdist:
	cabal sdist

clean:
	cabal clean

docs:
	cabal haddock --hyperlink-source

release: clean all docs

gold:
	ghc -idist/build/autogen/ SBVUnitTest/SBVUnitTest.hs -e createGolds
