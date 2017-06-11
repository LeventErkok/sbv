# (c) Copyright Levent Erkok. All rights reserved.
#
# The sbv library is distributed with the BSD3 license. See the LICENSE file
# in the distribution for details.

OS := $(shell uname)

SHELL   := /usr/bin/env bash
TSTSRCS = $(shell find . -name '*.hs' | grep -v SBVUnitTest | grep -v buildUtils | grep -v sandbox | grep -v GHC/SrcLoc/Compat.hs)

ifeq ($(OS), Darwin)
# OSX tends to sleep for long jobs; so run through caffeinate
TIME = /usr/bin/time caffeinate
else
TIME = /usr/bin/time
endif

BUILDTIMES = buildTimes.log

ifeq (z$(MAKECMDGOALS), zrelease)
define startTimer
	@tput rmam
	@echo [`date +%T`] $(1) >> ${BUILDTIMES}
endef
else
define startTimer
	@tput rmam
endef
endif

define endTimer
	@tput smam
endef

.PHONY: all install test doctest basicTest extendedTests sdist clean docs gold hlint tags checkLinks testInterfaces markBuildStart markBuildEnd  release

all: install

install: 
	$(call startTimer,$@)
	@(make -s -C buildUtils testInterfaces)
	@fast-tags -R --nomerge .
	@cabal configure --enable-tests --ghc-options="-Werror -Wall"
	@cabal build
	@cabal install --force-reinstalls
	$(call endTimer,$@)

basicTest:
	$(call startTimer,$@)
	@SBV_Z3=doesnotexist $(TIME) ./dist/build/SBVBasicTests/SBVBasicTests
	$(call endTimer,$@)

extendedTests:
	$(call startTimer,$@)
	@$(TIME) ./dist/build/int-test-extended/int-test-extended --hide-successes -p '**' -j 4
	$(call endTimer,$@)

test: install doctest basicTest extendedTests


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
	$(call startTimer,$@)
	@echo "*** Starting inline tests.."
	@$(TIME) doctest ${TSTSRCS}
	$(call endTimer,$@)

sdist: install
	$(call startTimer,$@)
	cabal sdist
	$(call endTimer,$@)

veryclean: clean
	@rm -f ${BUILDTIMES}
	@make -C buildUtils clean
	@-ghc-pkg unregister sbv

clean:
	@rm -rf dist

docs:
	$(call startTimer,$@)
	cabal haddock --haddock-option=--hyperlinked-source --haddock-option=--no-warnings
	$(call endTimer,$@)

markBuildStart:
	@echo ===================================================================== >> ${BUILDTIMES}
	@echo `date`. A new release build of SBV is starting.                       >> ${BUILDTIMES}

markBuildEnd:
	@echo `date`. SBV release build finished.		   >> ${BUILDTIMES}

release: markBuildStart clean checkLinks install sdist testInterfaces hlint docs test markBuildEnd
	@echo "*** SBV is ready for release!"

# same as release really, but doesn't check links and tests fewer solver connections.
# suitable to use when we're in more poverished environment.
limitedRelease: clean install sdist limitedTestInterfaces hlint docs test
	@echo "*** SBV is looking OK, but you should really run the 'release' target!"

hlint: 
	$(call startTimer,$@)
	@echo "Running HLint.."
	@hlint Data SBVUnitTest -i "Use otherwise" -i "Parse error" -i "Use fewer imports" -i "Use module export list" -i "Use import/export shortcut"
	$(call endTimer,$@)

uploadDocs:
	@buildUtils/hackage-docs

checkLinks:
	$(call startTimer,$@)
	@buildUtils/checkLinks
	$(call endTimer,$@)

testInterfaces:
	$(call startTimer,$@)
	make -C buildUtils
	@buildUtils/testInterfaces
	$(call endTimer,$@)

# only test connection to a few solvers
limitedTestInterfaces:
	$(call startTimer,$@)
	make -C buildUtils
	@buildUtils/testInterfaces Yices Z3 CVC4
	$(call startTimer,$@)

tags:
	@fast-tags -R --nomerge .
