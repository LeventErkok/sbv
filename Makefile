# (c) Copyright Levent Erkok. All rights reserved.
#
# The sbv library is distributed with the BSD3 license. See the LICENSE file
# in the distribution for details.

OS := $(shell uname)

SHELL   := /usr/bin/env bash

ifeq ($(OS), Darwin)
# OSX tends to sleep for long jobs; so run through caffeinate
TIME = /usr/bin/time caffeinate
NO_OF_CORES = `sysctl hw.ncpu | awk '{print $$2}'`
else
TIME = /usr/bin/time
NO_OF_CORES = `grep -c "^processor" /proc/cpuinfo`
endif

BUILDTIMES = buildTimes.log

.PHONY: quick install tests limitedTests test limitedTest gold testPattern doctest sdist
.PHONY: veryclean clean docs markBuildStart markBuildEnd release limitedRelease hlint uploadDocs checkLinks testInterfaces
.PHONY: limitedTestInterfaces tags

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

all: install

install: 
	$(call startTimer,$@)
	@fast-tags -R --nomerge .
	@cabal configure --enable-tests --ghc-options="-Werror -Wall"
	@cabal build
	@cabal install --force-reinstalls
	$(call endTimer,$@)

quick:
	$(call startTimer,$@)
	@fast-tags -R --nomerge .
	@cabal build --ghc-options="-Werror -Wall"
	@cabal install
	$(call endTimer,$@)

tests:
	$(call startTimer,$@)
	@$(TIME) ./dist/build/SBVTestSuite/SBVTestSuite --hide-successes -p '**' -j $(NO_OF_CORES)
	$(call endTimer,$@)

# When "limited", we skip query tests
limitedTests:
	$(call startTimer,$@)
	@$(TIME) ./dist/build/SBVTestSuite/SBVTestSuite --hide-successes -p \!extOnly -j $(NO_OF_CORES)
	$(call endTimer,$@)

test: install tests doctest

limitedTest: install limitedTests doctest

# use this as follows:
#         make testPattern TGT="U2Bridge"
testPattern:
	./dist/build/SBVTestSuite/SBVTestSuite -p ${TGT}

doctest:
	$(call startTimer,$@)
	@echo "*** Starting inline tests.."
	@$(TIME) cabal test doctest
	$(call endTimer,$@)

sdist: install
	$(call startTimer,$@)
	cabal sdist
	$(call endTimer,$@)

veryclean: clean
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

release: markBuildStart veryclean install sdist testInterfaces docs test checkLinks hlint markBuildEnd
	@echo "*** SBV is ready for release!"

# same as release really, but doesn't check links and tests fewer solver connections.
# suitable to use when we're in more poverished environment.
limitedRelease: clean install sdist limitedTestInterfaces docs limitedTest hlint
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
	make -C buildUtils veryClean
	make -C buildUtils
	@buildUtils/testInterfaces
	$(call endTimer,$@)

# only test connection to a few solvers
limitedTestInterfaces:
	$(call startTimer,$@)
	make -C buildUtils veryClean
	make -C buildUtils
	@buildUtils/testInterfaces Yices Z3
	$(call startTimer,$@)

tags:
	@fast-tags -R --nomerge .
