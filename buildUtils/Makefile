TARGETS=../.travis.yml ../.appveyor.yml

all: $(TARGETS)

ci: ci.hs
	ghc -O2 -Wall -Werror --make $@
	@rm -f *.o *.hi

genCI: ../.travis.yml ../.appveyor.yml

../.travis.yml: ci
	@./ci travis

../.appveyor.yml: ci
	@./ci appveyor

clean:
	@rm -f *.o *.hi

veryclean:
	@rm -f $(TARGETS)

# This was an experiment to generate a conversion
# bounds table. See http://github.com/LeventErkok/sbv/issues/456
# for details. Currently abandoned because of all the
# corner case issues we could not deal with. Perhaps revisit one day!
generateBounds: generateBounds.hs
	@rm -f *.o *.hi
	ghc -O2 -Wall -Werror --make -threaded $@
	@rm -f *.o *.hi
# 	@echo "*** The following takes about 6 minutes to run, be patient!"
# 	time ./generateBounds +RTS -N4 > ../Data/SBV/Utils/FloatConversionBounds.hs

