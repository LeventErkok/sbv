TARGETS=testInterfaces

all: $(TARGETS)

testInterfaces: testInterfaces.hs
	ghc -O2 -Wall -Werror --make $@
	@rm -f *.o *.hi

generateBounds: generateBounds.hs
	ghc -O2 -Wall -Werror --make -threaded $@
	@rm -f *.o *.hi
	./generateBounds +RTS -N4 > ../Data/SBV/Utils/FloatConversionBounds.hs

clean:
	@rm -f *.o *.hi

veryclean:
	@rm -f $(TARGETS)
