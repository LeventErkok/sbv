TARGETS=testInterfaces simplify

all: $(TARGETS)

testInterfaces: testInterfaces.hs
	ghc -O2 -Wall -Werror --make $@

simplify: simplify.hs
	ghc -O2 -Wall -Werror --make $@

clean:
	@rm -f *.o *.hi

veryClean:
	@rm -f $(TARGETS)
