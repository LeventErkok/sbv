TARGETS=testInterfaces

all: $(TARGETS)

testInterfaces: testInterfaces.hs
	ghc -O2 -Wall -Werror --make $@
	@rm -f *.o *.hi

clean:
	@rm -f *.o *.hi

veryClean:
	@rm -f $(TARGETS)
