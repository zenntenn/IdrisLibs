SHELL := /bin/bash

IDRIS = idris
IDRISFLAGS = -i .. -i ../.. --sourcepath .. --sourcepath ../.. +RTS -K32000000 -RTS -p contrib -p effects -V

example1: 
	${IDRIS} ${IDRISFLAGS} Example1.lidr -o example1

example1.noviabilitydefaults: 
	${IDRIS} ${IDRISFLAGS} Example1.NoViabilityDefaults.lidr -o example1.noviabilitydefaults

example2: 
	${IDRIS} ${IDRISFLAGS} Example2.lidr -o example2

example2.noviabilitydefaults: 
	${IDRIS} ${IDRISFLAGS} Example2.NoViabilityDefaults.lidr -o example2.noviabilitydefaults

example3: 
	${IDRIS} ${IDRISFLAGS} Example3.lidr -o example3

example3.noviabilitydefaults: 
	${IDRIS} ${IDRISFLAGS} Example3.NoViabilityDefaults.lidr -o example3.noviabilitydefaults

example4: 
	${IDRIS} ${IDRISFLAGS} Example4.lidr -o example4

example4.noviabilitydefaults: 
	${IDRIS} ${IDRISFLAGS} Example4.NoViabilityDefaults.lidr -o example4.noviabilitydefaults

example5: 
	${IDRIS} ${IDRISFLAGS} Example5.lidr -o example5

example5.noviabilitydefaults: 
	${IDRIS} ${IDRISFLAGS} Example5.NoViabilityDefaults.lidr -o example5.noviabilitydefaults

example6: 
	${IDRIS} ${IDRISFLAGS} Example6.lidr -o example6

clean:
	rm -f example1
	rm -f example1.noviabilitydefaults
	rm -f example2
	rm -f example2.noviabilitydefaults
	rm -f example3
	rm -f example3.noviabilitydefaults
	rm -f example4
	rm -f example4.noviabilitydefaults
	rm -f example5
	rm -f example5.noviabilitydefaults
	rm -f example6
	-find . -name '*.ibc' -delete
	-find . -name '*~' -delete
