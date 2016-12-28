SHELL := /bin/bash

IDRIS = idris
IDRISFLAGS = -i .. -i ../.. --sourcepath .. --sourcepath ../.. +RTS -K32000000 -RTS -p contrib -p effects -V

example1: 
	${IDRIS} ${IDRISFLAGS} Example1.lidr -o example1

example2: 
	${IDRIS} ${IDRISFLAGS} Example2.lidr -o example2

example3: 
	${IDRIS} ${IDRISFLAGS} Example3.lidr -o example3

example4: 
	${IDRIS} ${IDRISFLAGS} Example4.lidr -o example4

example5: 
	${IDRIS} ${IDRISFLAGS} Example5.lidr -o example5

example6: 
	${IDRIS} ${IDRISFLAGS} Example6.lidr -o example6

clean:
	rm example1 example2 example3 example4 example5
	-find . -name '*.ibc' -delete
	-find . -name '*~' -delete
