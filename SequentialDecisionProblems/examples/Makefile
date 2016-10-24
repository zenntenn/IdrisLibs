SHELL := /bin/bash

IDRIS = idris
IDRISFLAGS = +RTS -K32000000 -RTS -p contrib -p effects -V

example1: 
	${IDRIS} ${IDRISFLAGS} Example1.lidr -o example1

example2: 
	${IDRIS} ${IDRISFLAGS} Example2.lidr -o example2

example3: 
	${IDRIS} ${IDRISFLAGS} Example3.lidr -o example3

clean:
	-find . -name '*.ibc' -delete
	-find . -name '*~' -delete
