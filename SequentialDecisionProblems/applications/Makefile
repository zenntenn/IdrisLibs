SHELL := /bin/bash

IDRIS = idris
IDRISFLAGS = -i .. -i ../.. --sourcepath .. --sourcepath ../.. +RTS -K32000000 -RTS -p contrib -p effects -V

newcomb: Newcomb.lidr
	${IDRIS} ${IDRISFLAGS} Newcomb.lidr -o newcomb

fastnewcomb: FastNewcomb.lidr
	${IDRIS} ${IDRISFLAGS} FastNewcomb.lidr -o fastnewcomb

clean:
	rm newcomb
	-find . -name '*.ibc' -delete
	-find . -name '*~' -delete
