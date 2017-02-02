SHELL := /bin/bash

IDRIS = idris
IDRISFLAGS = -i .. -i ../.. --sourcepath .. --sourcepath ../.. +RTS -K32000000 -RTS -p contrib -p effects -V

newcomb: Newcomb.lidr
	${IDRIS} ${IDRISFLAGS} Newcomb.lidr -o newcomb

fastnewcomb: FastNewcomb.lidr
	${IDRIS} ${IDRISFLAGS} FastNewcomb.lidr -o fastnewcomb

emissionsgame0: EmissionsGame0.lidr
	${IDRIS} ${IDRISFLAGS} EmissionsGame0.lidr -o emissionsgame0

emissionsgame1: EmissionsGame1.lidr
	${IDRIS} ${IDRISFLAGS} EmissionsGame1.lidr -o emissionsgame1

clean:
	rm newcomb
	-find . -name '*.ibc' -delete
	-find . -name '*~' -delete
