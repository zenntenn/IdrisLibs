SHELL := /bin/bash

IDRIS = idris
IDRISFLAGS = -O3 --warnreach \
             -i .. -i ../.. --sourcepath .. --sourcepath ../.. \
             +RTS -K64000000 -RTS \
             -p contrib -p effects \
             --allow-capitalized-pattern-variables \
             -V

all: env newcomb fastnewcomb emissionsgame0 emissionsgame1 emissionsgame2 emissionsgame2.1

env: Env.lidr
	${IDRIS} ${IDRISFLAGS} --check Env.lidr

newcomb: Newcomb.lidr
	${IDRIS} ${IDRISFLAGS} Newcomb.lidr -o newcomb

fastnewcomb: FastNewcomb.lidr
	${IDRIS} ${IDRISFLAGS} FastNewcomb.lidr -o fastnewcomb

emissionsgame0: EmissionsGame0.lidr
	${IDRIS} ${IDRISFLAGS} EmissionsGame0.lidr -o emissionsgame0

emissionsgame1: EmissionsGame1.lidr
	${IDRIS} ${IDRISFLAGS} EmissionsGame1.lidr -o emissionsgame1

emissionsgame2: EmissionsGame2.lidr
	${IDRIS} ${IDRISFLAGS} EmissionsGame2.lidr -o emissionsgame2

emissionsgame2.1: EmissionsGame2.1.lidr
	${IDRIS} ${IDRISFLAGS} EmissionsGame2.1.lidr -o emissionsgame2.1

emissionsgame2fast: EmissionsGame2fast.lidr
	${IDRIS} ${IDRISFLAGS} EmissionsGame2fast.lidr -o emissionsgame2fast

clean:
	rm -f newcomb
	rm -f fastnewcomb
	rm -f emissionsgame0
	rm -f emissionsgame1
	rm -f emissionsgame2
	rm -f emissionsgame2.1
	rm -f emissionsgame2fast
	-find . -name '*.ibc' -delete
	-find . -name '*~' -delete
