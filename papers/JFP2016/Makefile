SHELL := /bin/bash

IDRIS = idris
IDRISFLAGS = -i .. -i ../.. -i ../../.. \
             --sourcepath .. --sourcepath ../.. --sourcepath ../../.. \
             +RTS -K32000000 -RTS -p contrib -p effects -V

all:
	find . -name '*.lidr' | xargs -n 1 ${IDRIS} ${IDRISFLAGS} --check

clean:
	-find . -name '*.ibc' -delete
	-find . -name '*~' -delete
