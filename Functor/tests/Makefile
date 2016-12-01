SHELL := /bin/bash

IDRIS = idris
IDRIS_STD_FLAGS = +RTS -K32000000 -RTS -p contrib -p effects -V
IDRIS_PATH_FLAGS = -i .. -i ../.. --sourcepath .. --sourcepath ../..

operations: operations.lidr 
	${IDRIS} ${IDRIS_STD_FLAGS} ${IDRIS_PATH_FLAGS} operations.lidr -o operations.exe

clean:
	-find . -name '*.ibc' -delete
	-find . -name '*.exe' -delete
	-find . -name '*~' -delete
