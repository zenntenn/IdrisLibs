SHELL := /bin/bash

IDRIS = idris
IDRIS_STD_FLAGS = +RTS -K32000000 -RTS -p contrib -p effects -V
IDRIS_PATH_FLAGS = -i .. -i ../.. --sourcepath .. --sourcepath ../..

basic_operations: basic_operations.lidr 
	${IDRIS} ${IDRIS_STD_FLAGS} ${IDRIS_PATH_FLAGS} basic_operations.lidr -o basic_operations.exe

clean:
	-find . -name '*.ibc' -delete
	-find . -name '*.exe' -delete
	-find . -name '*~' -delete
