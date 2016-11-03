SHELL := /bin/bash

IDRIS = idris
IDRIS_STD_FLAGS = +RTS -K32000000 -RTS -p contrib -p effects -V
IDRIS_PATH_FLAGS = -i .. -i ../.. --sourcepath .. --sourcepath ../..

type_checking_time: type_checking_time.lidr 
	${IDRIS} ${IDRIS_STD_FLAGS} ${IDRIS_PATH_FLAGS} type_checking_time.lidr -o type_checking_time.exe

clean:
	-find . -name '*.ibc' -delete
	-find . -name '*.exe' -delete
	-find . -name '*~' -delete
