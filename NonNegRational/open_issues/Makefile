SHELL := /bin/bash

IDRIS = idris
IDRIS_STD_FLAGS = +RTS -K32000000 -RTS -p contrib -p effects -V
IDRIS_PATH_FLAGS = -i .. -i ../.. --sourcepath .. --sourcepath ../..

rt_vs_tct_costs: rt_vs_tct_costs.lidr 
	${IDRIS} ${IDRIS_STD_FLAGS} ${IDRIS_PATH_FLAGS} rt_vs_tct_costs.lidr -o rt_vs_tct_costs.exe

clean:
	-find . -name '*.ibc' -delete
	-find . -name '*.exe' -delete
	-find . -name '*~' -delete
