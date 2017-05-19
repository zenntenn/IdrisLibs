SHELL := /bin/bash

IDRIS = idris
IDRISFLAGS = -O3 --warnreach \
             -i .. -i ../.. --sourcepath .. --sourcepath ../.. \
             +RTS -K32000000 -RTS \
             -p contrib -p effects \
             -V

run_time_complexity: run_time_complexity.lidr
	${IDRIS} ${IDRISFLAGS} run_time_complexity.lidr -o run_time_complexity

do_complexity: do_complexity.lidr
	${IDRIS} ${IDRISFLAGS} do_complexity.lidr -o do_complexity

error_in_C_tmp_file: error_in_C_tmp_file.lidr
	${IDRIS} ${IDRISFLAGS} error_in_C_tmp_file.lidr -o error_in_C_tmp_file

clean:
	rm -f run_time_complexity
	rm -f do_complexity
	rm -f error_in_C_tmp_file
	-find . -name '*.ibc' -delete
	-find . -name '*~' -delete
