SHELL := /bin/bash

IDRIS = idris
IDRISFLAGS = -i .. -i ../.. --sourcepath .. --sourcepath ../.. \
             +RTS -K64000000 -RTS \
             -p contrib -p effects \
             -V
# -O3 --warnreach

run_time_complexity: run_time_complexity.lidr
	${IDRIS} ${IDRISFLAGS} run_time_complexity.lidr -o run_time_complexity

do_complexity: do_complexity.lidr
	${IDRIS} ${IDRISFLAGS} do_complexity.lidr -o do_complexity

where_complexity: where_complexity.lidr
	${IDRIS} ${IDRISFLAGS} where_complexity.lidr -o where_complexity

error_in_C_tmp_file: error_in_C_tmp_file.lidr
	${IDRIS} ${IDRISFLAGS} error_in_C_tmp_file.lidr -o error_in_C_tmp_file

clean:
	rm -f run_time_complexity
	rm -f do_complexity
	rm -f where_complexity
	rm -f error_in_C_tmp_file
	-find . -name '*.ibc' -delete
	-find . -name '*~' -delete
