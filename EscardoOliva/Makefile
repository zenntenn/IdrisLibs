SHELL := /bin/bash

IDRIS = idris
IDRISFLAGS = -O3 --warnreach \
             -i .. -i ../.. --sourcepath .. --sourcepath ../.. \
             -p contrib -p effects -V --allow-capitalized-pattern-variables
# IDRISFLAGS = +RTS -K32000000 -RTS -p contrib -V --allow-capitalized-pattern-variables

tictactoe: TicTacToe.lidr Makefile
	${IDRIS} ${IDRISFLAGS} TicTacToe.lidr -o TicTacToe

clean:
	rm -f tictactoe
	-find . -name '*.ibc' -delete
	-find . -name '*~' -delete
