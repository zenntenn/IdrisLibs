SHELL := /bin/bash

IDRIS = idris
IDRISFLAGS = -p contrib -p effects -V --allow-capitalized-pattern-variables -O2
# IDRISFLAGS = +RTS -K32000000 -RTS -p contrib -V --allow-capitalized-pattern-variables

tictactoe: SeqGamesTychonoffDoubleNegShift.lidr Makefile
	${IDRIS} ${IDRISFLAGS} SeqGamesTychonoffDoubleNegShift.lidr -o tictactoe

clean:
	rm -f tictactoe
	-find . -name '*.ibc' -delete
	-find . -name '*~' -delete
