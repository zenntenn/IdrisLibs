SHELL := /bin/bash

IDRIS = idris
IDRISFLAGS = +RTS -K32000000 -RTS -p contrib -p effects -V

all:
	find . \
  -not \( -path "./examples" -prune \) \
  -not \( -path "./tmp" -prune \) \
  -not \( -path "./GenericSimpleProb" -prune \) \
  -name '*.lidr' | xargs -n 1 ${IDRIS} ${IDRISFLAGS} --check

clean:
	-find . -name '*.ibc' -delete
	-find . -name '*~' -delete
