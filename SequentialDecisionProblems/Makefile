SHELL := /bin/bash

IDRIS = idris
IDRISFLAGS = -i .. -i ../.. --sourcepath .. --sourcepath ../.. +RTS -K32000000 -RTS -p contrib -p effects -V

libs:
	find . \
  -not \( -path "./applications" -prune \) \
  -not \( -path "./examples" -prune \) \
  -not \( -path "./tests" -prune \) \
  -name '*.lidr' | xargs -n 1 ${IDRIS} ${IDRISFLAGS} --check

clean:
	-find . -name '*.ibc' -delete
	-find . -name '*~' -delete
