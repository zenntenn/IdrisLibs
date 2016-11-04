SHELL := /bin/bash

IDRIS = idris
IDRISFLAGS = +RTS -K32000000 -RTS -p contrib -p effects -V
#IDRISFLAGS = +RTS -K32000000 -RTS -p contrib -V

libs:
	find . \
  -not \( -path "./examples" -prune \) \
  -not \( -path "./papers" -prune \) \
  -not \( -path "./tmp" -prune \) \
  -not \( -path "./GenericSimpleProb" -prune \) \
  -not \( -path "./SequentialDecisionProblems" -prune \) \
  -not \( -path "./*/tests" -prune \) \
  -not \( -path "./*/open_issues" -prune \) \
  -name '*.lidr' | xargs -n 1 ${IDRIS} ${IDRISFLAGS} --check

clean:
	-find . -name '*.ibc' -delete
	-find . -name '*~' -delete
