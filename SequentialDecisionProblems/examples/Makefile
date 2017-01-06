SHELL := /bin/bash

IDRIS = idris
IDRISFLAGS = -i .. -i ../.. --sourcepath .. --sourcepath ../.. +RTS -K32000000 -RTS -p contrib -p effects -V

example1: 
	${IDRIS} ${IDRISFLAGS} Example1.lidr -o example1

example1.tab: 
	${IDRIS} ${IDRISFLAGS} Example1.Tab.lidr -o example1.tab

example1.noviabilitydefaults: 
	${IDRIS} ${IDRISFLAGS} Example1.NoViabilityDefaults.lidr -o example1.noviabilitydefaults

example1.noviabilitydefaults.tab: 
	${IDRIS} ${IDRISFLAGS} Example1.NoViabilityDefaults.Tab.lidr -o example1.noviabilitydefaults.tab

example2: 
	${IDRIS} ${IDRISFLAGS} Example2.lidr -o example2

example2.tab: 
	${IDRIS} ${IDRISFLAGS} Example2.Tab.lidr -o example2.tab

example2.noviabilitydefaults: 
	${IDRIS} ${IDRISFLAGS} Example2.NoViabilityDefaults.lidr -o example2.noviabilitydefaults

example2.noviabilitydefaults.tab: 
	${IDRIS} ${IDRISFLAGS} Example2.NoViabilityDefaults.Tab.lidr -o example2.noviabilitydefaults.tab

example3: 
	${IDRIS} ${IDRISFLAGS} Example3.lidr -o example3

example3.tab: 
	${IDRIS} ${IDRISFLAGS} Example3.Tab.lidr -o example3.tab

example3.noviabilitydefaults: 
	${IDRIS} ${IDRISFLAGS} Example3.NoViabilityDefaults.lidr -o example3.noviabilitydefaults

example3.noviabilitydefaults.tab: 
	${IDRIS} ${IDRISFLAGS} Example3.NoViabilityDefaults.Tab.lidr -o example3.noviabilitydefaults.tab

example4: 
	${IDRIS} ${IDRISFLAGS} Example4.lidr -o example4

example4.tab: 
	${IDRIS} ${IDRISFLAGS} Example4.Tab.lidr -o example4.tab

example4.noviabilitydefaults: 
	${IDRIS} ${IDRISFLAGS} Example4.NoViabilityDefaults.lidr -o example4.noviabilitydefaults

example4.noviabilitydefaults.tab: 
	${IDRIS} ${IDRISFLAGS} Example4.NoViabilityDefaults.Tab.lidr -o example4.noviabilitydefaults.tab

example5: 
	${IDRIS} ${IDRISFLAGS} Example5.lidr -o example5

example5.tab: 
	${IDRIS} ${IDRISFLAGS} Example5.Tab.lidr -o example5.tab

example5.noviabilitydefaults: 
	${IDRIS} ${IDRISFLAGS} Example5.NoViabilityDefaults.lidr -o example5.noviabilitydefaults

example5.noviabilitydefaults.tab: 
	${IDRIS} ${IDRISFLAGS} Example5.NoViabilityDefaults.Tab.lidr -o example5.noviabilitydefaults.tab

example6: 
	${IDRIS} ${IDRISFLAGS} Example6.lidr -o example6

example6.tab: 
	${IDRIS} ${IDRISFLAGS} Example6.Tab.lidr -o example6.tab

example7.noviabilitydefaults: 
	${IDRIS} ${IDRISFLAGS} Example7.NoViabilityDefaults.lidr -o example7.noviabilitydefaults

example7.noviabilitydefaults.tab: 
	${IDRIS} ${IDRISFLAGS} Example7.NoViabilityDefaults.Tab.lidr -o example7.noviabilitydefaults.tab

clean:
	rm -f example1 example1.tab example1.noviabilitydefaults example1.noviabilitydefaults.tab
	rm -f example2 example2.tab example2.noviabilitydefaults example2.noviabilitydefaults.tab
	rm -f example3 example3.tab example3.noviabilitydefaults example3.noviabilitydefaults.tab
	rm -f example4 example4.tab example4.noviabilitydefaults example4.noviabilitydefaults.tab
	rm -f example5 example5.tab example5.noviabilitydefaults example5.noviabilitydefaults.tab
	rm -f example6 example6.tab 
	rm -f                       example7.noviabilitydefaults example7.noviabilitydefaults.tab
	-find . -name '*.ibc' -delete
	-find . -name '*~' -delete
