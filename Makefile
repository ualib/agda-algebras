# This file is essentially a copy of the Makefile in the agda-categories library by Jacques Carette.
# The only difference is that this version works with .lagda files instead of .agda files.
# The original Makefile from agda-categories is https://github.com/agda/agda-categories/blob/master/Makefile

.PHONY: test Everything.agda clean

OTHEROPTS=

RTSARGS = +RTS -M6G -A128M ${OTHEROPTS} -RTS

test: Everything.agda
	agda ${RTSARGS} -i. Everything.agda

html: Everything.agda
	agda ${RTSARGS} --html --html-dir=./docs -i. Everything.agda
	cp ./docs/agda-algebras.html ./docs/index.html

Everything.agda:
	git ls-tree --full-tree -r --name-only HEAD | grep '^src/[^\.]*.lagda' | sed -e 's|^src/[/]*|import |' -e 's|/|.|g' -e 's/.lagda//' -e '/import Everything/d' | LC_COLLATE='C' sort > Everything.agda

clean:
	find . -name '*.agdai' -exec rm \{\} \;

profile: Everything.agda
	agda ${RTSARGS} -v profile:7 -v profile.definitions:15 -i. Everything.agda
