export IDRIS2 ?= idris2

lib_pkg = pretty-show.ipkg

test_pkg = test.ipkg

.PHONY: all lib install clean clean-install

all: lib docs

clean-install: clean install

lib:
	${IDRIS2} --build ${lib_pkg}

test:
	${IDRIS2} --build ${test_pkg} && build/exec/runTest

install:
	${IDRIS2} --install ${lib_pkg}

clean:
	${IDRIS2} --clean ${lib_pkg}
	${RM} -r build
