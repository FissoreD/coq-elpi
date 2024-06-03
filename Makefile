all:
	@dune build
.PHONY: all

build-core:
	@dune build theories
.PHONY: build-core

build-apps:
	@dune build $$(find apps -type d -name theories)
.PHONY: build-apps

build:
	@dune build @install
.PHONY: build

test-core:
	@dune runtest tests
.PHONY: test-core

test-apps:
	@dune build $$(find apps -type d -name tests)
.PHONY: test-apps

test:
	@dune runtest
	@dune build $$(find apps -type d -name tests)
.PHONY: test

examples:
	@dune build examples
.PHONY: examples

doc: build-core
	@echo "########################## generating doc ##########################"
	@mkdir -p doc
	@$(foreach tut,$(wildcard examples/tutorial*$(ONLY)*.v),\
		echo ALECTRYON $(tut) && OCAMLPATH=$(shell pwd)/_build/install/default/lib ./etc/alectryon_elpi.py \
		    --frontend coq+rst \
			--output-directory doc \
		    --pygments-style vs \
			-R $(shell pwd)/_build/install/default/lib/coq/user-contrib/elpi elpi \
			$(tut) &&) true
	@cp stlc.html doc/
	@cp etc/tracer.png doc/

clean:
	@dune clean
.PHONY: clean

install:
	@dune build -p coq-elpi
	@dune install coq-elpi
.PHONY: install

nix:
	nix-shell --arg do-nothing true --run "updateNixToolBox & genNixActions"
.PHONY: nix
