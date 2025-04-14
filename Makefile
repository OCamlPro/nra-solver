FLAGS?=

# Keep in sync with (package) entries in dune-project
DUNE_PACKAGES=nra_solver

all: build test

setup:
	# Create switch if it does not exist
	if [ ! -d "_opam" ]; then \
		opam switch create . --deps-only --with-test --with-doc --no-switch --yes; \
	fi
	# Make sure .opam file is up-to-date
	dune build $(addsuffix .opam,$(DUNE_PACKAGES))
	# (Re-)install dependencies
	opam install . --deps-only --with-test --with-doc --switch .

dev-setup: setup
	# Useful tools, but not required for the project
	opam install . --deps-only --with-dev-setup

watch:
	dune build $(FLAGS) -w @check

top:
	dune utop

build:
	dune build $(FLAGS)

test:
	dune build $(FLAGS) @runtest

clean:
	dune clean

.PHONY: all setup dev-setup watch top build test clean
