.PHONY: all tools build lib test examples samples clean

FSTAR_EXE ?= tools/run-fstar.sh

all: build lib

# Install the pinned F*/Pulse toolchain into tools/fstar.
tools: tools/fstar/bin/fstar.exe

tools/fstar/bin/fstar.exe: tools/fstar-version.txt $(wildcard tools/fstar-source.txt) tools/install-fstar.sh
	./tools/install-fstar.sh

# Build the .NET translator.
build:
	dotnet build Pal.slnx

# Build the Pulse support library.
lib: tools
	$(MAKE) -C pulse

# The regression gate: both trees, then the §7.2 lints. `examples` runs first because
# `make -C test` ends in the lint phase, and the provenance lint reads what the emitter
# actually produced — in the examples as well as in the tests. An example that is not
# gated is worse than no example: it is a claim about the tool that stopped being true
# without anyone noticing.
test: tools build lib examples samples
	$(MAKE) -C test

# The examples alone. Same harness and same two obligations as a test; what separates
# them is provenance (see examples/Makefile).
examples: tools build lib
	$(MAKE) -C examples

# Larger bodies of third-party code verified in place, with their upstream layout and
# licence (see samples/*/README.md). Gated by `make test` like the examples.
samples: tools build lib
	$(MAKE) -C samples

clean:
	$(MAKE) -C test clean
	$(MAKE) -C samples clean
	$(MAKE) -C examples clean
	$(MAKE) -C pulse clean
	dotnet clean Pal.slnx 2>/dev/null || true
