.PHONY: all tools build lib test clean

FSTAR_EXE ?= tools/run-fstar.sh

all: build lib

# Install the pinned F*/Pulse toolchain into tools/fstar.
tools: tools/fstar/bin/fstar.exe

tools/fstar/bin/fstar.exe: tools/fstar-version.txt tools/install-fstar.sh
	./tools/install-fstar.sh

# Build the .NET translator.
build:
	dotnet build Pal.sln

# Build the Pulse support library.
lib: tools
	$(MAKE) -C pulse

test: tools build lib
	$(MAKE) -C test

clean:
	$(MAKE) -C test clean
	$(MAKE) -C pulse clean
	dotnet clean Pal.sln 2>/dev/null || true
