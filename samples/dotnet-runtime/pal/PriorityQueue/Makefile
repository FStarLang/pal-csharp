# Verify dotnet/runtime's PriorityQueue<TElement, TPriority> with pal-csharp (sample; see ../../README.md).
GENERIC  := ../../src/libraries/System.Collections/src/System/Collections/Generic
# HashCommon's bindings, and not the unit: PriorityQueue calls no HashHelpers.
SOURCES  := $(GENERIC)/PriorityQueue.cs ../common/GlobalUsings.cs ../common/Scope.cs ../HashCommon/Bindings.cs $(wildcard *.cs)
REFERENCES := ../common

# The stock-compiler check (`cs`) is the runtime's own build. The harness only
# translates and verifies.
PAL_CS_FLAGS := --preview

default: verify

include ../../../../test/verify.mk
