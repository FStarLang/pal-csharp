# Verify dotnet/runtime's PriorityQueue<TElement, TPriority> with pal-csharp (sample; see ../../README.md).
GENERIC  := ../../src/libraries/System.Collections/src/System/Collections/Generic
SOURCES  := $(GENERIC)/PriorityQueue.cs ../../src/libraries/Common/src/System/Collections/Generic/EnumerableHelpers.cs $(wildcard ../common/*.cs) ../HashCommon/Bindings.cs $(wildcard *.cs)

# The stock-compiler check (`cs`) is the runtime's own build. The harness only
# translates and verifies.
PAL_CS_FLAGS := --preview

default: verify

include ../../../../test/verify.mk
