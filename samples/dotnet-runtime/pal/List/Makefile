# Verify dotnet/runtime's List<T> with pal-csharp (sample; see ../../README.md).
CORELIB  := ../../src/libraries/System.Private.CoreLib/src/System/Collections/Generic
SOURCES  := $(CORELIB)/List.cs $(wildcard ../common/*.cs) $(wildcard *.cs)

# The stock-compiler check (`cs`) is the runtime's own build: List.cs compiled
# standalone would collide with the BCL's List<T>. The harness only translates and verifies.
default: verify

include ../../../../test/verify.mk
