# Verify dotnet/runtime's HashSet<T> with pal-csharp (sample; see ../../README.md).
CORELIB  := ../../src/libraries/System.Private.CoreLib/src/System/Collections
SOURCES  := $(CORELIB)/Generic/HashSet.cs $(CORELIB)/Generic/HashSetEqualityComparer.cs \
            ../common/GlobalUsings.cs ../common/Scope.cs $(wildcard *.cs)
REFERENCES := ../HashCommon

# The stock-compiler check (`cs`) is the runtime's own build; the harness only translates
# and verifies.
PAL_CS_FLAGS := --unsafe

default: verify

include ../../../../test/verify.mk
