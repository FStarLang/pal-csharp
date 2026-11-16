# Verify dotnet/runtime's Dictionary<TKey,TValue> with pal-csharp (sample; see ../../README.md).
CORELIB  := ../../src/libraries/System.Private.CoreLib/src/System/Collections
SOURCES  := $(CORELIB)/Generic/Dictionary.cs $(CORELIB)/Generic/InsertionBehavior.cs \
            ../common/GlobalUsings.cs ../common/Scope.cs $(wildcard *.cs)
REFERENCES := ../HashCommon

PAL_CS_FLAGS := --unsafe

default: verify

include ../../../../test/verify.mk
