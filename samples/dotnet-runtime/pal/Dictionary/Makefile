# Verify dotnet/runtime's Dictionary<TKey,TValue> with pal-csharp (sample; see ../../README.md).
CORELIB  := ../../src/libraries/System.Private.CoreLib/src/System/Collections
COMMON   := ../../src/libraries/Common/src/System/Collections
SOURCES  := $(CORELIB)/Generic/Dictionary.cs $(CORELIB)/Generic/InsertionBehavior.cs \
            $(CORELIB)/Generic/IInternalStringEqualityComparer.cs \
            $(CORELIB)/HashHelpers.SerializationInfoTable.cs \
            $(COMMON)/HashHelpers.cs \
            $(wildcard ../common/*.cs) $(wildcard ../HashCommon/*.cs) $(wildcard *.cs)

PAL_CS_FLAGS := --unsafe

default: verify

include ../../../../test/verify.mk
