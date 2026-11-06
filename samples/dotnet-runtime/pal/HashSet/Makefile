# Verify dotnet/runtime's HashSet<T> with pal-csharp (sample; see ../../README.md).
CORELIB  := ../../src/libraries/System.Private.CoreLib/src/System/Collections
COMMON   := ../../src/libraries/Common/src/System/Collections
SOURCES  := $(CORELIB)/Generic/HashSet.cs $(CORELIB)/Generic/HashSetEqualityComparer.cs \
            $(CORELIB)/Generic/IInternalStringEqualityComparer.cs \
            $(CORELIB)/HashHelpers.SerializationInfoTable.cs \
            $(COMMON)/HashHelpers.cs $(COMMON)/Generic/BitHelper.cs \
            $(wildcard ../common/*.cs) $(wildcard ../HashCommon/*.cs) $(wildcard *.cs)

# The stock-compiler check (`cs`) is the runtime's own build; the harness only translates
# and verifies.
PAL_CS_FLAGS := --unsafe

default: verify

include ../../../../test/verify.mk
