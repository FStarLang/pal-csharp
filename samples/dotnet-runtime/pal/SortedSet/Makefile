# Verify dotnet/runtime's SortedSet<T> with pal-csharp (sample; see ../../README.md).
GENERIC  := ../../src/libraries/System.Collections/src/System/Collections/Generic
SOURCES  := $(GENERIC)/SortedSet.cs $(GENERIC)/SortedSet.TreeSubSet.cs $(GENERIC)/SortedSetEqualityComparer.cs ../../src/libraries/Common/src/System/Collections/Generic/BitHelper.cs $(wildcard ../common/*.cs) $(wildcard *.cs)

PAL_CS_FLAGS := --preview --unsafe

default: verify

include ../../../../test/verify.mk
