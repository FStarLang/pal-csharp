# Verify dotnet/runtime's SortedSet<T> with pal-csharp (sample; see ../../README.md).
GENERIC  := ../../src/libraries/System.Collections/src/System/Collections/Generic
CORELIB  := ../../src/libraries/System.Private.CoreLib/src/System/Collections/Generic
SOURCES  := $(GENERIC)/SortedSet.cs $(GENERIC)/Stack.cs $(GENERIC)/StackDebugView.cs $(CORELIB)/List.cs $(CORELIB)/Queue.cs $(CORELIB)/QueueDebugView.cs $(GENERIC)/SortedSet.TreeSubSet.cs $(GENERIC)/SortedSetEqualityComparer.cs $(GENERIC)/SortedDictionary.cs ../../src/libraries/Common/src/System/Collections/Generic/BitHelper.cs ../../src/libraries/Common/src/System/Collections/Generic/EnumerableHelpers.cs $(wildcard ../common/*.cs) $(wildcard *.cs)

PAL_CS_FLAGS := --preview --unsafe

default: verify

include ../../../../test/verify.mk
