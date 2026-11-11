# Verify dotnet/runtime's SortedSet<T> with pal-csharp (sample; see ../../README.md).
GENERIC  := ../../src/libraries/System.Collections/src/System/Collections/Generic
SOURCES  := $(GENERIC)/SortedSet.cs $(GENERIC)/SortedSet.TreeSubSet.cs $(GENERIC)/SortedSetEqualityComparer.cs $(GENERIC)/SortedDictionary.cs ../common/GlobalUsings.cs ../common/Scope.cs $(wildcard *.cs)

PAL_CS_FLAGS := --preview --unsafe
# List, Queue and Stack are units of their own (doc/translation.md §36): referenced, not
# translated again.
REFERENCES   := ../List ../Queue ../Stack

default: verify

include ../../../../test/verify.mk
