# Verify dotnet/runtime's SortedList<TKey,TValue> with pal-csharp (sample; see ../../README.md).
GENERIC  := ../../src/libraries/System.Collections/src/System/Collections/Generic
SOURCES  := $(GENERIC)/SortedList.cs $(wildcard ../common/*.cs) $(wildcard *.cs)

default: verify

include ../../../../test/verify.mk
