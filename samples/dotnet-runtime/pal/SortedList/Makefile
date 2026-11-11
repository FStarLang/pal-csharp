# Verify dotnet/runtime's SortedList<TKey,TValue> with pal-csharp (sample; see ../../README.md).
GENERIC  := ../../src/libraries/System.Collections/src/System/Collections/Generic
SOURCES  := $(GENERIC)/SortedList.cs ../common/GlobalUsings.cs ../common/Scope.cs $(wildcard *.cs)
REFERENCES := ../common

default: verify

include ../../../../test/verify.mk
