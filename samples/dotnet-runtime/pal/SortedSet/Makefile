# Verify dotnet/runtime's SortedSet<T> with pal-csharp (sample; see ../../README.md).
GENERIC  := ../../src/libraries/System.Collections/src/System/Collections/Generic
SOURCES  := $(GENERIC)/SortedSet.cs $(GENERIC)/SortedSet.TreeSubSet.cs $(GENERIC)/SortedSetEqualityComparer.cs $(GENERIC)/SortedDictionary.cs ../common/GlobalUsings.cs ../common/Scope.cs $(wildcard *.cs)

PAL_CS_FLAGS := --preview --unsafe
# The stock combined build intentionally shadows BCL collection types and uses
# the local, more complete generated-resource stand-in, not common/SR twice.
# These settings affect only this sample's stock C# project, not proof checking.
export PAL_CS_NOWARN := CS0436
export PAL_CS_UNSAFE := true
export PAL_CS_EXCLUDE := $(abspath ../common/SR.cs)
# List, Queue and Stack are units of their own (doc/translation.md §36): referenced, not
# translated again.
REFERENCES   := ../List ../Queue ../Stack
# The checked branch predicate keeps its representation behind a local F* interface.
export EXTRA_INCLUDES := .

default: verify

include ../../../../test/verify.mk
