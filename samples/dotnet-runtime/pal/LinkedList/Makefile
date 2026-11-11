# Verify dotnet/runtime's LinkedList<T> in place with pal-csharp.
# LinkedList<T>'s nodes are owned as one region (doc/translation.md §27, §31 in pal-csharp);
# §31 lists what is verified and what is not.
GENERIC  := ../../src/libraries/System.Collections/src/System/Collections/Generic
CORELIB  := ../../src/libraries/System.Private.CoreLib/src/System/Collections/Generic
SOURCES  := $(GENERIC)/LinkedList.cs ../common/GlobalUsings.cs ../common/Scope.cs $(wildcard *.cs)
REFERENCES := ../common

PAL_CS_FLAGS := --preview --unsafe

default: verify

include ../../../../test/verify.mk
