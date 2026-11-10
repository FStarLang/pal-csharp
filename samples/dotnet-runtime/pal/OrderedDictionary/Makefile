# Verify dotnet/runtime's OrderedDictionary<TKey,TValue> in place with pal-csharp.
# doc/translation.md §33 in pal-csharp lists what is verified and what is trusted.
COLL     := ../../src/libraries/System.Collections/src/System/Collections
# System.Collections' own ThrowHelper stands in for ../common's (their members collide).
SOURCES  := $(COLL)/Generic/OrderedDictionary.cs $(COLL)/Generic/OrderedDictionaryDebugView.cs \
            $(COLL)/ThrowHelper.cs \
            $(filter-out ../common/ThrowHelper.cs,$(wildcard ../common/*.cs)) ../HashCommon/Bindings.cs $(wildcard *.cs)

PAL_CS_FLAGS := --preview --unsafe

default: verify

include ../../../../test/verify.mk
