# Verify dotnet/runtime's OrderedDictionary<TKey,TValue> in place with pal-csharp.
# doc/translation.md §33 in pal-csharp lists what is verified and what is trusted.
COLL     := ../../src/libraries/System.Collections/src/System/Collections
# A unit of its own, referencing none: it compiles System.Collections' real ThrowHelper,
# whose members are named as ../common's stand-ins are (R36.4), and a HashHelpers model of
# its own in place of ../HashCommon's (see ../../README.md). The files of ../common it
# lists declare nothing that is translated.
SOURCES  := $(COLL)/Generic/OrderedDictionary.cs $(COLL)/Generic/OrderedDictionaryDebugView.cs \
            $(COLL)/ThrowHelper.cs \
            ../common/GlobalUsings.cs ../common/Scope.cs ../common/Internals.cs ../common/Bindings.cs \
            ../HashCommon/Bindings.cs $(wildcard *.cs)

PAL_CS_FLAGS := --preview --unsafe

default: verify

include ../../../../test/verify.mk
