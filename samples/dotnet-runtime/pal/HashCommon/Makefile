# The unit Dictionary and HashSet reference (see ../../README.md): CoreLib's HashHelpers and
# the string-comparer and equality stand-ins and bindings of the hashing collections.
CORELIB  := ../../src/libraries/System.Private.CoreLib/src/System/Collections
COMMON   := ../../src/libraries/Common/src/System/Collections
SOURCES  := $(CORELIB)/Generic/IInternalStringEqualityComparer.cs \
            $(CORELIB)/HashHelpers.SerializationInfoTable.cs \
            $(COMMON)/HashHelpers.cs \
            ../common/GlobalUsings.cs ../common/Scope.cs $(wildcard *.cs)

PAL_CS_FLAGS := --unsafe
REFERENCES   := ../common

default: verify

include ../../../../test/verify.mk
