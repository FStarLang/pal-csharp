# Verify dotnet/runtime's Stack<T> with pal-csharp (sample; see ../../README.md).
COLL     := ../../src/libraries/System.Collections/src/System/Collections/Generic
COMMON   := ../../src/libraries/Common/src/System/Collections/Generic
SOURCES  := $(COLL)/Stack.cs $(COLL)/StackDebugView.cs $(COMMON)/EnumerableHelpers.cs \
            $(wildcard ../common/*.cs) $(wildcard *.cs)

# The stock-compiler check (`cs`) is the runtime's own build: Stack.cs compiled
# standalone would collide with the BCL's Stack<T>. The harness only translates and verifies.
default: verify

include ../../../../test/verify.mk
