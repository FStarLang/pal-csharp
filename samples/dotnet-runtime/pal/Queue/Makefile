# Verify dotnet/runtime's Queue<T> with pal-csharp (sample; see ../../README.md).
CORELIB  := ../../src/libraries/System.Private.CoreLib/src/System/Collections/Generic
COMMON   := ../../src/libraries/Common/src/System/Collections/Generic
# Queue's own ThrowHelper stands in for ../common's: it needs exception resources the
# shared stub does not declare.
SOURCES  := $(CORELIB)/Queue.cs $(CORELIB)/QueueDebugView.cs $(COMMON)/EnumerableHelpers.cs \
            $(filter-out ../common/ThrowHelper.cs,$(wildcard ../common/*.cs)) $(wildcard *.cs)

# The stock-compiler check (`cs`) is the runtime's own build: Queue.cs compiled
# standalone would collide with the BCL's Queue<T>. The harness only translates and verifies.
default: verify

include ../../../../test/verify.mk
