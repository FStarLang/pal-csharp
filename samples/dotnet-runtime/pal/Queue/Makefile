# Verify dotnet/runtime's Queue<T> with pal-csharp (sample; see ../../README.md).
CORELIB  := ../../src/libraries/System.Private.CoreLib/src/System/Collections/Generic
SOURCES  := $(CORELIB)/Queue.cs $(CORELIB)/QueueDebugView.cs ../common/GlobalUsings.cs ../common/Scope.cs
REFERENCES := ../common

# The stock-compiler check (`cs`) is the runtime's own build: Queue.cs compiled
# standalone would collide with the BCL's Queue<T>. The harness only translates and verifies.
default: verify

include ../../../../test/verify.mk
