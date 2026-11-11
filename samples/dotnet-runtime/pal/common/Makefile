# The unit every collection harness references (see ../../README.md): the stand-ins for
# CoreLib's ThrowHelper, resource strings and internals, and the Common helpers more than
# one collection calls, translated and verified here once.
#
# GlobalUsings.cs and Scope.cs are a compilation's settings, not declarations: every unit
# lists them among its own sources.
COMMON   := ../../src/libraries/Common/src/System/Collections/Generic
SOURCES  := $(COMMON)/EnumerableHelpers.cs $(COMMON)/BitHelper.cs $(wildcard *.cs)

PAL_CS_FLAGS := --preview --unsafe

default: verify

include ../../../../test/verify.mk
