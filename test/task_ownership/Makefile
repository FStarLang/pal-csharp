include ../verify.mk

.PHONY: runtime
all: runtime
runtime: cs
	flock --close "$(PAL_ROOT)/src/Pal.Annotations/obj/pal-tests.lock" dotnet run --project TaskRuntime.csproj --no-launch-profile
