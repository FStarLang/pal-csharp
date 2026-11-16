include ../verify.mk

.PHONY: runtime
all: runtime
runtime: cs
	dotnet run --project TaskRuntime.csproj --no-launch-profile
