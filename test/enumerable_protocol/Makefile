include ../verify.mk

.PHONY: fresh negative runtime
fresh:
	@python3 checks.py positive
negative:
	@python3 checks.py negative
runtime: cs
	dotnet run --project runtime/Runtime.csproj -p:UseSharedCompilation=false
