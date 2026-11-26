include ../verify.mk

.PHONY: fresh runtime negative
fresh: translate
	@python3 checks.py positive

runtime: cs
	dotnet run --project runtime/Runtime.csproj -p:UseSharedCompilation=false

negative: translate
	@python3 checks.py negative
