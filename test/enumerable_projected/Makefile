include ../verify.mk

all: facts

.PHONY: fresh negative facts runtime
fresh: translate
	@python3 checks.py positive
negative: translate
	@python3 checks.py negative
facts:
	$(FSTAR_EXE) --force --z3refresh --z3rlimit 10 --cache_checked_modules --cache_dir _cache --include _cache --include $(PULSE_DIR) --include $(PULSE_DIR)/_cache --already_cached 'Prims,FStar,Pulse,Pulse.Main,Pulse.Nolib,Pulse.Class,Pulse.Lib,PulseCore' ProjectedFacts.fst
	@python3 checks.py frozen
runtime: cs
	dotnet run --project runtime/Runtime.csproj -p:UseSharedCompilation=false
