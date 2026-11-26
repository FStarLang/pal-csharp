.PHONY: all clean

FSTAR_EXE ?= ../../tools/run-fstar.sh
CACHE_DIR ?= _cache
FSTAR_OPTIONS := --cache_checked_modules --cache_dir $(CACHE_DIR) \
	--already_cached 'Prims,FStar,Pulse,Pulse.Main,Pulse.Nolib,Pulse.Class,Pulse.Lib,PulseCore' \
	--include $(CACHE_DIR) --include ../../pulse --include ../../pulse/_cache

all:
	@mkdir -p $(CACHE_DIR)
	$(FSTAR_EXE) $(FSTAR_OPTIONS) --force --z3refresh --z3rlimit 10 EnumerableSource.fst

clean:
	rm -rf $(CACHE_DIR)
