.PHONY: all clean

FSTAR_EXE ?= ../../tools/run-fstar.sh
CACHE_DIR ?= _cache

FSTAR_OPTIONS := --cache_checked_modules --cache_dir $(CACHE_DIR) \
                 --already_cached 'Prims,FStar,Pulse.Nolib,Pulse.Class,Pulse.Lib,PulseCore' \
                 --include $(CACHE_DIR)

all: $(CACHE_DIR)/Smoke.fst.checked

$(CACHE_DIR)/Smoke.fst.checked: Smoke.fst
	@mkdir -p $(CACHE_DIR)
	$(FSTAR_EXE) $(FSTAR_OPTIONS) Smoke.fst

clean:
	rm -rf $(CACHE_DIR)
