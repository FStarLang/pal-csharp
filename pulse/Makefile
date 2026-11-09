# Pulse.Lib.CSharp.* — the pal-csharp Pulse support library.
#
# Modules here are hand-written, idiomatic Pulse. Per the anti-contortion
# discipline (doc/translation.md §0), all proof difficulty that is not supplied
# by the user's C# annotations belongs here as *general-purpose* lemmas —
# never as a special case in the emitter.

.PHONY: all verify clean

all: verify

FSTAR_EXE ?= ../tools/run-fstar.sh
CACHE_DIR ?= _cache

ifneq ($(strip $(ADMIT)),)
$(error ADMIT is not allowed in the support-library gate; use a separate scratch verification)
endif

FSTAR = $(FSTAR_EXE) \
	--cache_checked_modules \
	--cache_dir $(CACHE_DIR) \
	--already_cached 'Prims,FStar,Pulse.Nolib,Pulse.Class,Pulse.Lib,PulseCore' \
	--include $(CACHE_DIR)

FSTAR_FILES := $(wildcard *.fst) $(wildcard *.fsti)

.depend: $(FSTAR_FILES)
	@mkdir -p $(CACHE_DIR)
	$(FSTAR) --dep full $(FSTAR_FILES) --output_deps_to $@

include .depend

$(CACHE_DIR)/%.checked:
	$(FSTAR) $<
	@touch -c $@

verify: $(ALL_CHECKED_FILES)

clean:
	rm -rf $(CACHE_DIR) .depend
