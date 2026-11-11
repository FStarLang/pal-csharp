# Shared harness for a pal-csharp acceptance test (plan §7).
#
# A test directory contains one or more annotated `.cs` files and a Makefile that
# does nothing but `include ../verify.mk`. Two obligations are checked, and both
# must hold:
#
#   cs      the sources compile with the stock C# compiler, so the annotations
#           really are inert — this is the core invariant of the design;
#   verify  `palcs` translates them and F*/Pulse discharges every proof.
#
# Verification runs in two phases because the set of generated modules is not
# known until `palcs` has run: the first phase translates, the second re-enters
# make with the generated file list and an F*-computed dependency order.

# pipefail, so a failed proof stays a failed build when its output is piped.
SHELL      := /bin/bash

PAL_ROOT   := $(abspath $(dir $(lastword $(MAKEFILE_LIST)))/..)
TEST_NAME  := $(notdir $(CURDIR))

FSTAR_EXE  ?= $(PAL_ROOT)/tools/run-fstar.sh
PALCS_DIR  ?= $(PAL_ROOT)/src/Pal.Tool/bin/Debug/net10.0
PALCS      ?= $(PALCS_DIR)/palcs
# Re-translate when the translator changes, not only when the sources do.
PALCS_DEPS := $(wildcard $(PALCS_DIR)/Pal.*.dll)
PULSE_DIR  ?= $(PAL_ROOT)/pulse
OUT        ?= out
CACHE_DIR  ?= _cache

SOURCES    ?= $(sort $(wildcard *.cs))
# More F* include directories: a harness whose contract is an F* development kept beside it.
EXTRA_INCLUDES ?=
# The modules of that development, checked by its own build: used, never re-checked here.
# Comma-separated, as F*'s `--already_cached` takes them.
EXTRA_CACHED ?=
# Harness directories whose translation this one references (R36): their declarations are
# not translated again here, and their modules are used from their own `.checked` files,
# never re-checked. A referenced harness is translated and verified first, by recursion,
# unless REFERENCES_BUILT is set by a caller that has already built it (the samples'
# Makefile, which orders the harnesses itself so that two clients of one unit cannot build
# it at once); then it is only required to be up to date. A referenced harness keeps the
# default OUT and CACHE_DIR.
REFERENCES ?=
REFERENCES_BUILT ?=
comma := ,
REF_GOAL := $(if $(filter translate,$(MAKECMDGOALS)),translate,verify)
REF_MANIFESTS := $(addsuffix /out/unit.json,$(REFERENCES))
# Every unit's TranslationErrors sentinel has the same module name, so each is checked into
# a cache directory of its own that no include path names.
SENTINEL_CACHE := $(CACHE_DIR)/sentinel

# Only in the second phase: the referenced units' manifests exist once the first has run.
ifeq ($(PHASE),verify)
ifneq ($(REFERENCES),)
REF_OUTS   := $(shell python3 $(PAL_ROOT)/test/unit-closure.py --dirs $(addsuffix /out,$(REFERENCES)))
REF_CACHED := $(shell python3 $(PAL_ROOT)/test/unit-closure.py --modules $(addsuffix /out,$(REFERENCES)))
endif
endif

# `--message_format json` so that a failure can be read by `palcs report` and said again
# against the C# it came from. F* still prints nothing else, so a passing run is as quiet
# as it ever was; the pipeline below only has work to do when there is a failure. A
# referenced unit's include directories come first, so that this unit's own win.
FSTAR_OPTIONS := --message_format json \
                 --cache_checked_modules --cache_dir $(CACHE_DIR) \
                 --already_cached 'Prims,FStar,Pulse,Pulse.Main,Pulse.Nolib,Pulse.Class,Pulse.Lib,PulseCore$(if $(EXTRA_CACHED),$(comma)$(EXTRA_CACHED))$(if $(REF_CACHED),$(comma)$(REF_CACHED))' \
                 $(foreach d,$(REF_OUTS),--include $(dir $(d))_cache --include $(d)) \
                 --include $(CACHE_DIR) --include $(OUT) \
                 --include $(PULSE_DIR) --include $(PULSE_DIR)/$(CACHE_DIR) \
                 $(foreach d,$(EXTRA_INCLUDES),--include $(d))

.PHONY: all cs print-sources translate verify _verify references clean

all: cs verify

# ---------------------------------------------------------------------------
# The core invariant: annotated C# is ordinary C#.
# ---------------------------------------------------------------------------

# A unit is a fragment of one assembly's sources (R36.2), so it compiles together with the
# units it references.
cs: $(SOURCES)
	@$(PAL_ROOT)/test/build-cs.sh $(TEST_NAME) $(if $(REFERENCES),\
	    $$($(MAKE) -s --no-print-directory print-sources | tr ' ' '\n' | sort -u),$(SOURCES))

# The sources of this unit and of the units it references, as absolute paths.
print-sources:
	@echo $(abspath $(SOURCES)) $(foreach r,$(REFERENCES),$$($(MAKE) -s --no-print-directory -C $(r) print-sources))

# ---------------------------------------------------------------------------
# Translate, then verify.
# ---------------------------------------------------------------------------

translate: $(OUT)/.stamp

references:
ifneq ($(REFERENCES_BUILT),)
	@$(foreach r,$(REFERENCES),{ s=$(r)/$(if $(filter verify,$(REF_GOAL)),_cache/.verified,out/.stamp); \
	    [ -e $$s ] && [ -z "$$(find $(r)/out -newer $$s -print -quit)" ] || \
	    { echo "$(TEST_NAME): referenced unit $(r) is not up to date"; exit 1; }; } &&) true
else
	@$(foreach r,$(REFERENCES),$(MAKE) --no-print-directory -C $(r) $(REF_GOAL) OUT=out CACHE_DIR=_cache &&) true
endif

ifneq ($(PHASE),verify)
$(REF_MANIFESTS): | references
endif

# An [IncludePulseFile] is copied into $(OUT) by the translation, so it is an input too.
$(OUT)/.stamp: $(SOURCES) $(PALCS) $(PALCS_DEPS) $(wildcard *.fst) $(REF_MANIFESTS)
	@mkdir -p $(OUT)
	$(PALCS) -o $(OUT) $(if $(PAL_CS_NULLABLE),--nullable $(PAL_CS_NULLABLE)) $(PAL_CS_FLAGS) \
	    $(foreach r,$(REFERENCES),--reference $(r)/out) $(SOURCES)
	@touch $@

verify: translate
	@$(MAKE) --no-print-directory -f $(PAL_ROOT)/test/verify.mk PHASE=verify REFERENCES="$(REFERENCES)" _verify

GENERATED := $(sort $(wildcard $(OUT)/*.fst))
MODULES   := $(filter-out $(OUT)/TranslationErrors.fst,$(GENERATED))
CHECKED   := $(patsubst $(OUT)/%.fst,$(CACHE_DIR)/%.fst.checked,$(MODULES))

# `.verified` tells a client that every module here is checked (see REFERENCES_BUILT).
_verify: $(CHECKED) $(if $(filter $(OUT)/TranslationErrors.fst,$(GENERATED)),$(SENTINEL_CACHE)/TranslationErrors.fst.checked)
	@touch $(CACHE_DIR)/.verified

# Only in the second phase: at top level the generated files may be stale, and
# remaking `.depend` from them during parse would fail before `translate` runs.
ifeq ($(PHASE),verify)
ifneq ($(MODULES),)
# F* computes the module dependency order, so a method calling another method
# verifies in the right order without the harness knowing anything about it.
$(CACHE_DIR)/.depend: $(MODULES) $(REF_MANIFESTS)
	@mkdir -p $(CACHE_DIR)
	@$(FSTAR_EXE) $(FSTAR_OPTIONS) --message_format human --dep full $(MODULES) \
	    --output_deps_to $@

include $(CACHE_DIR)/.depend
endif
endif

# F*'s messages go through `palcs report`, which maps each one back to the C# line that
# produced the Pulse it is about. The exit status has to be F*'s, not the reporter's --
# `pipefail` is what keeps a failed proof a failed build. A referenced unit's module is
# never checked here: F* would write it into this harness's cache and check it twice.
%.checked:
	@case "$@" in $(CACHE_DIR)/*) ;; *) echo "$(TEST_NAME): $@ is out of date; verify its unit first"; exit 1;; esac
	@mkdir -p $(CACHE_DIR)
	@echo "$(FSTAR_EXE) $(FSTAR_OPTIONS) $<"
	@set -o pipefail; $(FSTAR_EXE) $(FSTAR_OPTIONS) $< 2>&1 | $(PALCS) report -q -o $(OUT)

$(SENTINEL_CACHE)/TranslationErrors.fst.checked: $(OUT)/TranslationErrors.fst
	@mkdir -p $(SENTINEL_CACHE)
	@set -o pipefail; $(FSTAR_EXE) $(FSTAR_OPTIONS) --cache_dir $(SENTINEL_CACHE) $< 2>&1 | $(PALCS) report -q -o $(OUT)

clean:
	rm -rf $(OUT) $(CACHE_DIR) bin obj
