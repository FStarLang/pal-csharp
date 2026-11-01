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

# `--message_format json` so that a failure can be read by `palcs report` and said again
# against the C# it came from. F* still prints nothing else, so a passing run is as quiet
# as it ever was; the pipeline below only has work to do when there is a failure.
FSTAR_OPTIONS := --message_format json \
                 --cache_checked_modules --cache_dir $(CACHE_DIR) \
                 --already_cached 'Prims,FStar,Pulse,Pulse.Main,Pulse.Nolib,Pulse.Class,Pulse.Lib,PulseCore' \
                 --include $(CACHE_DIR) --include $(OUT) \
                 --include $(PULSE_DIR) --include $(PULSE_DIR)/$(CACHE_DIR)

.PHONY: all cs translate verify _verify clean

all: cs verify

# ---------------------------------------------------------------------------
# The core invariant: annotated C# is ordinary C#.
# ---------------------------------------------------------------------------

cs: $(SOURCES)
	@$(PAL_ROOT)/test/build-cs.sh $(TEST_NAME) $(SOURCES)

# ---------------------------------------------------------------------------
# Translate, then verify.
# ---------------------------------------------------------------------------

translate: $(OUT)/.stamp

$(OUT)/.stamp: $(SOURCES) $(PALCS) $(PALCS_DEPS)
	@mkdir -p $(OUT)
	$(PALCS) -o $(OUT) $(if $(PAL_CS_NULLABLE),--nullable $(PAL_CS_NULLABLE)) $(SOURCES)
	@touch $@

verify: translate
	@$(MAKE) --no-print-directory -f $(PAL_ROOT)/test/verify.mk PHASE=verify _verify

GENERATED := $(sort $(wildcard $(OUT)/*.fst))
CHECKED   := $(patsubst $(OUT)/%.fst,$(CACHE_DIR)/%.fst.checked,$(GENERATED))

_verify: $(CHECKED)

# Only in the second phase: at top level the generated files may be stale, and
# remaking `.depend` from them during parse would fail before `translate` runs.
ifeq ($(PHASE),verify)
ifneq ($(GENERATED),)
# F* computes the module dependency order, so a method calling another method
# verifies in the right order without the harness knowing anything about it.
$(CACHE_DIR)/.depend: $(GENERATED)
	@mkdir -p $(CACHE_DIR)
	@$(FSTAR_EXE) $(FSTAR_OPTIONS) --message_format human --dep full $(GENERATED) \
	    --output_deps_to $@

include $(CACHE_DIR)/.depend
endif
endif

# F*'s messages go through `palcs report`, which maps each one back to the C# line that
# produced the Pulse it is about. The exit status has to be F*'s, not the reporter's --
# `pipefail` is what keeps a failed proof a failed build.
%.checked:
	@mkdir -p $(CACHE_DIR)
	@echo "$(FSTAR_EXE) $(FSTAR_OPTIONS) $<"
	@set -o pipefail; $(FSTAR_EXE) $(FSTAR_OPTIONS) $< 2>&1 | $(PALCS) report -q -o $(OUT)

clean:
	rm -rf $(OUT) $(CACHE_DIR) bin obj
