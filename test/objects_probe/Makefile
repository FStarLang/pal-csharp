# Scheme-adequacy probe for the object system (doc/translation.md §3.4, §4.5).
#
# `Counter.cs` is the source; the .fst files were produced by hand-executing the
# scheme on it, rule by rule, before any emitter code was written. The target
# checks both halves: the C# is valid C#, and the derived Pulse verifies.
#
# This directory is the reference the class emitter is written against. When it
# and the emitted output of `test/counter` disagree, one of them is wrong and the
# scheme in doc/translation.md decides which.

.PHONY: all cs pulse clean

FSTAR_EXE ?= ../../tools/run-fstar.sh
CACHE_DIR ?= _cache
PULSE_DIR ?= ../../pulse

FSTAR_OPTIONS := --cache_checked_modules --cache_dir $(CACHE_DIR) \
                 --already_cached 'Prims,FStar,Pulse,Pulse.Main,Pulse.Nolib,Pulse.Class,Pulse.Lib,PulseCore' \
                 --include $(CACHE_DIR) \
                 --include $(PULSE_DIR) --include $(PULSE_DIR)/$(CACHE_DIR)

METHODS := Func_Counter__ctor Func_Counter_Increment Func_Counter_Get

all: cs pulse

cs:
	@dotnet build -v q --nologo Probe.csproj

pulse: $(addprefix $(CACHE_DIR)/,$(addsuffix .fst.checked,$(METHODS)))

$(CACHE_DIR)/Class_Counter.fst.checked: Class_Counter.fst
	@mkdir -p $(CACHE_DIR)
	$(FSTAR_EXE) $(FSTAR_OPTIONS) $<

$(CACHE_DIR)/%.fst.checked: %.fst $(CACHE_DIR)/Class_Counter.fst.checked
	$(FSTAR_EXE) $(FSTAR_OPTIONS) $<

clean:
	rm -rf $(CACHE_DIR) bin obj
