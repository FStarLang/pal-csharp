# Library-adequacy probe (plan §7.2).
#
# `InsertionSort.cs` is the source; the .fst files were produced by hand-executing
# doc/translation.md on it. The target checks both halves: the C# is valid C#,
# and the derived Pulse verifies against Pulse.Lib.CSharp.*.

.PHONY: all cs pulse clean

FSTAR_EXE ?= ../../tools/run-fstar.sh
CACHE_DIR ?= _cache
PULSE_DIR ?= ../../pulse

FSTAR_OPTIONS := --cache_checked_modules --cache_dir $(CACHE_DIR) \
                 --already_cached 'Prims,FStar,Pulse,Pulse.Main,Pulse.Nolib,Pulse.Class,Pulse.Lib,PulseCore' \
                 --include $(CACHE_DIR) \
                 --include $(PULSE_DIR) --include $(PULSE_DIR)/$(CACHE_DIR)

all: cs pulse

cs:
	@dotnet build -v q --nologo Probe.csproj

pulse: $(CACHE_DIR)/Func_InsertionSort.fst.checked

$(CACHE_DIR)/Let_Sorted.fst.checked: Let_Sorted.fst
	@mkdir -p $(CACHE_DIR)
	$(FSTAR_EXE) $(FSTAR_OPTIONS) $<

$(CACHE_DIR)/Func_InsertionSort.fst.checked: Func_InsertionSort.fst $(CACHE_DIR)/Let_Sorted.fst.checked
	$(FSTAR_EXE) $(FSTAR_OPTIONS) $<

clean:
	rm -rf $(CACHE_DIR) bin obj
