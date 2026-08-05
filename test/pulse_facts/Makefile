.PHONY: all clean

FSTAR_EXE ?= ../../tools/run-fstar.sh
CACHE_DIR ?= _cache

FSTAR_OPTIONS := --cache_checked_modules --cache_dir $(CACHE_DIR) \
                 --already_cached 'Prims,FStar,Pulse.Nolib,Pulse.Class,Pulse.Lib,PulseCore' \
                 --include $(CACHE_DIR)

# ObjectFacts, ShapeHierarchy and DeepHierarchy use the Pulse.Lib.CSharp support
# library (CA.alloc, CA.write), so they need the library on the include path; the
# others do not.
LIB_OPTIONS := --include ../../pulse --include ../../pulse/_cache

all: $(CACHE_DIR)/PulseFacts.fst.checked $(CACHE_DIR)/StructFacts.fst.checked \
     $(CACHE_DIR)/ObjectFacts.fst.checked $(CACHE_DIR)/InheritanceFacts.fst.checked \
     $(CACHE_DIR)/ShapeHierarchy.fst.checked $(CACHE_DIR)/DeepHierarchy.fst.checked \
     $(CACHE_DIR)/RecursiveFacts.fst.checked $(CACHE_DIR)/UserSpecFacts.fst.checked \
     $(CACHE_DIR)/SegmentFacts.fst.checked $(CACHE_DIR)/ConversionFacts.fst.checked

$(CACHE_DIR)/PulseFacts.fst.checked: PulseFacts.fst
	@mkdir -p $(CACHE_DIR)
	$(FSTAR_EXE) $(FSTAR_OPTIONS) PulseFacts.fst

$(CACHE_DIR)/StructFacts.fst.checked: StructFacts.fst
	@mkdir -p $(CACHE_DIR)
	$(FSTAR_EXE) $(FSTAR_OPTIONS) StructFacts.fst

$(CACHE_DIR)/ObjectFacts.fst.checked: ObjectFacts.fst
	@mkdir -p $(CACHE_DIR)
	$(FSTAR_EXE) $(FSTAR_OPTIONS) $(LIB_OPTIONS) ObjectFacts.fst

$(CACHE_DIR)/InheritanceFacts.fst.checked: InheritanceFacts.fst
	@mkdir -p $(CACHE_DIR)
	$(FSTAR_EXE) $(FSTAR_OPTIONS) InheritanceFacts.fst

$(CACHE_DIR)/ShapeHierarchy.fst.checked: ShapeHierarchy.fst
	@mkdir -p $(CACHE_DIR)
	$(FSTAR_EXE) $(FSTAR_OPTIONS) $(LIB_OPTIONS) ShapeHierarchy.fst

$(CACHE_DIR)/DeepHierarchy.fst.checked: DeepHierarchy.fst
	@mkdir -p $(CACHE_DIR)
	$(FSTAR_EXE) $(FSTAR_OPTIONS) $(LIB_OPTIONS) DeepHierarchy.fst

$(CACHE_DIR)/RecursiveFacts.fst.checked: RecursiveFacts.fst
	@mkdir -p $(CACHE_DIR)
	$(FSTAR_EXE) $(FSTAR_OPTIONS) $(LIB_OPTIONS) RecursiveFacts.fst

$(CACHE_DIR)/ConversionFacts.fst.checked: ConversionFacts.fst
	@mkdir -p $(CACHE_DIR)
	$(FSTAR_EXE) $(FSTAR_OPTIONS) $(LIB_OPTIONS) ConversionFacts.fst

$(CACHE_DIR)/SegmentFacts.fst.checked: SegmentFacts.fst
	@mkdir -p $(CACHE_DIR)
	$(FSTAR_EXE) $(FSTAR_OPTIONS) $(LIB_OPTIONS) SegmentFacts.fst

$(CACHE_DIR)/UserSpecFacts.fst.checked: UserSpecFacts.fst
	@mkdir -p $(CACHE_DIR)
	$(FSTAR_EXE) $(FSTAR_OPTIONS) $(LIB_OPTIONS) UserSpecFacts.fst

clean:
	rm -rf $(CACHE_DIR)
