SOURCES := Observations.cs Inherited.cs Helpers.cs Misses.cs SequenceProtocol.cs ClosedViewCall.cs
include ../verify.mk

.PHONY: bridge classifier runtime list-miss iterators actual-iterators guard-dependency
bridge: verify
	$(FSTAR_EXE) $(FSTAR_OPTIONS) $(PAL_ROOT)/pulse/Pulse.Lib.CSharp.Enumerable.Capability.fsti
	$(FSTAR_EXE) $(FSTAR_OPTIONS) $(PAL_ROOT)/pulse/Pulse.Lib.CSharp.Enumerable.Capability.fst
	$(FSTAR_EXE) $(FSTAR_OPTIONS) --include . ObservationBridge.fst
classifier:
	dotnet run --project classifier/Classifier.csproj
runtime:
	dotnet run --project runtime/Runtime.csproj -p:UseSharedCompilation=false
list-miss:
	$(MAKE) -C $(PAL_ROOT)/samples/dotnet-runtime/pal/List translate verify
	$(MAKE) verify SOURCES='Observations.cs ListMiss.cs' \
	  OUT=obj/actual-list/out CACHE_DIR=obj/actual-list/_cache \
	  REFERENCES=$(PAL_ROOT)/samples/dotnet-runtime/pal/List REFERENCES_BUILT=1 \
	  EXTRA_INCLUDES=$(PAL_ROOT)/pulse/_cache

iterators:
	$(MAKE) verify OUT=obj/iterator/out CACHE_DIR=obj/iterator/_cache \
	  EXTRA_INCLUDES=$(PAL_ROOT)/pulse/_cache
	python3 iterator_checks.py

actual-iterators:
	python3 iterator_installation_check.py
	$(MAKE) -C $(PAL_ROOT)/samples/dotnet-runtime/pal/SortedSet PHASE=verify \
	  OUT=obj/iterator-hit/out CACHE_DIR=obj/iterator-hit/_cache REFERENCES_BUILT=1 \
	  'EXTRA_INCLUDES=. $(PAL_ROOT)/pulse/_cache' \
	  obj/iterator-hit/_cache/Func_SortedSetIteratorInstallation_ListFalse.fst.checked \
	  obj/iterator-hit/_cache/Func_SortedSetIteratorInstallation_Ordinary.fst.checked \
	  obj/iterator-hit/_cache/Func_SortedSetIteratorInstallation_View.fst.checked

guard-dependency:
	python3 guard_dependency_check.py
