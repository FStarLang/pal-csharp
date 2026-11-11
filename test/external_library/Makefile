# R21.5a. A library the program calls but does not contain, passed to palcs as metadata.
# The library is built here as a stand-in for a vendor SDK.
export PAL_CS_REFERENCES := ../_external_sdk/bin/AcmeSdk.dll
# The editor builds the SDK through MSBuild rather than relying on the DLL above.
export PAL_CS_PROJECT_REFERENCES := ../_external_sdk/AcmeSdk.csproj

include ../verify.mk

.PHONY: reference-paths
all: reference-paths

reference-paths: $(PAL_CS_REFERENCES)
	@mkdir -p 'obj/reference-paths/dll&dir'
	@cp "$(word 1,$(PAL_CS_REFERENCES))" 'obj/reference-paths/dll&dir/AcmeSdk.dll'
	@cd obj/reference-paths && \
	    PAL_CS_REFERENCES="$(CURDIR)/obj/reference-paths/dll&dir/AcmeSdk.dll" \
	    $(PAL_ROOT)/test/build-cs.sh $(TEST_NAME) $(addprefix ../../,$(SOURCES))

.PHONY: refusals
all: refusals
refusals: $(PAL_CS_REFERENCES) $(PALCS) $(PALCS_DEPS)
	@mkdir -p obj/refusals
	@$(PALCS) -q $(foreach r,$(PAL_CS_REFERENCES),-r $(r)) -o obj/refusals UnboundSpan.cs.in > obj/refusals/log 2>&1; status=$$?; \
	if [ $$status -eq 0 ] || ! grep -q 'error PALCS0590:' obj/refusals/log || \
	   ! grep -q 'assert False' obj/refusals/TranslationErrors.fst; then \
	    cat obj/refusals/log; echo "external_library: an unbound vendor AsSpan must be refused"; exit 1; \
	fi

../_external_sdk/bin/AcmeSdk.dll: ../_external_sdk/AcmeSdk.cs ../_external_sdk/AcmeSdk.csproj
	dotnet build -v q --nologo ../_external_sdk/AcmeSdk.csproj -o ../_external_sdk/bin
