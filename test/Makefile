.PHONY: all clean

TESTS := $(shell find . -mindepth 1 -maxdepth 1 -type d \
	! -name '_*' ! -name '.*' | sort | sed 's|^\./||')

all: $(TESTS) lint

# The §7.2 mechanical detectors of emitter contortion. They run after the tests because
# the provenance lint reads what the emitter actually produced.
.PHONY: lint
lint: $(TESTS)
	@bash no-example-names.sh
	@bash provenance-lint.sh

.PHONY: $(TESTS)
$(TESTS):
	@$(MAKE) -C $@

clean:
	@for d in $(TESTS); do $(MAKE) -C $$d clean; done
