.PHONY: all clean

TESTS := $(shell find . -mindepth 1 -maxdepth 1 -type d \
	! -name '_*' ! -name '.*' | sort | sed 's|^\./||')

all: $(TESTS) lint

# The §7.2 mechanical detectors of emitter contortion. They run after the tests because
# the provenance lint reads what the emitter actually produced. `fst-configs.sh --check`
# is here for a different reason: an IDE config that disagrees with the build about
# include paths is worse than no config at all, so it must not be able to drift.
.PHONY: lint
lint: $(TESTS)
	@bash no-example-names.sh
	@bash provenance-lint.sh
	@bash fst-configs.sh --check

# Rewrite the .fst.config.json files after adding or removing a test directory.
.PHONY: configs
configs:
	@bash fst-configs.sh

.PHONY: $(TESTS)
$(TESTS):
	@$(MAKE) -C $@

clean:
	@for d in $(TESTS); do $(MAKE) -C $$d clean; done
