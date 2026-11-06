.PHONY: all clean

# A sample is a body of third-party code verified in place: larger than an example, kept
# with its upstream directory layout and licence, and gated by `make test` all the same.
# Each sample directory has its own Makefile that runs its harnesses.
SAMPLES := $(shell find . -mindepth 1 -maxdepth 1 -type d \
	! -name '_*' ! -name '.*' | sort | sed 's|^\./||')

all: $(SAMPLES)

.PHONY: $(SAMPLES)
$(SAMPLES):
	@$(MAKE) -C $@

clean:
	@for d in $(SAMPLES); do $(MAKE) -C $$d clean; done
