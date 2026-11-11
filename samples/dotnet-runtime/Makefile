.PHONY: all clean

# One harness per collection under pal/; see README.md.
HARNESSES := $(sort $(patsubst %/Makefile,%,$(wildcard pal/*/Makefile)))

all: $(HARNESSES)

# A harness after the units it references (its REFERENCES), so that each unit is built
# once even when several harnesses reference it; each then only checks that its
# references are up to date (REFERENCES_BUILT).
REFS_OF = $(addprefix pal/,$(notdir $(shell sed -n 's/^REFERENCES *:\?= *//p' $(1)/Makefile)))
$(foreach h,$(HARNESSES),$(eval $(h): $(call REFS_OF,$(h))))

.PHONY: $(HARNESSES)
$(HARNESSES):
	@$(MAKE) -C $@ REFERENCES_BUILT=1

clean:
	@for d in $(HARNESSES); do $(MAKE) -C $$d clean; done
