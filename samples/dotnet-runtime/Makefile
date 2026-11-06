.PHONY: all clean

# One harness per collection under pal/; see README.md.
HARNESSES := $(sort $(patsubst %/Makefile,%,$(wildcard pal/*/Makefile)))

all: $(HARNESSES)

.PHONY: $(HARNESSES)
$(HARNESSES):
	@$(MAKE) -C $@

clean:
	@for d in $(HARNESSES); do $(MAKE) -C $$d clean; done
