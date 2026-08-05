.PHONY: all clean

# An example is an acceptance test in every mechanical respect — same harness, same two
# obligations (the C# builds with the stock compiler; the generated Pulse verifies), same
# lints. What separates it from `test/` is provenance: an example is code that was written
# for some purpose other than being verified, ported here with its adaptations documented,
# whereas a test is written to exercise a numbered rule.
#
# They are built by the same rule and gated by the same `make test`, because an example
# that is allowed to rot is worse than no example: it is a claim about the tool that
# stopped being true without anyone noticing.
EXAMPLES := $(shell find . -mindepth 1 -maxdepth 1 -type d \
	! -name '_*' ! -name '.*' | sort | sed 's|^\./||')

all: $(EXAMPLES)

.PHONY: $(EXAMPLES)
$(EXAMPLES):
	@$(MAKE) -C $@

clean:
	@for d in $(EXAMPLES); do $(MAKE) -C $$d clean; done
