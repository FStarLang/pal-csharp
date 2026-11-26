default: check

SOURCES := Evidence.cs
include ../verify.mk

.PHONY: check classifier negative
check: verify classifier negative
	$(FSTAR_EXE) $(FSTAR_OPTIONS) --include . EvidenceTests.fst

classifier:
	$(MAKE) -C ../_default_equality_classifier

negative: verify
	python3 negative.py
