include ../verify.mk

.PHONY: execute
all: execute
execute: verify
	$(MAKE) -C ../shape_hierarchy
	bash run.sh
