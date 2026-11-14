include ../verify.mk

.PHONY: runtime check-borrow-fuel check-plain-definite-assignment check-plain-call-emission check-plain-null-safety check-plain-ghost-types check-ghost-results check-immutable-integers
all: runtime check-borrow-fuel check-plain-definite-assignment check-plain-call-emission check-plain-null-safety check-plain-ghost-types check-ghost-results check-immutable-integers check-tuples-and-switch-joins
.PHONY: check-tuples-and-switch-joins
check-tuples-and-switch-joins: verify
	@python3 check_tuples_and_switch_joins.py "$(PALCS)"
.PHONY: check-plain-patterns
all: check-plain-patterns
check-plain-patterns: verify
	@python3 check_plain_patterns.py "$(PALCS)"
.PHONY: check-plain-returns
all: check-plain-returns
check-plain-returns: verify
	@python3 check_plain_returns.py
.PHONY: check-current-models
all: check-current-models
check-current-models: verify
	@python3 check_current_models.py "$(PALCS)"
.PHONY: check-ghost-owned-fields
all: check-ghost-owned-fields
check-ghost-owned-fields: verify
	@python3 check_ghost_owned_fields.py "$(PALCS)"
.PHONY: check-ghost-consumption
all: check-ghost-consumption
check-ghost-consumption: verify
	@python3 check_ghost_consumption.py "$(PALCS)"
.PHONY: check-reopen-loops
all: check-reopen-loops
check-reopen-loops: verify
	@python3 check_reopen_loops.py "$(PALCS)"
.PHONY: check-raw-access
all: check-raw-access
check-raw-access: verify
	@python3 check_raw_access.py "$(PALCS)"
.PHONY: check-spec-shims
all: check-spec-shims
check-spec-shims:
	@python3 check_spec_shims.py "$(PALCS)"
check-immutable-integers: verify
	@python3 check_immutable_integers.py "$(PALCS)"
check-ghost-results: verify
	@python3 check_ghost_results.py "$(PALCS)"
check-plain-ghost-types:
	@python3 check_plain_locals.py --ghost-types "$(PALCS)"
check-plain-null-safety:
	@python3 check_plain_locals.py --null-safety "$(PALCS)"
check-plain-call-emission: verify
	@python3 check_plain_locals.py --emission
check-plain-definite-assignment:
	@python3 check_plain_locals.py "$(PALCS)"
check-borrow-fuel: verify
	@python3 -c 'from pathlib import Path; assert "#set-options \"--initial_fuel 0 --initial_ifuel 0\"" in Path("out/Func_Window_ReadWhileOpened.fst").read_text()'
runtime:
	dotnet run --project runtime/Runtime.csproj -p:UseSharedCompilation=false
