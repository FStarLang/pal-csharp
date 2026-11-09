# Soundness campaign

Branch: `soundness_analysis`. Baseline: `fd96720`.

## Plan and acceptance criteria

1. Establish a green baseline. Diagnose main CI, run `make test` with the pinned
   toolchain, and fix actual build failures rather than masking terminated jobs.
2. Audit the trust boundary: assumptions, admits, interface-only declarations,
   generated proof escape hatches, and upstream primitives. Try to derive `False`
   from suspicious axioms. Record counterexamples, not just plausibility arguments
   about the CLR.
3. Replace the array length axiom with an immutable length-carrying representation.
   Lift the array operations and span borrowing interface, prove their contracts,
   and restrict spans to representable lengths instead of bounding all Pulse slices
   axiomatically. Identify any remaining allocation/runtime assumptions separately.
4. Audit semantic preservation: evaluation order, numeric operations/conversions,
   erasure, exceptions, reference identity, vtables and inheritance. For each
   confirmed bug, retain a minimal regression and either implement the actual C#
   semantics or reject the unsupported construct.
5. Execute a translated subset and compare with ordinary C#, starting with scalar
   evaluation order, arrays and virtual dispatch where extraction permits. Execution
   is complementary evidence, not a soundness proof. Do not equate absence of
   `assume` syntax with an executable or assumption-free dependency closure.
6. Run the full gate after integration. Commit build/gate work, representation
   changes, semantic fixes and executable regressions separately. Document residual
   assumptions and untested areas; do not claim the entire translator sound.

## Baseline investigation

Main CI run `42495959606` stopped after about 23 minutes, before its 150-minute
timeout. The gate job log ends with exit 143 and an explicit runner shutdown
message; the two active verification jobs were terminated, with no preceding
proof error. The analyzer job passed. The failed job was rerun rather than
weakening verification or raising proof limits.

## Evidence and remaining work

This section is updated as the campaign progresses. The older
`SOUNDNESS_FINDINGS.md` is a historical report, not a current certificate of the
trust boundary.
