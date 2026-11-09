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

### Confirmed baseline counterexamples

The following all translated without diagnostics and verified with the pinned
F*/Pulse toolchain. Compiling and running the C# in Release contradicted each
claimed result:

| Construct | Claim proved before the repair | Actual C# |
|---|---|---|
| `x ^ y` for booleans | `Result == (x || y)` | `true ^ true` is false |
| `First(second: 2, first: 1)` | result is 2 | result is 1 |
| `checked((byte)x)` at `x == 256` | returns 0 | throws `OverflowException` |
| `Debug.Assert(++x == 1)` at `x == 0` | final `x == 1` | Release erases the call and its arguments; `x == 0` |
| `(int)((double)x * 0.5)` versus `* 0.75` | results are equal for every `x` | at 4 the results are 2 and 3 |

The Boolean counterexample was also extracted to OCaml and executed: the
translated program returned true where the original returned false.

Both length axioms admit a stronger counterexample: a total Pulse computation
with precondition `emp` and postcondition `pure False`. Allocate a
`Pulse.Lib.Vec` of length 2^31 (using `SizeT.uint32_to_sizet`), expose its array,
and call `CSharp.Array.arr_length_bound`. Alternatively convert the same array
to a `Pulse.Lib.Slice` and call `CSharp.Span.span_length_bound`. Both verified.
Neither needs a C# program, a local admit, an unsafe array allocation primitive,
or an inconsistent precondition. These are proof-only counterexamples; no
multi-gigabyte allocation was executed.

The error is quantification, not a missing CLR fact: a restriction on C# arrays
cannot consistently be imposed on **every** Pulse array or slice. The wrapper
must carry the restriction in its type instead.

### Trust that must not be hidden

Removing the length axioms does not make the entire translation axiom-free:

- `Assumptions.recover` is still an unimplemented, total dynamic recovery
  primitive used by the open-world hierarchy/vtable encoding. Termination and
  faithful recovery are trusted, not derived from `FStar.Dyn.undyn`.
- The platform's `SizeTFitsU32` assumption remains.
- Generic empty-array allocation and LINQ sorting still have admitted
  implementations. The pinned `Vec` API has no empty allocator independent of
  an element value. Replacing that admit by deprecated `Array.mask_alloc`
  would only move the trust into a primitive explicitly marked unsafe; this
  campaign does not do that.
- Comparers, delegates and several BCL bindings assume purity, determinism and
  termination; those properties do not hold for arbitrary C# implementations.
  Comparer order/hash laws are assumptions on clients, not CLR guarantees.
- User-supplied Pulse, `[Admit]`, `Pal.Assume`, and specification bindings remain
  explicit trust extensions. The upstream F*/Pulse logic, primitives, extraction
  and runtime remain part of the trusted computing base.

The campaign's regression and execution checks are evidence for specified
fragments, not a proof of semantic preservation for all accepted C#.
