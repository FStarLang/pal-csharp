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

The rerun (`128993154717`, gate job) also received a runner shutdown signal,
after about 42 minutes, while checking the same two sample methods. Neither run
reported an F* proof error before termination. The local baseline built the
toolchain and support library and checked most sample methods; it was stopped
after integration edits invalidated its running dependency graph, so it is not
counted as a green baseline. A complete integrated gate is required below.

Parallel stock-C# builds also exposed an actual build race: separate MSBuild
processes tried to write `Pal.Annotations.pdb` concurrently (CS2012). The test
harness now locks stock-C# compilation; F* verification remains parallel.
The child lock descriptor is closed before spawning MSBuild, so persistent
build workers cannot retain the lock after their build finishes.

## Findings and residual trust

The older `SOUNDNESS_FINDINGS.md` is a historical report, not a current certificate
of the trust boundary.

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

### Repairs and executable evidence

The compiler emits Boolean XOR as inequality, preserves the IEEE factor bits
in the scaling abstraction, and rejects reordered named arguments and potentially
overflowing checked narrowing casts. `Debug.Assert` and `Debug.Fail` are erased,
including their arguments, matching Release C# without `DEBUG`; `Pal.Assert`
remains the explicit checked assertion. An initial refusal of effectful debug
conditions was replaced by faithful erasure when integration exposed calls to
ordinary getters inside existing debug assertions.
The original false contracts are retained as diagnostic/proof-refusal tests.
The scaling model still specifies only bounds, not executable floating arithmetic.

`Array.Base` now pairs a raw array with a nonnegative `Int32` count. Its refinement
ties the count to the underlying storage, with a separate null case. Ownership,
allocation, reads, writes, sharing, gathering and copying are proved wrappers.
The record is hidden behind a verified interface: clients see the count and storage
projections, but do not unfold the representation in every unrelated SMT query.
This abstraction also removed an integration-time timeout in the Adler32 variant.
HashSet removal needed an explicit predecessor-range/distinctness lemma before
its writes: the facts are proved from the chain invariant, rather than rediscovered
inside a large sequence-update query. No contract or proof limit was weakened.
A paired-cursor regression likewise checkpoints the first cursor's length invariant
before advancing the second, retaining the original loop invariant and limit.
Ordinary allocation uses the verified `Vec` allocator, not deprecated raw-array
allocation. Array length is an executable record projection. Spans are raw slices
refined to have representable lengths; their length conversion and borrow/restore
operations are proved, with no global length assumption.

`test/runtime_comparison` compares ordinary Release C# with extracted OCaml for all Boolean
input pairs, eager versus short-circuit evaluation, narrowing/widening casts,
in-order named arguments, debug-call erasure (including message effects),
array allocation/read/write/length, and three hierarchy
clients covering multiple vtables, virtual mutation and downcasts. The array/span
round-trip is verified too, but **not executed**: the pinned Custard extractor
raises `pointer arithmetic has no OCaml representation` for raw slice operations.
The hierarchy runtime includes an explicit test-only `recover` adapter implemented
by `Obj.obj`, matching Custard's erased dynamic representation. This executes the
generated dispatch logic without pretending to eliminate its recovery assumption.

The two original length-axiom `emp -> False` proofs are retained as negative F*
tests. They must fail at the new array type/span refinement, not merely fail
somewhere for an unrelated error. Their huge allocations are never executed.

`test/trust-boundary.py` pins interface-only modules, sources containing explicit
assumptions/admits, and toolchain pins in `doc/trusted-sources.sha256`. Changes
require an explicit reviewed manifest update. This conservative review tripwire
also includes definitional interface-only modules and comments; it is not a
transitive logical audit or a proof that every remaining assumption is consistent.
The support-library Makefile rejects `ADMIT`, which previously populated the
ordinary verification cache with admitted queries.

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
- Decimal and opaque object/type/null/identity bindings are not executable
  implementations of the full CLR behavior. The trust inventory includes
  interface-only declarations as well as explicit assumptions.
- User-supplied Pulse, `[Admit]`, `Pal.Assume`, and specification bindings remain
  explicit trust extensions. The upstream F*/Pulse logic, primitives, extraction
  and runtime remain part of the trusted computing base.

The campaign's regression and execution checks are evidence for specified
fragments, not a proof of semantic preservation for all accepted C#.

## Final validation

`make -j16 test` completed with exit code 0 on `soundness_analysis`, using the
pinned toolchain and ordinary, non-admitted verification caches. This includes
the translator build, support library, examples, dotnet-runtime samples, and
the complete regression tree.

- All 103 diagnostic cases and 30 C# proof-refusal cases passed.
- Both original array/span `emp -> False` attempts were refused at the intended
  type/refinement boundary.
- Release C# and extracted OCaml produced identical results for the executable
  regression suite described above.
- All lints passed, including the 21-source trust inventory; the analyzer was
  silent across 68 projects.
- An isolated trust-inventory check rejected an added unreviewed interface.
  The support-library gate also rejected `ADMIT`.

This is a green **local integrated branch**, not a claim that the historical
baseline or remote main CI completed successfully. Both inspected CI attempts
were terminated as described above. No proof limits were raised and no new
logical assumptions or admits were added to obtain the green gate.
