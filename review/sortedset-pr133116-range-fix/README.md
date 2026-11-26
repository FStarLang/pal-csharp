# Local review: preserve SortedSet view membership in the bitmap lookup

**Unsubmitted review package. Nothing in this directory has been pushed or
submitted as a PR.** The proposed production change is exactly one line; it has
no PAL annotations, verifier changes, or dependencies.

This is a correction **on top of dotnet/runtime#133116**, pinned to head
`254919ae80190e850cbac0275b499915e018e681`, not a patch against unrelated current
`main`. That PR addresses dotnet/runtime#102118's duplicate-counting bug but
allows a bounded view to count out-of-range underlying nodes as members.

## Run the before/after experiment

Prerequisites: .NET 10 SDK, Python 3.9 or later, and Git. Tested locally with
SDK `10.0.115`. No NuGet packages, F*, PAL tooling, or runtime checkout are needed.
The source snapshot is included, and `NuGet.Config` clears package feeds.

From this directory:

```sh
python3 run.py
```

The runner verifies all eight upstream file hashes, checks both patches, creates
isolated source copies, and builds the two variants in parallel in **Release**.
It runs the **same test sources** against both. It exits zero only if the
baseline has the exact expected failures and the fixed variant passes.
Unexpected builds, exceptions, failure patterns, or missing output are fatal.
The original snapshot is checked again afterward.

For the view `{2,3,4,5}`, the observed results are:

| Method | `other` (a `List<int>`) | Expected | Pinned PR | With fix |
|---|---|---|---|---|
| `SetEquals` | `{2,3,4,9}` | false | **true** | false |
| `IsSubsetOf` | `{2,3,4,9}` | false | **true** | false |
| `IsProperSubsetOf` | `{2,3,4,9,10}` | false | **true** | false |
| `IsProperSupersetOf` | `{2,3,9}` | false | **true** | false |

The proposed xUnit theory has four rows: incremental insertion versus enumerable
construction, each with a below-range (`0`) or above-range (`9`) key. All four
rows fail before the fix and pass afterward. The fixed run executes all four
assertions in each row; a failing row stops at its first assertion.

The standalone runner also executes 20 control assertions and 12 edge-case
assertions. All controls pass in both variants. Six edge assertions fail before
the fix and none fail afterward. These cover inclusive endpoints, duplicates,
an empty view, elements absent from the underlying tree, the original
18-element duplicate regression, the existing large-tree fallback, an
out-of-range first item, descending ordering, and case-insensitive equality.
The oracle for these additional cases is `HashSet` populated from the view's
enumeration, with equality matching the tested comparer, not the installed
BCL's `SortedSet` set-relation methods.

After running the driver, invoke either identical suite directly:

```sh
dotnet artifacts/baseline/bin/Repro.dll  # exits 1: actual assertion failures
dotnet artifacts/fixed/bin/Repro.dll     # exits 0: all assertions pass
```

Logs are in `artifacts/{baseline,fixed}/{build,run}.log`; machine-readable results
are in `artifacts/results.json`. Generated sources and outputs are ignored by
Git. `python3 run.py --prepare-only` checks hashes and patch application without
building. `--write-patches` regenerates the patches from the defined one-line
replacement and the marked test method in `Regression.cs`; normal runs instead
require exact agreement with the supplied patch files.

## Review files

| File | Purpose |
|---|---|
| [fix.patch](fix.patch) | Production-only, one-line patch |
| [regression.patch](regression.patch) | Focused test added to the existing upstream integer view fixture |
| [ROOT_CAUSE.md](ROOT_CAUSE.md) | Detailed counterexample, dispatch change, and correctness argument |
| [PR_DESCRIPTION.md](PR_DESCRIPTION.md) | Unsubmitted PR-ready title and description |
| [Regression.cs](Regression.cs) | Exact proposed test method, run against both variants |
| [Program.cs](Program.cs) | Minimal observations, controls, edge cases, and test execution |
| [Compatibility.cs](Compatibility.cs) | Nonalgorithmic internal support and minimal test assertions |
| [Repro.csproj](Repro.csproj), [run.py](run.py) | Standalone build and reproducibility checks |
| [SOURCES.md](SOURCES.md), [SHA256SUMS](SHA256SUMS) | Immutable provenance and file checksums |
| `upstream/` | Unmodified MIT-licensed source snapshot |

For a future upstream submission, only `fix.patch` and `regression.patch` belong
in the runtime code diff. The surrounding review package is not a proposed
runtime dependency. Against a checkout of the pinned head, these can be reviewed
or applied with:

```sh
git apply --check /absolute/path/to/this/package/fix.patch /absolute/path/to/this/package/regression.patch
git apply /absolute/path/to/this/package/fix.patch /absolute/path/to/this/package/regression.patch
```

These are local operations, not publishing instructions.

## What this validation does and does not establish

The subject is the actual vendored `SortedSet`, `TreeSubSet`, equality comparer,
`BitHelper`, and `EnumerableHelpers` sources, compiled into the executable.
A runtime assembly-identity assertion prevents accidentally testing the
installed BCL `SortedSet`. The fixed implementation differs only by `fix.patch`.

The compatibility file replaces private resource strings, obsolete-attribute
constants, and the debugger proxy, not collection algorithms. It also supplies
minimal `Theory`, `InlineData`, and `Assert.False` definitions so the proposed
test body executes without downloading xUnit. The normal runner verifies that
the test patch contains exactly that method, reindented into the existing
fixture. **The complete runtime xUnit project, its inheritance/discovery
infrastructure, and the full runtime test suite have not been built or run.**

Release is deliberate: this pinned PR still has Debug-only assertions calling
an older `FindRange` signature. Those unrelated source defects are not modified.
The project suppresses CS0436 for deliberate source-over-framework type
selection and SYSLIB0050/SYSLIB0051 for the upstream legacy serialization code.
All other warnings remain errors.

This package is executable regression evidence and a focused correctness
argument, not a new whole-library formal-verification claim. It does not repair
or certify unrelated overflow, fallback, or bitmap-growth behavior.

The surrounding repository also contains an implementation-backed public
`SetEquals(List)` proof and a range-guard removal experiment. See
[ROOT_CAUSE.md, section 9](ROOT_CAUSE.md#9-implementation-backed-public-call-proof)
for the command, dependency checks, and explicit size/trust limitations. These
proof prerequisites are separate from the standalone executable and are not
part of the proposed upstream patch.
