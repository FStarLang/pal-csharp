# Source provenance

Upstream repository: [dotnet/runtime](https://github.com/dotnet/runtime).

Reviewed PR: [dotnet/runtime#133116](https://github.com/dotnet/runtime/pull/133116),
"Fix SortedSet.IsSubsetOf et al".

Immutable head:
[`254919ae80190e850cbac0275b499915e018e681`](https://github.com/dotnet/runtime/commit/254919ae80190e850cbac0275b499915e018e681).
The PR's head repository/branch when inspected was
`lilinus/runtime:SortedSet-CheckUniqueAndUnfoundElements`.
The package makes no claim about later revisions or the PR's future status.

The following files were downloaded verbatim under `upstream/` using
`https://raw.githubusercontent.com/dotnet/runtime/254919ae80190e850cbac0275b499915e018e681/`
followed by the listed path. The original MIT license and file headers are
retained. [SHA256SUMS](SHA256SUMS) records the exact downloaded bytes.

```text
LICENSE.TXT
src/libraries/System.Collections/src/System/Collections/Generic/SortedSet.cs
src/libraries/System.Collections/src/System/Collections/Generic/SortedSet.TreeSubSet.cs
src/libraries/System.Collections/src/System/Collections/Generic/SortedSetEqualityComparer.cs
src/libraries/Common/src/System/Collections/Generic/BitHelper.cs
src/libraries/Common/src/System/Collections/Generic/EnumerableHelpers.cs
src/libraries/System.Collections/tests/Generic/SortedSet/SortedSet.Generic.Tests.cs
src/libraries/System.Collections/tests/Generic/SortedSet/SortedSet.TreeSubSet.Tests.cs
```

The five implementation files are compiled unchanged in the baseline. Only
`SortedSet.cs` receives a production change in the fixed variant. The two
upstream test files provide review context and the exact insertion target for
`regression.patch`; the standalone project does not compile their entire
fixtures. Instead it runs the exact added test method from `Regression.cs`.

The rest of the framework comes from .NET 10. Private support types and local
test infrastructure are explicitly listed in `Compatibility.cs`. No collection
algorithm from these five upstream files is replaced by a shim.

To independently check local integrity:

```sh
cd upstream
sha256sum --check ../SHA256SUMS
```

These checksums detect local changes relative to this manifest; they are not
an upstream signature. The immutable download URLs allow independent
comparison with the upstream content.
