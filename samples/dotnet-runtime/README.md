# dotnet/runtime `System.Collections.Generic`

Collections from [dotnet/runtime](https://github.com/dotnet/runtime), verified in place:
the contracts are attributes on the original C# source files, and pal-csharp translates
those files to Pulse and checks them with F*. The files keep their upstream paths under
`src/`, so `diff` against upstream shows exactly what was added.

- **Upstream:** dotnet/runtime, commit `a69ba15b9ce80c57fe5eea2a16a9f9fb404201f2`.
- **Licence:** MIT; see [`LICENSE.TXT`](LICENSE.TXT). The rest of pal-csharp is licensed
  separately; see the repository root.

## What is verified

| Collection | Source | Verified |
|---|---|---|
| `List<T>` | `System.Private.CoreLib/.../Generic/List.cs` | constructors, `Add`, `Insert`, `Remove`/`RemoveAt`/`RemoveRange`, capacity and growth, `Clear`, `Contains`, `CopyTo`, `Reverse`, `ToArray`, `TrimExcess`, the indexer, `IndexOf`/`LastIndexOf`, `Exists`, `Find*`, `ForEach`, `RemoveAll`, `TrueForAll`, `BinarySearch`, `Sort` (array and `IComparer` overloads) |
| `Stack<T>` | `System.Collections/.../Generic/Stack.cs` | 18 members |
| `Queue<T>` | `System.Private.CoreLib/.../Generic/Queue.cs` | 19 members |
| `PriorityQueue<TElement,TPriority>` | `System.Collections/.../Generic/PriorityQueue.cs` | 20 members: `Enqueue`, `Dequeue`, `Peek`, the `Try*` forms, `DequeueEnqueue`, `EnqueueDequeue`, `Clear`, capacity management, and sift up/down for both comparer paths |
| `SortedList<TKey,TValue>` | `System.Collections/.../Generic/SortedList.cs` | 22 members and the class invariant (keys strictly sorted) |
| `HashSet<T>` | `System.Private.CoreLib/.../Generic/HashSet.cs` | `Clear`, `Count`, `Contains`, `FindItemIndex`, `Remove`, against an invariant that the hash chains are well formed |

**Enumerators and views.** Every collection's enumerator is verified as well:
`GetEnumerator`, `MoveNext`, `Current`, `Reset` and `Dispose`, plus the boxing
`IEnumerator.Current` and the explicit `IEnumerable<T>.GetEnumerator`. When the
collection's version is unchanged, `MoveNext` steps through the model; when it has changed,
`MoveNext` throws. Also verified: `PriorityQueue.UnorderedItemsCollection`, and
`SortedList`'s `KeyList`/`ValueList` views with their enumerators. In all, 101 enumerator
and view members are verified (`doc/translation.md` §28–§29).

Members that are not annotated, and why, are recorded in `doc/translation.md` §22–§29.
The other `.cs` files under `src/` are unmodified upstream files that the annotated ones
need in order to compile.

## Changes to the upstream code

Besides the pal-csharp attributes and `Pal.*` ghost calls:

- each collection's version counter is marked `[Wrapping]`, because it is allowed to
  overflow;
- in `List<T>.RemoveAll`, two one-line `while` loops were given block bodies, so that they
  can hold loop invariants;
- `Stack<T>.Enumerator.ThrowInvalidVersion` is marked `[DoesNotReturn]`.

## Layout

- `src/`: the dotnet/runtime sources, at their upstream paths.
- `pal/<Collection>/`: one harness per collection. Its `Makefile` names the sources and
  includes `test/verify.mk`. Any `.cs` beside it stands in for runtime internals the
  collection uses (`SR`, `ThrowHelper`, etc.), and any `.fst` is an F* theory the
  contracts refer to.
- `pal/common/`, `pal/HashCommon/`: stand-ins shared by several harnesses.

The harnesses only translate and verify. They do not run the stock-compiler check that
`test/` does, because these files compiled on their own would collide with the BCL types
of the same names; compiling them is the runtime's own build.

## Running

```bash
make -C samples/dotnet-runtime              # all collections
make -C samples/dotnet-runtime/pal/List     # one
```

`make test` at the repository root runs them too.

Not included: `SortedSet<T>`, `SortedDictionary<TKey,TValue>`, `LinkedList<T>` and
`Dictionary<TKey,TValue>`, which still need translator support (see §23 and §25).
