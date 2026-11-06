# The pal-csharp annotation surface

This is the user-facing reference: everything you can write in an annotated C# program, and
what each construct means. It is the C# counterpart of `pal/doc/pal_surface_syntax.md`.

For *how* each construct is translated, see [`translation.md`](translation.md), which is the
specification the emitter implements. This document says what to write; that one says what
comes out.

---

## 0. The one guarantee

**An annotated program is an ordinary C# program.** It compiles with the stock C# compiler,
runs unchanged, and the annotations cost nothing:

* attributes are inert metadata;
* the `void`-returning `Pal.*` intrinsics are `[Conditional("PAL")]`, so unless `PAL` is
  defined the C# compiler removes **the entire call site, including argument evaluation** —
  `Pal.Invariant(Sorted(a, 0, i))` does not evaluate `Sorted`;
* `Ghost<T>` parameters are optional parameters of an empty `readonly struct`, so callers
  need not mention them and nothing is allocated.

There is no `#ifdef` to get wrong. PAL needs `-DC2PULSE`; pal-csharp needs nothing.

The value-returning intrinsics (`Pal.Old`, `Pal.Result`, `Pal.Forall`, …) cannot be
`[Conditional]`, because they return a value. They only ever occur as arguments to a
conditional intrinsic or inside an attribute string, so they are erased along with their
enclosing call. Calling one directly is a programming error and throws.

Add a reference to `Pal.Annotations` and `using PalLang;`.

---

## 1. Contracts

### 1.1 On a declaration, as attributes

```csharp
[Requires("0 <= n && n <= a.Length")]
[Ensures("Result >= 0")]
[Ensures("Contents(a) == Old(Contents(a))")]
public static int Count(int[] a, int n) { … }
```

| Attribute | Meaning |
|---|---|
| `[Requires(p)]` | precondition; repeatable, conjoined in order |
| `[Ensures(p)]` | postcondition; repeatable, conjoined in order |
| `[Preserves(p)]` | shorthand for `[Requires(p)] [Ensures(p)]` |
| `[PreservesValue(e)]` | shorthand for `[Ensures("e == Old(e)")]` |
| `[Decreases(m)]` | termination measure of a recursive method |
| `[Throws(typeof(E), p)]` | the method may throw an `E`, and then `p` holds; repeatable, disjoined (§2.3) |

**The strings are not opaque.** Each is parsed with `SyntaxFactory.ParseExpression` and
bound by Roslyn *in the scope of the annotated member*, so parameters, locals, `[Spec]`
functions, sibling classes and `this` all resolve and are type-checked. A mistake inside a
string is reported at its position inside the string literal, not against the attribute.

**Order matters, and is a real obligation.** F\* type-checks `p₁ /\ p₂` with `p₁` in scope,
so a conjunct that establishes a bound must precede one that relies on it:

```csharp
[Ensures("0 <= Result && Result < a.Length")]   // must come first
[Ensures("Contents(a)[Result] == key")]         // needs the bound above
```

A postcondition is checked *under* the precondition (R4.8), so a postcondition may rely on
whatever the precondition established without restating it.

### 1.2 In statement position

Contracts may equally lead the method body. This form has full IntelliSense, refactoring
and no string parsing; it cannot express a contract for a bodyless member.

```csharp
public static int Count(int[] a, int n)
{
    Pal.Requires(0 <= n && n <= a.Length);
    Pal.Ensures(Pal.Result<int>() >= 0);
    …
}
```

Both forms lower to the same thing. Mix them freely.

### 1.3 The specification vocabulary

| Written | Means |
|---|---|
| `Old(e)` | the value of `e` on entry (postconditions only) |
| `Result` / `Pal.Result<T>()` | the returned value (postconditions only) |
| `Implies(p, q)`, `Iff(p, q)` | `⟹`, `⟺` — C# has no operator for either |
| `Forall((int i) => …)`, up to three binders | universal quantification |
| `Exists((int i) => …)`, up to two binders | existential quantification |
| `Contents(a)` | the ghost `Seq<T>` of an array's contents |
| `IsPermutation(s, t)` | `s` is a rearrangement of `t` |
| `SetAt(s, i, v)`, `Slice(s, i, j)` | ghost sequence update and subsequence |
| `Splice(s, i, j, t)`, `Reverse(s)` | `s` with `[i, j)` replaced by `t`; `s` reversed |
| `Ring(s, h, n)` | the `n` elements of a circular buffer `s` from `h`, wrapping once (`0 <= h <= s.Length`, `0 <= n <= s.Length`; else empty) |
| `IndexOf(s, x)`, `IndexOf(s, x, i, n)` | first match of `x` in `s` (or in `[i, i+n)`), else `-1` |
| `LastIndexOf(s, x)`, `LastIndexOf(s, x, index, count)` | last match, searching back from `index` over `count` elements |
| `DefaultEquals(a, b)` | `EqualityComparer<T>.Default.Equals(a, b)` |
| `Compare(c, x, y)` | `c.Compare(x, y)` for a ghost comparer `c` (an `IComparer<T>`), up to sign (R25.6) |
| `IsNull(x)` | `x` is `null`, for a type parameter or a comparer (R25.4) |
| `Sorted(c, s)`, `StrictlySorted(c, s)` | `s` ascends under `c`, allowing / forbidding equal neighbours (R25.6) |
| `LowerBound(c, s, x)` | the number of elements of `s` less than `x` under `c`: where `x` goes (R25.6) |
| `KeyIndex(c, s, x)` | the position of `x` in a strictly sorted `s`, else `-1` (R25.6) |
| `BinarySearch(c, s, i, n, x)` | what `Array.BinarySearch(a, i, n, x, c)` returns on contents `s` (R25.5) |
| `FindIndex(s, p)`, `FindIndex(s, p, i, n)` | first position whose element `p` holds of (in `[i, i+n)`), else `-1`; `p` a `Predicate<T>` (R26.3) |
| `FindLastIndex(s, p)`, `FindLastIndex(s, p, index, count)` | last such position, searching back from `index` over `count` elements (R26.3) |
| `TrueForAll(s, p)` | `p` holds of every element (R26.3) |
| `FindAll(s, p)`, `RemoveAll(s, p)` | the elements `p` holds / does not hold of, in order (R26.3) |
| `ConvertAll(s, f)` | `s` mapped through the `Converter<T, TOutput>` `f` (R26.3) |
| `Permutation(s, t)` | `t` is a rearrangement of `s`, by an explicit bijection (R26.7) |
| `SortedRange(s0, s1, i, n, c)` | `s1` is `s0` with `[i, i+n)` sorted under `c ?? Comparer<T>.Default`: what `Array.Sort(a, i, n, c)` does (R26.7) |
| `IsHeap(s, c)`, `HeapMin(s, x, c)` | `s` of `(element, priority)` pairs is a 4-ary min-heap under `c`; no node of `s` is below `x` (R26.10) |
| `HeapUp`, `HeapDown`, `HeapUpStop`, `HeapDownStop`, `HeapMinChild` | sift-up/sift-down loop invariants and exit conditions (R26.10) |
| `Tree<V>(x)`, `WellFormed(x)` | the `SpecTree<V>` of views a `[Region]` pointer reaches; every path from it ends at `null` (R27.7) |
| `s.Length`, `s[i]` on a `Seq<T>` | length and indexing of a ghost sequence |
| `Same(a, b)` | `a == b`, where C# refuses `==` — an unconstrained type parameter |
| `Live(x)` | ownership of `x`, when inference cannot see it |
| `PtsTo(p, v)`, `Pure(p)`, `ExistsProp(v => …)` | separation-logic resources |

Inside an attribute string these are written unqualified (`Old`, `Result`, `Contents`);
in statement position they are written `Pal.Old`, `Pal.Contents`, and so on. `Result` is
the bare spelling in a string; `return` is *not* available, because it is a C# keyword and
the string is parsed as C#.

---

## 2. Loops

Attributes cannot attach to statements, so loop annotations are leading statements of the
loop body:

```csharp
while (lo < hi && !found)
{
    Pal.Invariant(0 <= lo && lo <= hi && hi <= a.Length);
    Pal.Invariant(Sorted(Pal.Contents(a), 0, a.Length));
    Pal.Decreases(hi - lo);
    …
}
```

| Intrinsic | Meaning |
|---|---|
| `Pal.Invariant(p)` | a loop invariant; repeatable |
| `Pal.Decreases(m)` | the termination measure |
| `Pal.Broke()` | in an invariant: a `break` out of this loop was taken (R26.10) |
| `Pal.Returned()`, `Pal.ReturnValue<T>()` | in an invariant: a `return` inside this loop was taken, and its value (R26.2) |
| `Pal.Assert(p)` | a proof step |
| `Pal.Assume(p)` | assume without proof — **unsound**, reported as a warning |

Four things about loops are worth knowing before you write one.

**Every loop needs a measure.** Pulse requires it (F2). pal-csharp infers one only for a
counted `for` — `for (int i = 0; i < n; i++)` and its descending mirror — and otherwise
demands `Pal.Decreases`. It will not guess: a guessed measure is a proof step the
translator invented.

**The measure must decrease on every path**, including the path that stops the loop. A
loop that finishes its work on the iteration that also ends the loop typically needs the
"exit" step to shrink the measure as well — see `test/binary_search`, where the branch that
finds the key also advances `lo`.

**Ownership is inferred.** PAL requires an explicit `_invariant(_live(x))` for every local
a loop touches; pal-csharp computes that from the body. `Pal.Live(x)` is the manual
override for what inference cannot see.

**A loop body sees the invariant and nothing else.** Facts from the enclosing `[Requires]`
are *not* in scope inside the loop. Restating one as an invariant is the single most common
fix when a correct loop will not verify.

**An invariant may own.** `Pal.Invariant` also accepts an `SlProp` — an `[SpecOp]` that
denotes ownership (§9) — and then states what the loop *holds* at the top of each
iteration, not merely what is true of its values. This is what a loop that walks a data
structure needs, and §2.2 is about writing one.

### 2.1 `break` and `continue`

Both are supported. The flag the translation uses is internal, but an invariant may name
it as `Pal.Broke()`: `Pal.Implies(Pal.Broke(), …)` says what held when the loop was left
early, which is how a postcondition learns why the loop ended (R26.10, `test/collections_listrest`).
Carrying the exit condition in the guard — `while (i < n && !done)` rather than
`if (…) break;` — also works; `test/compare_elements` does that. A `return` inside a loop
is supported too (R26.2), and `Pal.Returned()`/`Pal.ReturnValue<T>()` name it likewise.

A guard may write a local: `while ((i = f(n)) < size)` or `while (++i < bound)` (R26.11).
The invariant then describes the state just after the write.

A `return` inside a loop is supported too (translation.md R24.14). Its flag *can* be named,
inside the loop: `Pal.Returned()` is whether a `return` in the loop has run, and
`Pal.Result<T>()` is the value it returned. The invariant says what a `return` established:

```csharp
while (i < a.Length)
{
    Pal.Invariant(Pal.Implies(Pal.Returned(), Pal.Result<int>() >= 0 && Pal.Contents(a)[Pal.Result<int>()] == x));
    …
    if (a[i] == x) return i;
    i++;
}
```

`Pal.Returned()` outside a loop is an error (`PALCS0645`).

### 2.2 Cursors

A loop that walks a linked structure owns a different part of it on each iteration. The
idiom, in full:

```csharp
Cells.Start(head, xs);                       // establish the invariant
Cell<T>? at = head;
int i = 0;
while (at != null)
{
    Pal.Invariant(Cells.Seg(head, at, SpecList.Take(xs.Value, i)));   // walked
    Pal.Invariant(Cells.Held(at, SpecList.Drop(xs.Value, i)));        // remaining
    Pal.Invariant(0 <= i && i <= xs.Value.Length);
    Pal.Decreases(SpecList.Drop(xs.Value, i).Length);
    …
}
Cells.Finish(head, at, i, xs);               // give the whole structure back
```

Three things make this work, and all three are things *you* write:

* **Name the walked part with a function of the counter.** `Take`/`Drop` for a list, a
  one-hole context for a tree (`test/tree_cursor`). Never accumulate it in a ghost variable:
  a total function of `i` is what lets the invariant be re-established without a history.
* **Give the measure the structure's size, not the counter.** `Pal.Decreases` is required
  here — a tree has no length by which a counter could be bounded.
* **For a loop with two ways out, use a flag in the measure.** `break` cannot be mentioned
  by an invariant (§2.1), so write `int live = 1;` as the loop condition and
  `Pal.Decreases(remaining.Size + live)`. A step shrinks the structure; stopping clears the
  flag; both decrease the sum. `test/tree_cursor/Search.cs` is the worked example.

Inside the loop, a null test of a `[Plain]` reference is an ordinary comparison — it may be
a loop condition, and a field read after it is checked against whatever your lemmas
establish. That is §9's bargain: you own the predicate, so you own the case analysis.

---

### 2.3 Exceptions

A method that may throw says what, and when, with `[Throws]`. `Thrown` names the exception
at the declared class, so its fields can be read; everything else in the predicate is read
in the pre-state:

```csharp
[Throws(typeof(RangeError), "Thrown.Code == 2 && Contents(a)[Thrown.Index] < 0")]
public static int CheckAll(int[] a) { … throw new RangeError(2, i); … }
```

A method with no `[Throws]` is proved never to throw, so every exception a callee declares
has to be caught. A `try` is written the way a loop is: what holds when it exits goes in
`Pal.Invariant`s at the head of its body, because a handler knows the *class* of what it
caught and nothing more:

```csharp
try
{
    Pal.Invariant(result >= 0 - 2);
    result = CheckAll(a);
}
catch (AppError e) when (e.Code == 25) { result = 0 - 2; }
catch (AppError) { result = 0 - 1; }
```

An exception class has an immutable payload (get-only properties set by its one
constructor), and `finally`, and a `return` inside a `try`, are not supported.
doc/translation.md §19 has the details.

### 2.4 Verifying production code in place

`[assembly: TranslateAnnotatedOnly]` makes pal-csharp translate only annotated members,
so a production file can be verified by adding attributes to the one method that matters.
That code may use `decimal`, `string`, `T?` (`HasValue`, `Value`), `IList<T>` / `List<T>`
(treated as arrays), `foreach` over a list or array, and `OrderBy(x => x.P).ToList()`.
Inside a `foreach`, `Pal.Index(x)` is the position of the current element:

```csharp
foreach (var band in schedule)
{
    Pal.Invariant(Pal.Forall((int j) => Pal.Implies(0 <= j && j < Pal.Index(band),
        ScheduleResult.BoundOk(Pal.Contents(schedule)[j]))));
    …
}
```

doc/translation.md §20 has the rules, and the library assumptions such a proof trusts.

## 3. Ownership

Most of what PAL spells with macros is already in the C# type system.

| C# | Meaning in the proof |
|---|---|
| `T x` | a value; no resource |
| `ref T x` | `pts_to` in both the pre- and the postcondition |
| `out T x` | as `ref` (see the limitations in `translation.md` §8) |
| `in T` / `ref readonly T` | as `ref`, read-only when combined with `[Frac]` |
| `T[] a` | the array, plus `A.pts_to a s` for its contents |

The residue is attributes:

| Attribute | Meaning |
|---|---|
| `[Frac("p")]` | hold the parameter at a fractional permission `p` — **read-only**, and shareable |
| `[Consumes]` | ownership is taken and not returned |
| `[Plain]` | suppress the resource the type would otherwise imply |
| `[NonNull]` | the reference is known non-null |

`[Frac]` is the one with real consequences. Because the permission is exactly the right to
read, the contents cannot change: the same binder stands for the argument's contents before
and after, so postconditions about it need no existential, and — the point — the **same
array or object may be passed to two parameters at once**. Writing through a `[Frac]`
parameter is an error.

Two `[Frac]` parameters must be given **different** permission names. That is what makes
them allowed to be the same thing: one shared name would tie them together again and forbid
the aliasing the attribute exists to allow.

### Splitting a permission: `Pal.Share` and `Pal.Gather`

Passing one array to two `[Frac]` parameters does not work by itself. Pulse holds the whole
permission under one name and will not split it on a guess, so the call is refused with
`Cannot prove: A.pts_to var_a _ _` against a context holding exactly that. The split is
written:

```csharp
Pal.Share(a);              // a is now held as two halves
bool same = Equal(a, a);   // each parameter takes one
Pal.Gather(a);             // and the two halves become one again
```

`Pal.Gather` is `Pal.Share`'s exact inverse, so the pair round-trips with nothing in
between and full ownership is restored — a mutator is callable again afterwards. It also
proves the two views **agreed**, which is not an extra assumption: they were views of one
object, so nothing else was possible.

Both work on objects as well as arrays, and on an object the permission reaches everything
it owns — its fields, its arrays and its sub-objects, all the way down. So a whole object
graph can be observed through a fraction, and none of it can be written through one.

Why you write this and not the compiler: deciding where to split means recognising that two
expressions denote the same object, and no C# frontend can do that — the two names may be
fields, or may have been aliased three statements earlier. A split is a proof step, and
proof steps are the annotation language's job.

**Two views at a time, and no more.** Sharing an already-shared name leaves three resources
that all look alike, and Pulse's matcher needs a unique candidate, so the next call is
refused. Three observers are reached by nesting — share, use both, gather, then share
again — not by sharing twice.

### Structs

A `struct` is translated as an F\* record, and `[Refine]` puts a predicate on it:

```csharp
[Refine("Lo <= Hi")]
public struct Range
{
    public int Lo;
    public int Hi { get; set; }   // an auto-property is a field
}
```

Three things are worth knowing.

**A refinement names the fields directly.** Write `[Refine("Lo <= Hi")]`, not
`[Refine("this.Lo <= this.Hi")]`: inside a struct declaration an unqualified field name is
what a C# programmer expects, and `this` is a keyword that cannot be bound. A `[Refine]` on
a single field reads the same way — `[Refine("Count >= 0")]` on `Count`.

**The refinement is a type, not an obligation you carry around.** Whoever produces a
`Range` proves it; whoever consumes one may assume it. Neither costs an annotation.

**A struct field must be a value** — a scalar, or another struct that pal-csharp
translates. An `int[]` field is rejected (`PALCS0511`). This is the model, not a gap: a C#
struct is *copied* on assignment, so a struct holding an array would give every copy a
second claim on the same memory, which is exactly the aliasing separation logic exists to
rule out. C can put a pointer in a struct because a C struct is addressed rather than
copied. In pal-csharp the storage travels alongside the state that describes it:

```csharp
public static void Enqueue(int[] a, ref RingState s, int value)
```

Structs are built with object initializers; unmentioned fields take their zero. A
user-written constructor is rejected.

```csharp
var r = new Range { Lo = 0, Hi = 10 };
```

`default(T)` is allowed, but on a refined struct it carries a real obligation — the zero
value must satisfy the refinement, and often it does not. That is the annotation doing its
job.

### Classes

A class is what lets state and the storage it describes finally live together. Compare the
struct version above:

```csharp
// The model: a pure, ghost description of what a Stack *is*. You write it; pal-csharp
// does not invent it. `[Spec]` on a struct makes it a spec-only type, so unlike an
// ordinary struct it may hold `Seq<T>` and other spec-only types. An unbounded stack
// could just use `Seq<int>` directly and declare no model struct at all.
// A fact about the MODEL is a `[Refine]` here, not an `[Invariant]` on the class — see below.
[Spec]
[Refine("Elems.Length <= Capacity")]
public struct StackModel
{
    public Seq<int> Elems;
    public SpecInt  Capacity;
}

// A fact about the FIELDS is an `[Invariant]` here. It may be temporarily false inside a
// method; the model refinement above never can be.
[Invariant("0 <= top && top <= items.Length")]
public sealed class Stack
{
    private int[] items;      // a class MAY own an array; a struct may not
    private int top;

    // The abstraction function: the ONE member that may read the fields. It says how the
    // representation is understood as a model.
    [Model]
    public StackModel Model => new StackModel {
        Elems    = Pal.Slice(Pal.Contents(items), 0, top),
        Capacity = items.Length
    };

    // [Spec] members are functions of the MODEL, never of the fields.
    [Spec] public SpecInt Count    => Model.Elems.Length;
    [Spec] public SpecInt Capacity => Model.Capacity;

    [Requires("0 <= capacity")]
    [Ensures("@this.Count == 0 && @this.Capacity == capacity")]
    public Stack(int capacity) { items = new int[capacity]; top = 0; }

    [Requires("@this.Count < @this.Capacity")]
    [Ensures("@this.Count == Old(@this.Count) + 1")]
    [Ensures("@this.Capacity == Old(@this.Capacity)")]
    public void Push(int v) { items[top] = v; top = top + 1; }

    [Ensures("Result == @this.Count")]
    public int Size() => top;
}
```

Five things are worth knowing, and each is a consequence of the scheme rather than a
convention.

**A fact about the fields goes in `[Invariant]`; a fact about the model goes in `[Refine]`
on the model type.** This is the one thing worth reading twice, because putting a fact in
the wrong place produces a class that verifies and is still useless.

`[Invariant]` states how the *memory-resident fields* hang together: `0 <= top` and
`top <= items.Length`. Such a fact is *temporarily false* inside a method — `Push` above
breaks it between the two field writes — and is re-established on exit, which is why it
cannot be a refinement, and why `[Invariant]` and `[Refine]` are different attributes.

`Elems.Length <= Capacity` is a different kind of fact: it mentions no field, only the
model. Written as `[Invariant]` it would be true and *invisible* — your callers hold the
object's invariant as an opaque predicate, so a fact buried inside it is one they cannot
use. Written as `[Refine]` on `StackModel` it travels in the model's type and every caller
has it, everywhere, without asking. The compiler will tell you if you get this backwards
(`PALCS0527`).

If your model is an atomic type such as `SpecInt` or `Seq<int>` there is no struct to
refine, so put the `[Refine]` on the `[Model]` member instead and name the model value
`Result`, as you would in an `[Ensures]`. That form works for a struct model too, and is the
right one when the fact is something this *class* guarantees rather than something intrinsic
to the model type.

You never have to state the connection between the fields and the model, though: that is
what `[Model]` is, and it is always part of the invariant.

**You choose the model; the compiler does not derive it.** `[Model]` names a pure ghost
type of your choosing, so it can be a type you already have a theory about, and you can
state and prove pure lemmas about it without mentioning `Stack` at all. `[Model]` is also
the *only* member allowed to read the fields.

**The receiver is spelled `@this`, and contracts see only accessible members.** A spec
string is compiled as the body of a static method, so a bare `this` is a C# error; `@this`
is the same word as a verbatim identifier, and it binds. Write it once and you will not
think about it again — and if you forget, the error says so. For the same reason a contract
may name only `public` or `internal` members; `[Model]` may stay `private`, because only
the object's own invariant consumes it.

**Your contracts talk about the object through its `[Spec]` members, which are functions of
the model.** `@this.Count == Old(@this.Count) + 1` means what it says. A `[Spec]` member
that reads a field directly is rejected (`PALCS0523`) — because a caller holds only the
model, so an observation it cannot compute from the model is one it cannot use.

That gives the rule worth remembering: **every quantity a caller needs must be in the
model.** Had `Capacity` been left out of `StackModel`, `Push`'s
`[Requires("Count < Capacity")]` would be unwritable and `Push` uncallable — the class would
verify and be useless. You find this out at the declaration, not at a call site.

**An object is owned, so two parameters are two different objects** — unless you say
otherwise. `Merge(Stack a, Stack b)` may not be called as `Merge(s, s)`. That is not a
compiler error — it translates perfectly well — it is an unprovable one, and Pulse reports
it as `Cannot prove: class_Stack__inv var_s _` on the calling line. pal-csharp refuses what
it cannot translate; what cannot be *proved* is the prover's to say, and keeping that
boundary sharp is why the frontend is small. Ownership also means a `C`-typed reference is never
`null`, so no method needs a null check to satisfy the translator. A `C?` is the *same*
Pulse pointer with the non-null refinement dropped, which is why passing a `C` where a `C?`
is wanted costs nothing and why the null-forgiving `x!` costs only what the surrounding
`if` already proves. It is the subject of *Recursive classes* below.

To allow the aliasing, mark the parameters `[Frac]` and split at the call site with
`Pal.Share` (§3). `SameSize([Frac("pa")] Stack a, [Frac("pb")] Stack b)` may be called on
one stack twice. What you give up is writing: a mutator needs full ownership, and calling
one on a fractional object is refused — again by Pulse, on the calling line, because
whether you have enough permission is a separation-logic question and not a syntactic one.

**A read-only method is fractional already, and you write nothing.** A method that assigns
no field is generalised over its receiver's permission automatically. A caller holding the
whole object is unaffected; a caller holding half can still call it. There is no attribute
for this because there is no decision to make: the same analysis that decides a method
preserves its object decides it needs only a fraction of it, and one analysis cannot
disagree with itself.

**An object local can alias.** `Stack t = s;` binds a second name to one object; it
allocates nothing, owns nothing, and emits nothing. Both names denote the same object
throughout, which is what makes `Pal.Share(t)` and `Pal.Share(s)` the same statement.

**Hierarchies work, to any depth.** `abstract`, `virtual` and `override` are supported: an
abstract class declares a `[Model]` and abstract methods, each subclass supplies its own
model and overrides, and a client holding a base-typed reference calls through it without
knowing the leaf. A subclass's model must *forget* to the base's, which is the one thing you
write; `doc/translation.md` §9 is the scheme and `test/deep_hierarchy` is a three-level
example. Checked downcasts (`is`/`as`) are supported and are *free* — with a precondition
strong enough to prove the cast succeeds, `x as Square` cannot fail, so it costs nothing to
prove and nothing to run.

**An ordinary open class works too.** A class may be concrete *and* extensible — with
fields, a constructor, a non-virtual method, and `virtual` methods with bodies — and
another ordinary class may derive from it and override some of them. R9.21 desugars it
into the shape above: an abstract half carrying the contracts and a generated leaf carrying
the representation and the bodies. `new C(…)` is unaffected and `: base(args)` is inlined.
One thing follows, and it is C#'s doing rather than the scheme's: a `virtual` method's
contract is the one every override must satisfy, so a caller learns only that (a
non-virtual method keeps its contract exactly). `test/open_concrete` is the example.

**A subclass may extend the model.** By default it does not: a plain `[Model]` member is
not overridable, so a subclass inherits the model whole and the forgetting function is the
identity. Mark the `[Model]` member `virtual` and the subclass may declare a `[Model]` of
its own and override the base's to say what the base's model is in terms of it — the same
two members R9.6 has always wanted, and the forgetting function becomes a projection. An
observation follows its own model: one declared alongside the base's model is reached
through the projection rather than copied down. `test/open_model` is the example.

C# `interface`
implementations are still rejected, as are generic class and struct *declarations*
(`PALCS0581`) — a class is polymorphic in pal-csharp only through the methods that
operate on it. A static mutable field is rejected too
(`PALCS0522`): it is global state that no per-object invariant covers.

**Overloads and several constructors work.** A class may declare `Temperature(int, int)`,
`Temperature(int)` and `Temperature()`, and a convenience constructor may chain to the
general one with `: this(...)`; its postcondition is then discharged from the chained
constructor's contract rather than re-proved from the fields. Methods overload too. The
only shape refused is a constructor that chains *and then does more work*
(`PALCS0598`) — the chained constructor hands the object back with its invariant already
established, so a later assignment would have to reopen it. Chain to a constructor that
does the work, or assign every field directly. `: base(...)` waits on a base class that
may have fields at all.

The generated module name grows a suffix only where it must: `Func_Temperature_Get` when
`Get` is alone, `Func_Temperature__ctor_int_int` and `Func_Temperature__ctor_unit` when
there is an overload set to separate.

Two things a class gets for free, and neither costs an annotation. A freshly constructed
object is automatically distinct from every object that already existed. And nothing is
ever freed — the CLR's garbage collector means pal-csharp inherits none of PAL's
deallocation obligations.

### Recursive classes

A class holding a field of its **own nullable type** is recursive, and it owns not one
record but the whole chain hanging off it. That needs an inductive ownership predicate — and
you do not write one. You write the `[Model]` member you already owe, and pal-csharp reads
the induction out of it backwards.

```csharp
public sealed class Node
{
    internal int value;
    internal Node? next;

    [Model] private SpecList<SpecInt> Items => SpecList.Cons(value, next!.Items);

    [Spec] public SpecList<SpecInt> Elements => Items;

    [Ensures("@this.Elements == SpecList.Cons(v, n.Elements)")]
    public Node(int v, Node? n) { value = v; next = n; }
}
```

Read left to right, `[Model]` defines `Items`. Read right to left it is the ownership
predicate: a node whose model is `hd :: tl` owns a cell whose value is `hd` and whose `next`
owns `tl`, and a null reference owns nothing and denotes `[]`. You write no `slprop`, no
`fold`, and none of the case lemmas.

**The `!` is required, and it is also the right reading.** Without it the stock C# compiler
rejects the member under `<Nullable>enable</Nullable>`, and the core guarantee is that your
file still compiles unmodified. It is not a claim that `next` is non-null: it says the
member is **total** — a null reference denotes the empty structure, so `next!.Items` is `[]`
when `next` is null and the equation holds either way. That totality is exactly what gives
the induction its base case. Nothing in a `[Model]` member is ever executed.

**The `if (x == null)` you already write is the case analysis.** There is no ghost statement
to invoke and no window to open by hand: inside the `else` branch the reference's fields are
readable and writable, by ordinary C#, and the branch is where the proof steps go.

```csharp
[Requires("n.Elements.Length < 2147483647")]
[Ensures("Result == n.Elements.Length")]
[Decreases("n.Elements")]
public static int Length([Frac("p")] Node? n)
{
    if (n == null) { return 0; }
    return 1 + Length(n.next);
}
```

Four things follow, and each is an ordinary rule rather than a rule about recursion:

* **A self-recursive method needs `[Decreases]`,** and its argument is a *model*. The
  sub-model being smaller is handed to you by the case analysis, so there is no measure
  arithmetic to write. Without one the method is refused, exactly as a `while` without a
  measure is.
* **The null test must be the whole condition of an `if`.** Inside a `&&`, or assigned to a
  `bool`, there is no branch for the case analysis to be the extent of, and it is refused.
* **A field is reachable only inside such a branch** — which is why `Length` may name
  `n.next` at all despite being a static method of another class. Outside one it is refused.
* **`[Frac]` works over a recursion.** `Length` above only reads, so it is written
  fractional and can be called by an owner that itself holds only a share.

**Destructive traversal is the point.** `x.next = Append(x.next, y)` is an ordinary field
write inside such a branch — this is the case a flat, non-inductive invariant cannot express
at all:

```csharp
[Ensures("Result.Elements == SpecList.Append(x.Elements, y.Elements)")]
[Decreases("x.Elements")]
public static Node? Append([Consumes] Node? x, [Consumes] Node? y)
{
    if (x == null) { return y; }
    x.next = Append(x.next, y);
    return x;
}
```

`[Consumes]` is what says the result owns the arguments, so neither invariant is handed
back. A **constructor** consumes its object parameters with no annotation at all: its body
may only initialise fields, so an object it is given has nowhere to go except into the
object being built. Using such a name afterwards is refused, because there is nothing left
to read out of it.

**Branch-local mutation must be written in tail position.** Two arms that leave the object
in different states cannot be joined afterwards, so each arm ends in its own `return`:

```csharp
if (t == null)          { return new TreeNode(v, null, null); }
else if (v < t.value)   { t.left  = Insert(t.left,  v); return t; }
else if (v > t.value)   { t.right = Insert(t.right, v); return t; }
else                    { return t; }
```

Two model types ship, and the rule is stated over a constructor's arity rather than over the
type.

`SpecList<T>` — `SpecList.Empty<T>()`, `SpecList.Cons(head, tail)`, `.Length`, `.Head`,
`.Tail`, `.IsEmpty`, `SpecList.Append`, `SpecList.Take`, `SpecList.Drop`,
`SpecList.InsertAt`, `SpecList.RemoveAt`, `SpecList.Reverse`.

`SpecTree<T>` — `SpecTree.Leaf<T>()`, `SpecTree.Branch(left, value, right)`, `.Size`,
`.Height`, `.IsLeaf`, `SpecTree.Elements`, `SpecTree.Insert`.

`SpecTree<SpecKv<T>>` is a **map**: `SpecTree.Entry(key, value)` builds a keyed entry, and
`SpecTree.HasKey`, `SpecTree.Get`, `SpecTree.Keys` and the three-argument `SpecTree.Insert`
read and write one. It exists because an ordered container over an unconstrained `T` has no
comparison to be ordered by; the order lives in an `int` key beside the value.

The indexing operations are **total**: a negative or oversized index clamps rather than
being ill-defined, so `SpecList.Take(xs, -1)` is empty and `SpecList.RemoveAt(xs, 99)`
removes nothing. That is deliberate — a postcondition mentioning an index must be well
formed before the precondition that bounds it has been read.

`test/linked_list` and `test/binary_tree` are the worked examples at `int`;
`test/generic_list` and `test/generic_tree` are the same libraries generic in the element.
The tree ones prove an in-place BST insert equal to the mathematical insertion, which is
full functional correctness rather than "the result is still a tree".

**What is refused, rather than approximated.** A recursive class that also takes part in a
hierarchy, or that owns an array; a `[Model]` that is not a single constructor application,
or that does not use each recursive field exactly once; *iterative* traversal of a recursive
structure; mutual recursion between two classes; and `[Backward]` — a `prev` pointer. That
last one is not owned but *constrained*, and while the Pulse shape for it is verified in
`test/pulse_facts/RecursiveFacts.fst`, the surface rule that would supply a new node's
predecessor is not, and pal-csharp does not guess.

---

## 4. Specification functions

`[Spec]` marks a pure function usable in contracts. Its body is real C#, translated, not an
opaque string.

```csharp
[Spec]
public static bool Sorted(Seq<int> s, SpecInt lo, SpecInt hi) =>
    Pal.Forall((SpecInt i, SpecInt j) =>
        Pal.Implies(lo <= i && i < j && j < hi && j < s.Length, s[i] <= s[j]));

[Spec(Recursive = true)]
[Decreases("n")]
public static SpecInt SumUpTo(SpecInt n) => n <= 0 ? 0 : n + SumUpTo(n - 1);
```

A `[Spec]` function's parameters *and its result* get the **specification** reading: `int`
is a mathematical integer, `T[]` and `Seq<T>` are both ghost sequences, a `bool` result is
a proposition. Use `SpecInt` / `SpecNat` when you mean an unbounded integer and want to say
so. Because an `int`-returning `[Spec]` denotes a mathematical value, it composes with
arithmetic and may be used as an array index in a contract.

**A contract may only call `[Spec]` and `[Lemma]` methods** — never an executable one, which
has a heap effect and no meaning as a term. When you want to say something about what an
executable method computes, give it a pure model and tie the two together:

```csharp
[Spec]
public static int At(int start, int i, int capacity) =>
    start + i < capacity ? start + i : start + i - capacity;

[Ensures("Result == At(start, i, capacity)")]
public static int Wrap(int start, int i, int capacity) { … }
```

Without that `Ensures`, a caller of `Wrap` would learn only that the result is in range — a
type property. With it, the caller knows *which* index it is, which is the property the
rest of the proof needs.

**A `[Spec]` function may be defined in F*** when its theory is proved there:
`[Spec][PulseBody("HashChain.wf $(buckets) $(entries)")] static bool Wf(Seq<int> buckets,
Seq<Entry> entries) => throw new InvalidOperationException();`. The text is the definition,
with `$(p)` for a parameter; the C# body is not looked at (translation.md R24.17).

**Keep a predicate total if a loop invariant will mention it.** A `[Requires]` on a `[Spec]`
function becomes a refinement that must be discharged *wherever the predicate appears* —
including when the loop invariant is first established, where the counter is often still
out of range. Fold the bounds into the quantifier's antecedent instead, as `Sorted` does
above: well-typedness of `s[i]` then follows from the antecedent.

---

## 5. Lemmas

A lemma is a proof step. It is declared as a method and **applied by calling it**:

```csharp
[Lemma]
[Requires("0 <= j && j + 1 < Contents(a).Length")]
[Ensures("IsPermutation(SetAt(Contents(a), j + 1, x), " +
         "SetAt(SetAt(Contents(a), j + 1, Contents(a)[j]), j, x))")]
[PulseBody("Pulse.Lib.CSharp.Seq.upd_shift_is_permutation $(a) (I32.v $(j)) $(x)")]
[Conditional("PAL")]
public static void UpdShift(int[] a, int j, int x) { }

// at the point of use, in ordinary C#:
SeqLemmas.UpdShift(a, j, key);
```

This is the headline ergonomic difference from PAL, where the same step is
`_ghost_stmt(Mod.lemma $(head));`. Here it is a method call: type-checked, refactorable,
findable by "find all references", and erased at runtime.

A lemma's parameters keep the **program** reading (`int` is `Int32.t`), because a lemma
talks about the values the program actually holds. Its body may be C#, or raw F\* via
`[PulseBody]`, or absent under `[Admit]` — which is reported as a warning, because an
admitted lemma is assumed rather than proved.

| Attribute | Meaning |
|---|---|
| `[Lemma]` | this method is a proof step; must return `void` |
| `[PulseBody(s)]` | supply the proof as raw F\*/Pulse |
| `[Admit]` | assume the contract; warned about |
| `[Rlimit(n)]` | give the method's proof `n` times the solver budget (R22.31) |
| `[GhostArg(d)]` | an extra erased parameter, for ghost types with no C# surface |

Inside a `[PulseBody]`, `$(x)` is the Pulse term standing for the C# name `x`. A **type**
parameter is such a name: `$(T)` is how a generic lemma says which type it is about, and it
is needed whenever the lemma's value arguments do not already determine it — an
introduction rule for the empty case of a predicate, say.

### 5.1 Lemmas that move ownership

A lemma whose contract mentions any `SlProp` clause is a **ghost function**: it consumes the
resources in its `[Requires]` and produces those in its `[Ensures]`, exactly as a `[Lemma]`
over pure propositions consumes and produces facts. Nothing in the syntax changes — the
translator notices the `SlProp` and emits a Pulse `ghost fn` instead of an F\* `Lemma`.

```csharp
[Lemma]
[Requires("Dll.Seg(from, prev, to, last, xs)")]
[Requires("!xs.IsEmpty && from == node")]
[Ensures("Dll.Opened(from, node, prev, to, last, xs)")]
[PulseBody("DllSeg.seg_open $(from) $(node) $(prev) $(to) $(last) $(xs)")]
[Conditional("PAL")]
public static void Open(DNode? from, DNode node, DNode? prev, DNode? to, DNode? last,
                        Ghost<SpecList<SpecInt>> xs) { }
```

Two conventions matter here and nowhere else:

* A ghost parameter is declared `Ghost<T>`, not `T` — `Ghost<SpecList<SpecInt>> xs` above.
* A parameter that will carry a *mathematical* integer into an `SlProp` should be declared
  `SpecInt`, not `int`, since that is what a C# `int` becomes in specification position.

This is the shape §9 uses to give a user-defined ownership predicate a C# face.

---

## 6. Ghost data

```csharp
public static int Lookup(int[] a, int i, Ghost<Seq<int>> shadow = default) { … }
```

`Ghost<T>` is an empty `readonly struct` with an implicit conversion from `T`, so a caller
may pass a real value, or omit the argument entirely. It erases to a Pulse implicit
(`#shadow: erased t`).

Ghost parameters must come last, so that callers can omit them. A ghost argument is
resolved by unification, which means one that appears **only** in the pure part of a
contract cannot be inferred, and such a method cannot currently be called from translated
C# (`translation.md` §8).

In a *spec string* you write the parameter's name and nothing else — `[Ensures("result ==
xs.Length")]` — because a spec string is bound against parameters that are already
unwrapped. In a *statement*-position specification (`Pal.Invariant`, `Pal.Decreases`, a
`[Lemma]` argument) you are writing ordinary C#, where `Ghost<T>` is a real type, so write
`xs.Value`. The `.Value` is transparent: it means exactly what `xs` means.

A `Ghost<T>` *local*, initialised and never assigned, is a snapshot: `Ghost<Seq<int>> before
= Pal.Contents(a);` names the contents at that point for later ghost statements, and has no
run-time existence (translation.md R24.12).

---

## 7. Raw Pulse

Escape hatches, in increasing order of bluntness.

| Construct | Emits |
|---|---|
| `Pal.InlinePulse("…")` | a verbatim Pulse expression, in specification position |
| `Pal.GhostStmt("…")` | a verbatim Pulse statement |
| `[PulseBody("…")]` | a verbatim body for a `[Lemma]` or `[Spec]` |
| `[PulseType("…")]` on a struct | maps the C# type onto a Pulse type |
| `[assembly: IncludePulse("M", "…")]` | a whole verbatim module `M.fst` |
| `[assembly: IncludePulseFile("M.fst")]` | the same, read from a file beside the source |

Prefer `IncludePulseFile` to `IncludePulse` for anything longer than a couple of lines: a
`.fst` in your source tree is an ordinary F\* file, so your editor highlights it, F\*'s IDE
mode checks it, and errors point at it rather than into the middle of a string literal. The
module name is the file's base name; the path is resolved relative to the file carrying the
attribute.

Inside any raw-Pulse string, PAL's antiquotation syntax works unchanged:

| Syntax | Expands to |
|---|---|
| `$(e)` | the translation of the C# expression `e` |
| `$&(x)` | the address of `x` |
| `$type(T)`, `$field(f)` | the translated type / field name |
| `$fold(…)`, `$unfold(…)` | fold / unfold of a predicate |

Raw Pulse is not a failure of the design; it is where a genuinely hard proof step belongs —
at the annotation layer, in the user's file, where it can be seen and changed. What it must
not do is migrate into the translator (`translation.md` §0, rule 3).

---

## 8. Spec-only types

| Type | Pulse |
|---|---|
| `SpecInt` | mathematical `int` |
| `SpecNat` | `nat` |
| `Seq<T>` | `Seq.seq ⟦T⟧` |
| `Ghost<T>` | `erased ⟦T⟧` |
| `SlProp` | `slprop` |
| `SpecList<T>` | `list ⟦T⟧` |
| `SpecTree<T>` | `Pulse.Lib.CSharp.Tree.tree ⟦T⟧` (declared, not built in — see below) |

These exist only in specifications. A program method that mentions one in its signature is
an error (`PALCS0500`) — mark it `[Spec]`, or wrap the parameter in `Ghost<>`.

### Bringing your own

The table above is a *starting library*, not the language. `SpecList<T>` is built in
because F\*'s `list` and its theory are worth having by default; everything else on it —
including `SpecTree<T>` — is declared in ordinary C# through three attributes that any
program may use. If the structure you are specifying is an association list, a trie, a
priority queue or a protocol state machine, you declare it the same way the standard
library does, and the translator learns nothing new.

Write the type in F\* and bring it in with `[assembly: IncludePulse]` (§7):

```csharp
[assembly: IncludePulse("MyAssoc", @"
type assoc (k:eqtype) (v:Type) =
  | Empty : assoc k v
  | Entry : k -> v -> assoc k v -> assoc k v

let rec count #k #v (a: assoc k v) : nat =
  match a with Empty -> 0 | Entry _ _ rest -> 1 + count rest
")]
```

Then give it a C# face. `[SpecType]` names the F\* type; `[SpecCtor]` names a constructor,
with `Empty = true` on the one a `null` reference denotes; `[SpecOp]` names any other term,
applied to the receiver and then the arguments:

```csharp
[SpecType("MyAssoc.assoc")]
public sealed class SpecAssoc<K, V>
{
    [SpecOp("MyAssoc.count")]
    public SpecInt Count => throw new InvalidOperationException();

    [SpecOp("MyAssoc.Entry?")]          // a discriminator is an ordinary operation
    public bool IsEntry => throw new InvalidOperationException();
}

public static class SpecAssoc
{
    [SpecCtor("MyAssoc.Empty", Empty = true)]
    public static SpecAssoc<K, V> Nil<K, V>() => throw new InvalidOperationException();

    [SpecCtor("MyAssoc.Entry")]
    public static SpecAssoc<K, V> Entry<K, V>(K key, V value, SpecAssoc<K, V> rest) => throw new InvalidOperationException();
}
```

The bodies are unreachable — these are specifications, and nothing calls them at run time —
so any `throw` will do. Declare all of one type's constructors together in one class; that
is how a use of `Entry` finds out which sibling is the empty one.

The type is now usable everywhere a built-in one is, including as a recursive class's
`[Model]`, where `Empty = true` is what lets `null` mean something:

```csharp
public sealed class Pair
{
    internal int key, val;
    internal Pair? next;

    [Model]
    private SpecAssoc<SpecInt, SpecInt> Map => SpecAssoc.Entry<SpecInt, SpecInt>(key, val, next!.Map);
}

[Ensures("Result == c.Map.Count")]
[Decreases("c.Map")]
public static int Count([Frac("q")] Pair? c) => c == null ? 0 : Count(c.next) + 1;
```

Two things the translator deliberately does not do. It does not check that the F\* names
exist — a misspelling surfaces as a type error in the generated module, carrying the text
you wrote in the attribute, which is where it can be read. And it does not guess an F\*
name from a C# one: a member of a specification type used without `[SpecOp]` or
`[SpecCtor]` is `PALCS0573`, not a silently mistranslated specification.

See `test/user_spec_type` for the whole of the above as a working test.

---

## 9. Bringing your own ownership predicate

§8 lets you bring your own *spec type*. This section lets you bring your own **ownership
predicate** — what it means to own a reference — for the structures no derivation can
describe.

You need this when the shape of ownership is not a fold over the fields. The example is a
**doubly linked list segment**: it is bounded at both ends, so it carries boundary pointers
that are chosen by the specification rather than read off the data; its empty case is
`from == to`, a relation between two of them, so `x == null` is not the case split; its
`prev` field points at a cell the previous node already owns, so it can only be
*constrained* and never owned; and its key lemma — that two adjacent segments compose —
relates two instances of the predicate at once.

### `[Plain]`: a class pal-csharp derives nothing about

```csharp
[Plain]
public sealed class DNode
{
    internal int value;
    internal DNode? prev;
    internal DNode? next;
}
```

`[Plain]` emits the record, the reference and the nullable reference, and stops. There is
no `[Model]`, no invariant, no case lemmas, no constructor. Nothing is owned by virtue of a
reference's *type*: a `DNode?` parameter is a bare binder, and ownership is only ever what a
clause says.

In exchange, you may say anything. Write the predicate and its lemmas in Pulse, in an
ordinary `.fst` file beside your C# source:

```csharp
[assembly: IncludePulseFile("DllSeg.fst")]
```

```fstar
// DllSeg.fst
module DllSeg
#lang-pulse
open Pulse
module B = Pulse.Lib.Box

let rec dll_seg (p: perm) ([@@@mkey] from: Class_DNode.class_DNode__opt)
                (prev to_ last: Class_DNode.class_DNode__opt) (l: list int)
  : Tot slprop (decreases l)
  = match l with
    | [] -> pure (from == to_ /\ prev == last)
    | hd :: tl -> exists* v r. ...

unfold
let seg (from prev to_ last: Class_DNode.class_DNode__opt) (l: list int) : slprop =
  dll_seg 1.0R from prev to_ last l
```

Two conventions matter. The class module is `Class_<Name>`, its record `class_<Name>__raw`,
its nullable reference `class_<Name>__opt` (a `Pulse.Lib.Box.box` of the record — already
nullable, so `B.null` and `B.is_null` apply), its non-null reference `class_<Name>` (the
refinement `b: class_<Name>__opt { not (B.is_null b) }`), and its fields `fld_<name>` — that
is the whole of what `[Plain]` publishes. Because the two reference types are one type and a
refinement, a lemma you write takes a cursor **once**: the pointer a contract talks about is
the pointer a field read goes through. And the friendly wrapper you
name from C# should be `unfold`, so that Pulse's resource matching (which is syntactic)
still sees `dll_seg` and every lemma you wrote about it applies.

(`[assembly: IncludePulse("DllSeg", "…")]` takes the same text as a string literal, and is
what you want for two or three lines. For anything larger use the file form: you get syntax
highlighting, F\*'s IDE mode, and errors that point at F\* source rather than into the middle
of a C# string.)

### `SlProp` clauses

A `[SpecOp]` returning `SlProp` is an *ownership* clause: where it appears in a contract it
joins the separating conjunction rather than the `pure`.

```csharp
public static class Dll
{
    [SpecOp("DllSeg.seg")]
    public static SlProp Seg(DNode? from, DNode? prev, DNode? to, DNode? last,
                             SpecList<SpecInt> values) => throw new InvalidOperationException();
}
```

```csharp
[Requires("Dll.Seg(from, prev, null, last, xs)")]
[Ensures("Dll.Seg(from, prev, null, last, xs)")]
[Ensures("Result == xs.Length")]
[Decreases("xs")]
public static int Length(DNode? from, DNode? prev, DNode? last,
                         Ghost<SpecList<SpecInt>> xs = default)
```

### In the body

A `[Plain]` reference behaves the way the encoding does and no more:

* `if (from == null) { … } else { … }` is `if (None? from)`. **No lemma is placed** — there
  is no derived predicate to case-split, so if your predicate needs a case split, call your
  own `cases` lemma first. That restriction is the point: for a general segment, emptiness
  is `from == to`, not `from == null`.
* Inside the `else` branch the reference is known non-null, so `from.next` and
  `from.prev = node` are the ordinary box read and box write. Whether they are *owned* is
  your predicate's business; a missing `pts_to` shows up as a proof failure you fix in your
  annotations.
* `new DNode { value = v, prev = null, next = head }` allocates. **Object-initializer syntax
  only** — a constructor call is refused, because reading a constructor body to learn which
  argument lands in which field is exactly the deriving `[Plain]` opts out of.
* Proof steps are **ordinary C# calls** to the ghost lemmas your predicate publishes (§5.1).

### One lemma per step

The style rule that makes the above workable: *a user predicate publishes one ghost lemma per
step a C# body takes, whose signature mentions only what C# can name — parameters, locals,
`null`, spec lists — and keeps every `with` and every `rewrite` inside the `.fst` file.*

```csharp
DllProof.Cases(from, prev, last, xs);
if (from == null) { return 0; }
DllProof.Open(from, from!, prev, null, last, xs);
int rest = Length(from.next, from, last);
DllProof.Close(from, from!, prev, null, last, xs);
return rest + 1;
```

The one thing the lemmas have to absorb is that C# cannot declare a refined binder. A
predicate stated over a nullable cursor needs, at the point a field is read, to talk about
the *box*; so have it **name the head node twice** — once as the cursor the contract already
mentions and once as the box — tied by a `pure (from == Some v)`:

```fstar
unfold
let opened (from: class_DNode__opt) (v: class_DNode)
           (prev to_ last: class_DNode__opt) (l: list int) : slprop
  = exists* r tl.
      B.pts_to v r **
      dll_seg 1.0R r.fld_next from to_ last tl **
      pure (from == Some v /\ l == I32.v r.fld_value :: tl /\ r.fld_prev == prev)
```

The call site then writes `DllProof.Open(from, from!, …)`, supplying both. `from!` is C#'s
null-forgiving operator, which the C# compiler already demands in order to pass a `DNode?`
where a `DNode` is declared; pal-csharp reads the same declaration and projects. Inside an
`if (from != null)` branch, where C# narrows the type for you, plain `from` means exactly the
same thing.

Writing `head.prev = node` and having it cost nothing is the payoff: because the predicate
only ever constrained `prev` with an equation, re-closing the segment simply reports what
the field now holds.

`Pal.GhostStmt("…")` (§7) remains available for a step you have not bothered to publish as a
lemma — `unreachable ()` in a dead branch is the usual one.

`[Plain]` may not be combined with `[Model]` (`PALCS0574`), and a `[Plain]` class may not
take part in a hierarchy (`PALCS0575`).

The honest caveat: a segment operation still costs four or five explicit proof steps. What
this buys you is that they are typed C# calls to lemmas someone wrote once, rather than
`rewrite`s every caller has to rediscover. Reach for `[Plain]` when §3's recursive classes
will not do, and not before.

See `test/dll_segment` for the whole of the above as a working test.

---

### `[Region]`: tree nodes owned as one region

```csharp
public sealed class SearchTree<T>
{
    private readonly IComparer<T> comparer;
    private Node? root;

    [Model]
    private TreeModel<T> Model => new TreeModel<T> { Nodes = Pal.Tree<(T, bool)>(root), Comparer = comparer };

    [Region]
    internal sealed class Node
    {
        public T Item;
        public Node? Left;
        public Node? Right;
        public bool IsRed;

        [Model]
        private (T, bool) View => (Item, IsRed);
    }
}
```

A `[Region]` class is a node type whose objects belong, all together, to whichever object
holds a field of that type. That object's invariant owns a ghost heap of every node (a
*region*), so nodes may be reached by several pointers at once, as in a red-black tree's
top-down re-linking. The class must be `sealed` and must declare exactly two nullable fields
of its own type: the left and right children, in declaration order. Its optional `[Model]`
is the *view* of one node. The class has no methods of its own.

In the owner's model and contracts, and in loop invariants:

* `Pal.Tree<V>(x)` is the `SpecTree<V>` of views reached from `x`;
* `Pal.WellFormed(x)` says every path from `x` ends at `null`.

A loop down the tree reads like this:

```csharp
Node? current = root;
while (current != null)
{
    Pal.Decreases(Pal.Tree<(T, bool)>(current).Size);
    Pal.Invariant(Pal.Implies(!Pal.Returned(), Pal.WellFormed(current) &&
                  SpecSearchTree.Contains(comparer, Pal.Tree<(T, bool)>(current), item) ==
                  SpecSearchTree.Contains(comparer, Pal.Tree<(T, bool)>(root), item)));
    ...
    current = order < 0 ? current.Left : current.Right;
}
```

The guard `!Pal.Returned()` is needed when the body can `return`: the iteration that
returns leaves `current` unconstrained (doc/translation.md R27.10).

`PalLang.SpecSearchTree` has the searches over a `SpecTree<(T, TTag)>`: `Contains`,
`Find`, `Leftmost`, `Rightmost` and `HeapIndex`. Each follows the path the code follows, so
none needs an ordering hypothesis.

An owner of a region is always held whole (no `Pal.Share`). `new Node(...)` is not yet
supported. See doc/translation.md §27.

## 10. Generics

### 10.1 Methods

A method may be generic, provided its type parameters are **unconstrained**:

```csharp
[Requires("0 <= i && i < a.Length")]
[Requires("0 <= j && j < a.Length")]
[Ensures("Contents(a) == SetAt(SetAt(Old(Contents(a)), i, Old(Contents(a))[j]), j, Old(Contents(a))[i])")]
public static void Exchange<T>(T[] a, int i, int j)
{
    T x = a[i];
    T y = a[j];
    a[i] = y;
    a[j] = x;
}
```

Nothing here is new syntax: `T` is an ordinary C# type parameter, it may be used as a
type in the signature, in locals and in specifications, and callers write the call they
would write anyway — the type argument may be inferred or spelled out, and either way it
is Roslyn that resolves it.

An unconstrained `T` admits no operation but moving the value around, which is precisely
what makes these specifications *complete* rather than partial: with no arithmetic and no
comparison available, the result sequence is determined by the input sequence, and the
postcondition can say so exactly.

Two restrictions:

* **A constraint is rejected** (`PALCS0580`). `where T : IComparable<T>` is a typeclass
  obligation — every call site must supply a dictionary, and dispatch through it is a
  translation pal-csharp has not designed. Write the method at the concrete type instead.
* **A generic `struct` is rejected** (`PALCS0581`). A struct is a value here — copied at
  every assignment, stored inline in whatever holds it — and its representation record has
  not been designed with a type parameter. Write it at the element type you need, or make
  it a class.

### 10.2 Classes

A class may be generic on the same terms:

```csharp
public sealed class Cell<T>
{
    internal T value;
    internal Cell<T>? next;

    [Model] private SpecList<T> Items => SpecList.Cons(value, next!.Items);
    [Spec]  public SpecList<T> Elements => Items;

    [Ensures("@this.Elements == SpecList.Cons(v, n.Elements)")]
    public Cell(T v, Cell<T>? n) { value = v; next = n; }
}
```

Everything §3 says about a recursive class applies unchanged — the `[Model]` is still one
constructor application using each recursive field once, the null test still opens the
window, `[Consumes]` and `[Frac]` still mean what they meant. The type parameter is simply
carried along.

Callers write the call they would write anyway; a method of a generic class is generic in
the class's parameters as well as its own, and Roslyn resolves both.

Two things are worth knowing:

* **`==` is not available on an unconstrained `T`**, so a specification about a value of
  type-parameter type says `Pal.Same(a, b)` instead. It means `==` and nothing else.
* **An ordered container is keyed, not compared.** `where T : IComparable<T>` is refused
  (`PALCS0580`), so `test/generic_tree` is a `TreeNode<T>` with an `int key` and a `T
  value` — a map, fully general in what it stores, needing no comparison on `T` at all.

`test/generic_list` and `test/generic_tree` are complete libraries in this style: length,
concatenation, copy, take, drop, insert-at, remove-at and reverse for the list; size,
height, containment, lookup, insert and copy for the tree. Most of them are **persistent** —
they allocate what they return and leave the argument `[Frac]`-observed — because an
operation that rebuilds its result is the one whose ownership is simplest to state, and
because that is the ordinary contract of a container operation in a garbage-collected
language.

The destructive operations are the ones with nothing to allocate: `Prepend` and `Concat`
for the list, `Insert` for the tree. Three shapes are *not* expressible today, and the
reasons are §3's rather than §10's: reading a field through a **non-null** reference (there
is no null test to open the window at), passing a reference to a call **while its window is
open**, and giving a `[Consumes]` parameter away on **two different paths** of the same
method. `doc/translation.md` §15.5 records each with the rule that would lift it.

## 11. What is rejected

pal-csharp refuses rather than mistranslates. Every rejection is a diagnostic with a source
span, collected in `diagnostics.json` alongside the generated modules, and every error also
writes `assert False` into `TranslationErrors.fst`, so a failed translation can never be
mistaken for a passing proof.

### `Span<T>` and `ReadOnlySpan<T>`

A span is a **borrowed window** into somebody else's memory. Writing a method that takes
one is no different from writing one over an array — `s.Length`, `s[i]`, `s[i] = x`, a
counted loop and a `Contents(s)` contract all behave as you expect, and the bounds
obligations are the same. `ReadOnlySpan<T>` is read-only, so it takes a fractional
permission whether or not you write `[Frac]`; write `[Frac]` only when two parameters must
share one array by name.

```csharp
[Requires("0 <= i && i < Contents(a).Length")]
[Ensures("Result == Contents(a)[i]")]
public static int Read(ReadOnlySpan<int> a, int i) => a[i];
```

**Creating a span borrows.** `a.AsSpan(from, count)`, `s.Slice(i, n)`, `s[i..j]` and the
implicit `int[]` → `Span<int>` conversion all take ownership away from the source for as
long as the window is out — so while `w` exists, `a` cannot be indexed.

**`Pal.Restore(w)` gives it back**, and you write it, because C# has nowhere to put it:
ending a borrow has no runtime content, so it is a proof step like any other. Afterwards
the source holds `Pal.Splice(old, from, to, window)` — its old contents with the window's
range replaced — which is what lets you say both what the window did and what it left
alone:

```csharp
[Requires("0 <= from && 0 <= count && from + count <= Contents(a).Length")]
[Ensures("Contents(a).Length == Old(Contents(a)).Length")]
[Ensures("Forall((int k) => Implies(from <= k && k < from + count, Contents(a)[k] == 0))")]
[Ensures("Forall((int k) => Implies(0 <= k && k < Contents(a).Length && " +
         "(k < from || from + count <= k), Contents(a)[k] == Old(Contents(a))[k]))")]
public static void ClearRange(int[] a, int from, int count)
{
    Span<int> w = a.AsSpan(from, count);
    Clear(w);            // written once, over a span; works on any window of any array
    Pal.Restore(w);
}
```

Forget the restore and the postcondition about `a` will not prove — the window still holds
the memory. Write it too early and the next use of `w` will not prove. Windows nest, and
are restored innermost first, which is not a rule anybody wrote down: the outer window's
ownership is inside the inner one until you give it back.

Refused with `PALCS0590`: `stackalloc` (an allocation, not a borrow); `a[1..3]` on an
*array*, which in C# **copies** rather than windowing; `^k` in a range; the implicit
`int[]` → `Span<int>` conversion anywhere but a local's initializer (name the borrow and
pass the name); `Pal.Restore` of a span *parameter*, which somebody else borrowed; and
assigning to a span local after its declaration — a second window gets a second name.

And a **loop invariant** over a span cannot use `Pal.Forall` directly, because C# refuses a
`ref struct` inside a lambda (CS9108). Contracts are fine — they are bound elsewhere — but
inside a body, name the predicate:

```csharp
[Spec]
public static bool ZeroBelow(Seq<int> s, SpecInt n) =>
    Pal.Forall((int k) => Pal.Implies(0 <= k && k < n && k < s.Length, s[k] == 0));

// ... in the loop:
Pal.Invariant(ZeroBelow(Pal.Contents(a), i));
```

That moves `Pal.Contents(a)` out of the lambda and into an argument, which C# allows. See
`test/array_view`.

Currently outside the supported subset: `stackalloc`, a span-typed return, `goto`,
`try`/`catch`/`throw`, **constrained** type parameters (unconstrained ones are supported,
as are generic classes), C# `interface` declarations, delegates, `async`, `foreach` and
`IEnumerable<T>`, `string`, floating point, struct fields that are not values,
user-written struct constructors, static mutable fields, a class that is neither `sealed`
nor `abstract`, a `return` that is not in tail position **inside a loop**, an increment or
decrement written in a specification, a `switch` label that is a pattern or carries a
`when` guard, and a `break` that leaves a `switch` before the end of its section, and a method body that both
reads a field of a *view* receiver and calls a method on that same receiver (R4.10c; for an
object, R22.15 admits it).

A computed property — a property whose getter has a body, as opposed to an auto-property or
a `[Spec]` property — **is** inside the subset: R9.20 translates it as the method its getter
is, and it emits the same Pulse a method with the same body emits. A `set` accessor is not,
because C# names its parameter `value` rather than the author naming it, and no
specification can be written over a name the author did not choose. (Under
`[TranslateAnnotatedOnly]`, translation.md §22 admits setters, indexers and `const` fields
for verifying library code in place, with `value` named in the setter's contracts.)

Also outside the subset, and until §18 each of these was *silently dropped* rather than
reported: a property with a `set` accessor, an indexer, a `const` field, an explicit interface
implementation, a user-defined operator or conversion, an event, a finalizer, an `override`
of a member of `object` (`Equals`, `GetHashCode`, `ToString`), two members of one program
whose generated module names collide (R2.1a resolves an overload set; two same-named types
in different namespaces it does not), a constructor that chains and then does more work, an `implements` clause, a call to a method not declared in this compilation
(including any BCL method), `==`/`!=` on class-typed operands, and an annotated `record`.
`doc/translation.md` §18.2 says what each is waiting for.

`switch` itself is supported: R5.14 desugars it to an if/else chain, evaluating the
governing expression once and moving `default` to the end. What it does not cover is
everything about `switch` that is not a comparison against a constant. `goto case` and
`goto default` are refused specifically: C# forbids implicit fallthrough, which is what
makes the chain a faithful target, and these two are the exception that asks to enter one
arm from inside another. The diagnostic names the two rewrites — stack the labels where
the other section should run *instead*, factor out a method where it should run *as
well*.

Two entries left this list in M7. Conversions between machine-integer widths — explicit
casts and C#'s implicit promotions alike — are translated by §13's R13.1 and R13.4. A
`return` that is not in tail position is rewritten by Normalize (R5.5b) everywhere except
inside a loop. Increment and decrement in expression position, including
`a[i++]`, are translated by R13.3.

For a recursive class (§3): a hierarchy it also takes part in, an array it also owns, a
`[Model]` that is not one constructor application over each recursive field exactly once,
mutual recursion between two classes, an iterative rather than recursive traversal, a null
test that is not the whole condition of an `if`, a field named outside such a test, a
self-recursive method with no `[Decreases]`, a use of a name whose ownership has moved, and
`[Backward]`.

Within the subset, the proof obligations are: no arithmetic overflow, no out-of-bounds
index, no null dereference, no division by zero. C# defines the first as wrapping and turns
the rest into exceptions; pal-csharp proves none of them happen, which is stronger than
C#'s guarantee and matches PAL's treatment of the corresponding undefined behaviour.

---

## 12. A complete example

```csharp
using PalLang;

public static class SortedSpec
{
    [Spec]
    public static bool Sorted(Seq<int> s, SpecInt lo, SpecInt hi) =>
        Pal.Forall((SpecInt i, SpecInt j) =>
            Pal.Implies(0 <= i && lo <= i && i < j && j < hi && j < s.Length, s[i] <= s[j]));
}

public static class Sorting
{
    [Ensures("Contents(a).Length == Old(Contents(a)).Length")]
    [Ensures("SortedSpec.Sorted(Contents(a), 0, Contents(a).Length)")]
    [Ensures("IsPermutation(Contents(a), Old(Contents(a)))")]
    public static void InsertionSort(int[] a) { … }
}
```

`test/insertion_sort_sorted` contains this in full: the ordinary two-nested-loop insertion
sort, proved to produce a sorted rearrangement of its input. Its proof is four loop
invariants, four `Pal.Assert` steps and one `[Lemma]` call — all of it in the `.cs` file.
