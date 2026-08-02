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
| `s.Length`, `s[i]` on a `Seq<T>` | length and indexing of a ghost sequence |
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

### 2.1 `break` and `continue`

Both are supported. One limitation is worth stating up front: the flag the translation uses
is internal, so an invariant cannot mention it, and a postcondition **cannot say that the
loop ran to completion**. If your contract needs that, carry the exit condition in the
guard instead — `while (i < n && !done)` rather than `if (…) break;`. `test/compare_elements`
does exactly this and says why.

---

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

**Not yet implemented.** This is the planned surface; the translation scheme behind it is
`doc/translation.md` §3.4 and §4.5, and every Pulse shape it relies on is already verified
in `test/pulse_facts/ObjectFacts.fst`. It is written down here so that the design can be
argued with before the code exists.

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
boundary sharp is why the frontend is small. Ownership also means a live object is never
`null`, so no method needs a null check to satisfy the translator.

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

**M2 is `sealed` classes only.** `virtual`, `abstract`, `override` and interface
implementations are rejected (`PALCS0521`), because a per-class invariant cannot express
behavioural subtyping. A static mutable field is rejected too (`PALCS0522`): it is global
state that no per-object invariant covers.

Two things a class gets for free, and neither costs an annotation. A freshly constructed
object is automatically distinct from every object that already existed. And nothing is
ever freed — the CLR's garbage collector means pal-csharp inherits none of PAL's
deallocation obligations.

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
| `[GhostArg(d)]` | an extra erased parameter, for ghost types with no C# surface |

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

These exist only in specifications. A program method that mentions one in its signature is
an error (`PALCS0500`) — mark it `[Spec]`, or wrap the parameter in `Ghost<>`.

---

## 9. What is rejected

pal-csharp refuses rather than mistranslates. Every rejection is a diagnostic with a source
span, collected in `diagnostics.json` alongside the generated modules, and every error also
writes `assert False` into `TranslationErrors.fst`, so a failed translation can never be
mistaken for a passing proof.

Currently outside the supported subset: `Span<T>` and `ReadOnlySpan<T>` (planned), `goto`,
`try`/`catch`/`throw`, `class` instances (**specified but not implemented** — see
§3 Classes), generics, interfaces, delegates, `async`, `string`, floating point, numeric
conversions between machine-integer widths, struct fields that are not values,
user-written struct constructors, and a `return` that is not in tail position.

Within the subset, the proof obligations are: no arithmetic overflow, no out-of-bounds
index, no null dereference, no division by zero. C# defines the first as wrapping and turns
the rest into exceptions; pal-csharp proves none of them happen, which is stronger than
C#'s guarantee and matches PAL's treatment of the corresponding undefined behaviour.

---

## 10. A complete example

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
