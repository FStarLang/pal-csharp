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
`null`, so no method needs a null check to satisfy the translator. A `C?` is a different
type and is the subject of *Recursive classes* below.

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

Every class must be **`sealed` or `abstract`** (`PALCS0521`). A leaf owns a representation
and an abstract base owns a vtable; a class that were both would have to be its own
subclass's vtable type and one of that type's values at once. C# `interface`
implementations are still rejected, as are generic class and struct *declarations*
(`PALCS0581`) — a class is polymorphic in pal-csharp only through the methods that
operate on it. A static mutable field is rejected too
(`PALCS0522`): it is global state that no per-object invariant covers.

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

In exchange, you may say anything. Write the predicate and its lemmas in Pulse:

```csharp
[assembly: IncludePulse("DllSeg", """
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
""")]
```

Two conventions matter. The class module is `Class_<Name>`, its record `class_<Name>__raw`,
its reference `class_<Name>`, its nullable reference `class_<Name>__opt`, and its fields
`fld_<name>` — that is the whole of what `[Plain]` publishes. And the friendly wrapper you
name from C# should be `unfold`, so that Pulse's resource matching (which is syntactic)
still sees `dll_seg` and every lemma you wrote about it applies.

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
* Proof steps are `Pal.GhostStmt("DllSeg.dll_seg_elim_cons 1.0R $(from) …")`, with `$(x)`
  splicing the Pulse name of a C# variable and `with r tl. assert (…)` naming what a lemma
  existentially quantified.

Writing `head.prev = node` and having it cost nothing is the payoff: because the predicate
only ever constrained `prev` with an equation, re-closing the segment simply reports what
the field now holds.

`[Plain]` may not be combined with `[Model]` (`PALCS0574`), and a `[Plain]` class may not
take part in a hierarchy (`PALCS0575`).

The honest caveat: a segment operation costs five or six ghost lines, most of them
`rewrite`s that talk the boundary pointers into the shape the next lemma expects. Reach for
`[Plain]` when §3's recursive classes will not do, and not before.

See `test/dll_segment` for the whole of the above as a working test.

---

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

Currently outside the supported subset: `Span<T>` and `ReadOnlySpan<T>` (planned), `goto`,
`try`/`catch`/`throw`, constrained type parameters, generic type declarations, C#
`interface` declarations, delegates, `async`,
`string`, floating point, struct fields that are not values, user-written struct
constructors, static mutable fields, a class that is neither `sealed` nor `abstract`, a
`return` that is not in tail position **inside a loop**, an increment or decrement
written in a specification, a `switch` label that is a pattern or carries a `when` guard,
and a `break` that leaves a `switch` before the end of its section.

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
