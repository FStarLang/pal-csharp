using System;

namespace PalLang;

// ---------------------------------------------------------------------------
// Contracts on declarations.
//
// Attribute arguments must be compile-time constants in C#, so predicates are
// carried as strings. They are NOT opaque: the translator parses each string
// with SyntaxFactory.ParseExpression and binds it with Roslyn in the scope of
// the annotated member, so parameters, locals, `[Spec]` functions, `Old`,
// `Result` and `this` all resolve and are type-checked.
//
// A contract may also be written on a property. R9.20 translates a computed
// property as the method its getter is, and C# does not permit an attribute on
// an accessor, so the property declaration is the only place the contract of
// that method can go.
// ---------------------------------------------------------------------------

/// <summary>A precondition. The predicate is a C# expression in the scope of the member.</summary>
[AttributeUsage(AttributeTargets.Method | AttributeTargets.Constructor | AttributeTargets.Property,
                AllowMultiple = true)]
public sealed class RequiresAttribute(string predicate) : Attribute
{
    public string Predicate { get; } = predicate;

    /// <summary>
    /// R32.13. When set to a view class (a sealed subclass nested in this member's class),
    /// the clause belongs to the replica of this member verified at the view, where
    /// <c>@this</c> is the view, and not to the member itself.
    /// </summary>
    public Type? At { get; set; }
}

/// <summary>
/// A postcondition. May use <c>Old(e)</c> for the pre-state value of <c>e</c>
/// and <c>Result</c> for the returned value.
/// </summary>
[AttributeUsage(AttributeTargets.Method | AttributeTargets.Constructor | AttributeTargets.Property,
                AllowMultiple = true)]
public sealed class EnsuresAttribute(string predicate) : Attribute
{
    public string Predicate { get; } = predicate;

    /// <summary>
    /// R32.13. When set to a view class (a sealed subclass nested in this member's class),
    /// the clause belongs to the replica of this member verified at the view, where
    /// <c>@this</c> is the view, and not to the member itself.
    /// </summary>
    public Type? At { get; set; }
}

/// <summary>
/// R19.2. The method may throw <paramref name="exception"/> (or a subclass of it), and
/// when it does, <paramref name="predicate"/> holds. The predicate is written over the
/// parameters and <c>Thrown</c>, the exception object, typed at
/// <paramref name="exception"/>. A method with no <c>[Throws]</c> must be proved not to
/// throw at all.
/// </summary>
[AttributeUsage(AttributeTargets.Method | AttributeTargets.Constructor | AttributeTargets.Property,
                AllowMultiple = true)]
public sealed class ThrowsAttribute(Type exception, string predicate = "true") : Attribute
{
    public Type Exception { get; } = exception;
    public string Predicate { get; } = predicate;

    /// <summary>
    /// R27.57. When set, the clause belongs to the replica of this inherited member that is
    /// verified at the subclass <c>At</c> (whose override the body reaches), not to the
    /// member itself.
    /// </summary>
    public Type? At { get; set; }
}

/// <summary>Shorthand for <c>[Requires(p)] [Ensures(p)]</c>.</summary>
[AttributeUsage(AttributeTargets.Method | AttributeTargets.Property, AllowMultiple = true)]
public sealed class PreservesAttribute(string predicate) : Attribute
{
    public string Predicate { get; } = predicate;
}

/// <summary>Shorthand for <c>[Ensures("x == Old(x)")]</c>.</summary>
[AttributeUsage(AttributeTargets.Method | AttributeTargets.Property, AllowMultiple = true)]
public sealed class PreservesValueAttribute(string expression) : Attribute
{
    public string Expression { get; } = expression;
}

/// <summary>A termination measure for a recursive method.</summary>
[AttributeUsage(AttributeTargets.Method, AllowMultiple = false)]
public sealed class DecreasesAttribute(string measure) : Attribute
{
    public string Measure { get; } = measure;
}

// ---------------------------------------------------------------------------
// Ownership. Most ownership is read off the C# type system (ref/out/in,
// T[], Span<T>, ReadOnlySpan<T>); these cover the residue.
// ---------------------------------------------------------------------------

/// <summary>Ownership is taken and not returned.</summary>
[AttributeUsage(AttributeTargets.Parameter)]
public sealed class ConsumesAttribute : Attribute;

/// <summary>
/// R27.46. The argument is not null and its dynamic type is exactly <paramref name="type"/>,
/// a translated class implementing the parameter's interface type. An open generic
/// (<c>typeof(C&lt;&gt;)</c>) is constructed at the parameter type's arguments. Every caller
/// passes an expression whose static type is that class; inside the method, the parameter
/// is an object of it, and its contracts may name the class's members on it.
/// </summary>
/// <remarks>
/// R32.13. On a method's return value, it names a view (a sealed nested subclass the
/// containing class borrows into): the method returns an object of exactly that class, and
/// its result is the view's record.
/// </remarks>
[AttributeUsage(AttributeTargets.Parameter | AttributeTargets.ReturnValue)]
public sealed class ExactlyAttribute(Type type) : Attribute
{
    public Type Type { get; } = type;
}

/// <summary>
/// Carry <em>no derived ownership</em>.
///
/// <para>On a <b>parameter</b>, this suppresses the resource the parameter's type would
/// otherwise imply: the reference is passed, and what is owned through it is whatever the
/// contract says explicitly.</para>
///
/// <para>R12.1. On a <b>class</b>, it suppresses the whole derived encoding. The translator
/// emits the representation — the record of fields, the reference, and the nullable
/// reference — and nothing else: no invariant, no model, no case lemmas, and no automatic
/// conjunct in any contract mentioning the class.</para>
///
/// <para>This is the escape hatch for structures whose ownership predicate cannot be read
/// off a <c>[Model]</c>. §10 derives the predicate from one downward fold over one
/// recursive field, which is enough for a list or a tree and not enough in general: a
/// <em>list segment</em> is bounded at both ends, so it carries boundary parameters no fold
/// over the fields could produce, and its emptiness is a relation between two of them
/// rather than a property of one. A doubly linked list needs both.</para>
///
/// <para>What a <c>[Plain]</c> class asks of the user in exchange is everything §10 would
/// have derived: the predicate, its intro and elim lemmas, and any lemma relating two
/// instances of it — written in Pulse, brought in with <see cref="IncludePulseAttribute"/>,
/// named in contracts by a <see cref="SpecOpAttribute"/> on an <c>SlProp</c>-valued member,
/// and applied in bodies with <c>Pal.GhostStmt</c>. The translator places the calls the
/// user names and derives nothing.</para>
/// </summary>
[AttributeUsage(AttributeTargets.Parameter | AttributeTargets.Class)]
public sealed class PlainAttribute : Attribute;

/// <summary>
/// R27.3. The objects of this class are owned as one <em>region</em> by whichever
/// translated class holds a field of it: a ghost heap of every node, read and written through
/// <c>Pulse.Lib.CSharp.Region</c>, so nodes may alias and be re-linked freely. The class must
/// be <c>sealed</c> and declare exactly two fields of its own type (the children, in
/// declaration order); an optional <c>[Model]</c> member is the <em>view</em> of one node,
/// which <c>Pal.Tree</c> maps over the tree a pointer reaches.
/// </summary>
[AttributeUsage(AttributeTargets.Class)]
public sealed class RegionAttribute : Attribute
{
    /// <summary>
    /// R31.1. The nodes form rings rather than trees: the two self-typed fields are the
    /// <em>next</em> and <em>previous</em> links of a circular doubly-linked list
    /// (<c>LinkedListNode&lt;T&gt;</c>). The owner's invariant does not require its pointers
    /// to be unshared trees, a read requires only that the node is in the region, and the
    /// tree intrinsics (<c>Pal.Tree</c>, <c>Pal.WellFormed</c>, <c>Pal.Unshared</c>,
    /// <c>Pal.Reshaped</c>) are refused (PALCS0780). The shape is the user's to state, through
    /// <c>SpecRing</c>.
    /// </summary>
    public bool Cyclic { get; set; }
}

/// <summary>
/// R22.14. Arithmetic that writes this integer field -- or, on a method or constructor, all the integer
/// arithmetic in its body -- wraps, as C#'s default unchecked context says it does,
/// rather than carrying R6.4's no-overflow obligation. For a counter nothing else reads
/// arithmetically -- a version stamp -- the obligation is unprovable, and for a growth
/// computation that tests for the wrap afterwards the wrap is what the code relies on.
/// </summary>
[AttributeUsage(AttributeTargets.Field | AttributeTargets.Method | AttributeTargets.Constructor)]
public sealed class WrappingAttribute : Attribute;

/// <summary>
/// Hold this parameter at an explicit fractional permission.
/// <para>
/// On a <em>method</em> it says the same thing about the receiver, which is the one
/// parameter C# gives no syntax for: the method observes <c>@this</c> rather than owning
/// it, so callers holding any fraction may call it and two aliases may call it at once.
/// R4.11b derives this from the write set for a method that has a body; an
/// <c>abstract</c> method has none, so it says so here (R9.7).
/// </para>
/// </summary>
[AttributeUsage(AttributeTargets.Parameter | AttributeTargets.Method)]
public sealed class FracAttribute(string permission) : Attribute
{
    public string Permission { get; } = permission;
}

/// <summary>
/// A back pointer: this field is <em>not</em> owned (R10.10).
/// <para>
/// A recursive class owns what its ordinary recursive fields point at. A back pointer
/// points at a cell that already belongs to the structure, so owning it would be owning it
/// twice. Marked this way, the field contributes an <em>index</em> to the class's
/// invariant and a pure equation to each node — "my predecessor is who you say it is" —
/// rather than a resource, and the <c>[Model]</c> member is excused from mentioning it.
/// </para>
/// <para>
/// At most one per class, and its type must be the class's own nullable type.
/// </para>
/// </summary>
[AttributeUsage(AttributeTargets.Field)]
public sealed class BackwardAttribute : Attribute;

/// <summary>This reference is known non-null; no null obligation is generated.</summary>
[AttributeUsage(AttributeTargets.Parameter | AttributeTargets.Field)]
public sealed class NonNullAttribute : Attribute;

// ---------------------------------------------------------------------------
// Type refinements.
// ---------------------------------------------------------------------------

/// <summary>A predicate that holds whenever a value of this type is initialized.</summary>
[AttributeUsage(AttributeTargets.Struct | AttributeTargets.Class | AttributeTargets.Field | AttributeTargets.Property,
                AllowMultiple = true)]
public sealed class RefineAttribute(string predicate) : Attribute
{
    public string Predicate { get; } = predicate;
}

/// <summary>A predicate that holds always, including when uninitialized.</summary>
[AttributeUsage(AttributeTargets.Struct | AttributeTargets.Class | AttributeTargets.Field | AttributeTargets.Property,
                AllowMultiple = true)]
public sealed class RefineAlwaysAttribute(string predicate) : Attribute
{
    public string Predicate { get; } = predicate;
}

// ---------------------------------------------------------------------------
// Objects: the model, and the object invariant.
// ---------------------------------------------------------------------------

/// <summary>
/// The abstraction function: how this object's representation is understood as a pure
/// ghost model (translation.md R3.9).
/// </summary>
/// <remarks>
/// The member's return type <em>is</em> the model type, so the model is chosen by the
/// author rather than derived by the compiler. It may be any spec-only type — a
/// <c>Seq&lt;T&gt;</c>, or a <c>[Spec]</c> struct for a product model.
///
/// This is the one member permitted to read the object's fields; every <c>[Spec]</c>
/// member is a function of the model instead. It may be <c>private</c>, because only the
/// object's own invariant consumes it (R4.10b).
///
/// Exactly one <c>[Model]</c> member is required per class; a class without one is
/// PALCS0524, since with no model every method specification collapses to memory safety.
/// </remarks>
[AttributeUsage(AttributeTargets.Property | AttributeTargets.Method)]
public sealed class ModelAttribute : Attribute;

/// <summary>
/// A predicate relating an object's fields, which every method may assume on entry and
/// must re-establish on exit (translation.md R3.10).
/// </summary>
/// <remarks>
/// This is <em>not</em> <see cref="RefineAttribute"/>. A refinement holds of every value
/// of its type at all times; an object invariant may be <em>temporarily broken</em> inside
/// a method — between two field writes, say — and is re-established at the exit. That
/// window is exactly the emitted <c>unfold</c>/<c>fold</c> bracket.
///
/// The predicate names fields as simple names, as <see cref="RefineAttribute"/> does on a
/// struct; contracts, which are written from outside, use <c>@this</c> instead (R4.10a).
///
/// It must also <em>mention</em> a field. A fact about the model alone belongs on the model
/// type as a <see cref="RefineAttribute"/>, not here — placed here it would be true but
/// unreachable, since a caller holds the invariant as an opaque predicate and cannot see
/// inside it. That is R3.9d, and it is checked (PALCS0527).
/// </remarks>
[AttributeUsage(AttributeTargets.Class, AllowMultiple = true)]
public sealed class InvariantAttribute(string predicate) : Attribute
{
    public string Predicate { get; } = predicate;
}

// ---------------------------------------------------------------------------
// Ghost, spec and lemma methods.
// ---------------------------------------------------------------------------

/// <summary>
/// A pure specification function. Its C# expression body is translated to a
/// Pulse <c>let</c>, so it is usable in contracts and in ordinary code.
/// </summary>
/// <remarks>
/// On a <c>struct</c> this instead marks a <em>spec-only type</em> (translation.md
/// R3.9a): the struct is erased, never appears in executable code, and — unlike an
/// ordinary struct (R3.4) — its fields may themselves be spec-only types such as
/// <c>Seq&lt;T&gt;</c>. That is what makes a product model expressible.
///
/// On a property of a class this marks an <em>observation</em>: a pure function of the
/// object's model (R3.9c). Its body may name the <c>[Model]</c> member and other
/// <c>[Spec]</c> members, but never a field — a caller holds only the model, so an
/// observation it cannot compute from the model is one it cannot use.
/// </remarks>
[AttributeUsage(AttributeTargets.Method | AttributeTargets.Property | AttributeTargets.Struct)]
public sealed class SpecAttribute : Attribute
{
    /// <summary>Emit as a recursive definition (requires <see cref="DecreasesAttribute"/>).</summary>
    public bool Recursive { get; init; }
}

/// <summary>
/// A lemma: a ghost method with a contract and no runtime effect. Apply it by
/// calling it like any other method; mark it <c>[Conditional("PAL")]</c> so the
/// call is erased from a normal build.
/// </summary>
[AttributeUsage(AttributeTargets.Method)]
public sealed class LemmaAttribute : Attribute;

/// <summary>Supply a raw Pulse body for a <c>[Lemma]</c> or <c>[Spec]</c> method.</summary>
[AttributeUsage(AttributeTargets.Method)]
public sealed class PulseBodyAttribute(string body) : Attribute
{
    public string Body { get; } = body;
}

/// <summary>
/// R22.31. Multiply the solver budget for this method's proof by <paramref name="factor"/>
/// (F*'s <c>--z3rlimit_factor</c>). It changes how long the proof may take, not what is proved.
/// </summary>
[AttributeUsage(AttributeTargets.Method)]
public sealed class RlimitAttribute(int factor) : Attribute
{
    public int Factor { get; } = factor;
}

/// <summary>
/// R30.40. The named <c>[Spec]</c> members of the declaring type are opaque to the SMT solver
/// while this method is checked (F*'s <c>--using_facts_from</c>): their definitions are not
/// unfolded, so what the proof knows of them comes from lemmas and from facts stated in
/// their terms. Like <see cref="RlimitAttribute"/> it changes how the proof is found, not
/// what is proved: hiding a definition can only make a proof fail.
/// </summary>
[AttributeUsage(AttributeTargets.Method)]
public sealed class OpaqueSpecsAttribute(params string[] specs) : Attribute
{
    public string[] Specs { get; } = specs;
}

/// <summary>Admit this method's contract without proof. Reported as a diagnostic.</summary>
[AttributeUsage(AttributeTargets.Method)]
public sealed class AdmitAttribute : Attribute;

/// <summary>Declare an extra erased parameter, for ghost types with no C# surface.</summary>
[AttributeUsage(AttributeTargets.Method, AllowMultiple = true)]
public sealed class GhostArgAttribute(string declaration) : Attribute
{
    public string Declaration { get; } = declaration;
}

// ---------------------------------------------------------------------------
// User-defined specification types (doc/translation.md §11).
// ---------------------------------------------------------------------------

/// <summary>
/// R11.1. Declares this type to be a specification-only type denoting the F* type
/// <paramref name="type"/>. Its C# type parameters become the F* type's arguments, in
/// order, so <c>SpecAssoc&lt;K, V&gt;</c> with <c>[SpecType("M.assoc")]</c> denotes
/// <c>M.assoc ⟦K⟧ ⟦V⟧</c>.
///
/// <para>The F* type is the user's: it reaches the generated modules through
/// <see cref="IncludePulseAttribute"/> or by already being on the include path. The
/// translator emits the name it was given and does not check that it exists — that is
/// F*'s job, and a misspelling surfaces as a type error carrying this string.</para>
/// </summary>
[AttributeUsage(AttributeTargets.Struct | AttributeTargets.Class | AttributeTargets.Interface |
                AttributeTargets.Enum)]
public sealed class SpecTypeAttribute(string type) : Attribute
{
    public string Type { get; } = type;

    /// <summary>
    /// R20.11. The type is a reference type whose values may be <c>null</c>: a variable of
    /// it is an <c>option</c> of the F* type, and a member read through it requires it to
    /// be non-null.
    /// </summary>
    public bool Nullable { get; init; }
}

/// <summary>
/// R21.1. On a case of a closed hierarchy — a <c>sealed record</c> deriving from an
/// <c>abstract record</c> that carries <see cref="SpecTypeAttribute"/> — or on a constant of
/// an enum that carries one: the F* data constructor it denotes. Without it, the case's
/// constructor is the one in the base type's F* module with the case's own C# name.
/// </summary>
[AttributeUsage(AttributeTargets.Class | AttributeTargets.Field)]
public sealed class SpecCaseAttribute(string constructor) : Attribute
{
    public string Constructor { get; } = constructor;
}

/// <summary>
/// R21.5. Binds a member of a library type the program cannot annotate — named by its
/// documentation-comment ID, <c>"T:System.DateOnly"</c>,
/// <c>"M:System.DateOnly.op_LessThan(System.DateOnly,System.DateOnly)"</c> — to the F*
/// term it denotes: a type to the F* type (as <see cref="SpecTypeAttribute"/> does), and a
/// method, operator or property to a function (as <see cref="SpecOpAttribute"/> does). Each
/// binding is an assumption, listed among what the proof trusts.
/// </summary>
[AttributeUsage(AttributeTargets.Assembly, AllowMultiple = true)]
public sealed class SpecBindingAttribute(string member, string term) : Attribute
{
    public string Member { get; } = member;
    public string Term { get; } = term;
}

/// <summary>
/// R11.2. Declares this member to denote the F* term <paramref name="function"/>, applied
/// to the receiver if it has one and then to its arguments, left to right. One rule for a
/// property, an instance method, a static method and a discriminator, because all four are
/// applications.
/// </summary>
[AttributeUsage(AttributeTargets.Method | AttributeTargets.Property | AttributeTargets.Constructor)]
public sealed class SpecOpAttribute(string function) : Attribute
{
    public string Function { get; } = function;
}

/// <summary>
/// R27.22. A <see cref="SpecOpAttribute"/> over the nodes of a region. The method's first type
/// argument is a <c>[Region]</c> class <c>K</c>, and the F* term <paramref name="function"/>
/// is applied to <c>K</c>'s view, left link and right link (<c>class_K__view</c>,
/// <c>class_K__left</c>, <c>class_K__right</c>) before the arguments. A method returning
/// <c>void</c> is a lemma: called as a statement, it is a ghost call of the F* lemma.
/// </summary>
[AttributeUsage(AttributeTargets.Method)]
public sealed class RegionOpAttribute(string function) : Attribute
{
    public string Function { get; } = function;
}

/// <summary>
/// R27.23. An instance method of the class owning a region that runs with its receiver
/// <em>open</em>: it is handed the receiver's fields and the region's heap rather than its
/// invariant, and gives them back the same way. Its contract names the fields directly
/// (<c>root</c>) and the heap through <c>Pal.Heap&lt;K&gt;()</c>. It is for helpers called
/// in the middle of an update, where the invariant does not hold.
/// </summary>
[AttributeUsage(AttributeTargets.Method)]
public sealed class OpenAttribute : Attribute;

/// <summary>
/// R11.3. Declares this static method to denote a <em>constructor</em> of the
/// <c>[SpecType]</c> it returns. A constructor is a <see cref="SpecOpAttribute"/> that is
/// also a declaration: it is what §10 inverts to obtain a recursive class's ownership
/// predicate, so it is marked separately and carries the bit that says which one is empty.
///
/// <para>Set <see cref="Empty"/> on exactly one constructor per type. That is the one a
/// null reference denotes, and so the base case of every induction over the type. All the
/// constructors of one specification type must be declared together, as static methods of
/// a single class, which is how the empty one is found from a use of another.</para>
/// </summary>
[AttributeUsage(AttributeTargets.Method)]
public sealed class SpecCtorAttribute(string constructor) : Attribute
{
    public string Constructor { get; } = constructor;

    /// <summary>True of the nullary constructor a null reference denotes (R11.3).</summary>
    public bool Empty { get; init; }
}

// ---------------------------------------------------------------------------
// Raw Pulse interop.
// ---------------------------------------------------------------------------

/// <summary>Map this C# type onto a Pulse type given by a raw Pulse definition.</summary>
[AttributeUsage(AttributeTargets.Struct | AttributeTargets.Class)]
public sealed class PulseTypeAttribute(string definition) : Attribute
{
    public string Definition { get; } = definition;
}

/// <summary>Emit a verbatim Pulse module. Applied at assembly scope.</summary>
[AttributeUsage(AttributeTargets.Assembly | AttributeTargets.Class, AllowMultiple = true)]
public sealed class IncludePulseAttribute(string module, string body) : Attribute
{
    public string Module { get; } = module;
    public string Body { get; } = body;
}

/// <summary>
/// Emit a verbatim Pulse module read from a file beside the C# source. Applied at
/// assembly scope.
///
/// <para>This is <see cref="IncludePulseAttribute"/> with the body in its own
/// <c>.fst</c> file, which is how anything longer than a few lines should be written:
/// the file is real F* that an editor, <c>fstar.exe</c> and the IDE can all see, rather
/// than the inside of a C# string literal. The module name is <em>not</em> given
/// separately — it is the file's base name, so it cannot drift from the <c>module</c>
/// header the file already carries.</para>
///
/// <para><paramref name="path"/> is resolved relative to the directory of the C# file
/// carrying the attribute.</para>
/// </summary>
[AttributeUsage(AttributeTargets.Assembly | AttributeTargets.Class, AllowMultiple = true)]
public sealed class IncludePulseFileAttribute(string path) : Attribute
{
    public string Path { get; } = path;
}


/// <summary>
/// R20.1. Translate only the annotated declarations of this compilation. Applied at
/// assembly scope, it turns a whole-program translation into one that verifies chosen
/// methods of a program that is mostly ordinary code: a method is translated when it
/// carries a pal-csharp attribute, and calling one that is not is refused.
/// </summary>
[AttributeUsage(AttributeTargets.Assembly)]
public sealed class TranslateAnnotatedOnlyAttribute : Attribute;

/// <summary>
/// R27.39. A delegate parameter the method calls back with pointers into a region it holds.
/// The delegate takes one reference to a <c>[Region]</c> class and returns a value; the method
/// lends it the region at a fraction and states its contract about the calls through
/// <c>Pal.Trace</c>. An argument at this position is a lambda whose first statement is
/// <c>Pal.Protocol</c>, the invariant it keeps over the trace.
/// </summary>
/// <remarks>
/// R32.11. With <c>Bounded = true</c> the callee takes a bound from the caller,
/// <c>Pal.CallBound(action)</c>, and calls the delegate fewer times than it. Its contract
/// requires what it needs of the bound; the lambda passed states the bound in
/// <c>Pal.Protocol(tr => …, maxCalls)</c> and may assume it.
/// </remarks>
[AttributeUsage(AttributeTargets.Parameter)]
public sealed class CallbackAttribute : Attribute
{
    public bool Bounded { get; set; }
}

/// <summary>
/// R35.18. A <c>bool</c> parameter the method is translated at each constant value of,
/// instead of once: every call passes a literal (or omits the argument, passing the
/// default), and calls the translation at that value, in which an <c>if</c> the value
/// decides is the branch it takes. A method calling itself through the other value then
/// calls a different translation.
/// </summary>
[AttributeUsage(AttributeTargets.Parameter)]
public sealed class SpecializeAttribute : Attribute;
