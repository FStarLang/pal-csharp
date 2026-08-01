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
// ---------------------------------------------------------------------------

/// <summary>A precondition. The predicate is a C# expression in the scope of the member.</summary>
[AttributeUsage(AttributeTargets.Method | AttributeTargets.Constructor, AllowMultiple = true)]
public sealed class RequiresAttribute(string predicate) : Attribute
{
    public string Predicate { get; } = predicate;
}

/// <summary>
/// A postcondition. May use <c>Old(e)</c> for the pre-state value of <c>e</c>
/// and <c>Result</c> for the returned value.
/// </summary>
[AttributeUsage(AttributeTargets.Method | AttributeTargets.Constructor, AllowMultiple = true)]
public sealed class EnsuresAttribute(string predicate) : Attribute
{
    public string Predicate { get; } = predicate;
}

/// <summary>Shorthand for <c>[Requires(p)] [Ensures(p)]</c>.</summary>
[AttributeUsage(AttributeTargets.Method, AllowMultiple = true)]
public sealed class PreservesAttribute(string predicate) : Attribute
{
    public string Predicate { get; } = predicate;
}

/// <summary>Shorthand for <c>[Ensures("x == Old(x)")]</c>.</summary>
[AttributeUsage(AttributeTargets.Method, AllowMultiple = true)]
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

/// <summary>Suppress the resource this parameter's type would otherwise imply.</summary>
[AttributeUsage(AttributeTargets.Parameter)]
public sealed class PlainAttribute : Attribute;

/// <summary>Hold this parameter at an explicit fractional permission.</summary>
[AttributeUsage(AttributeTargets.Parameter)]
public sealed class FracAttribute(string permission) : Attribute
{
    public string Permission { get; } = permission;
}

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
// Ghost, spec and lemma methods.
// ---------------------------------------------------------------------------

/// <summary>
/// A pure specification function. Its C# expression body is translated to a
/// Pulse <c>let</c>, so it is usable in contracts and in ordinary code.
/// </summary>
[AttributeUsage(AttributeTargets.Method)]
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
