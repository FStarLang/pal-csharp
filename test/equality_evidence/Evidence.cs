using PalLang;

[assembly: TranslateAnnotatedOnly]

[Plain]
public sealed class IdentityKey
{
    public int Value;
}

[Plain]
public sealed class OverrideKey
{
    public int Value;
    public override bool Equals(object? other) => other is OverrideKey;
    public override int GetHashCode() => 0;
}

[Plain]
public sealed class EquatableKey : System.IEquatable<EquatableKey>
{
    public int Value;
    bool System.IEquatable<EquatableKey>.Equals(EquatableKey? other) => true;
}

// Even empty generic owners retain their default-equality interpretation in the
// storage type; it cannot be changed merely by refolding an empty invariant.
public sealed class EvidenceStorage<T>
{
    public int Value;
    [Model] private SpecInt Model => Value;
}

// A type argument's own evidence is part of that argument's type. It must not
// invent another binder on an otherwise evidence-free generic declaration.
[Spec]
public struct EvidenceEnvelope<T>
{
    public Seq<T> Value;
}

[Spec]
public struct NestedEvidenceStorage<T>
{
    public EvidenceEnvelope<EvidenceStorage<T>> Owner;
}

public static class EvidenceSpecs
{
    [Spec] public static SpecInt Zero<T>() => 0;

    [Ensures("EvidenceSpecs.Zero<T>() == 0")]
    public static void Nullary<T>() { }

}
