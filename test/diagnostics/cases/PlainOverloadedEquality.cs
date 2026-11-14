// EXPECT: PALCS0001
// An overloaded operator is not reference identity, even on a plain representation.
using PalLang;

[assembly: TranslateAnnotatedOnly]

[Plain]
public sealed class Node
{
    public static bool operator ==(Node? left, Node? right) => true;
    public static bool operator !=(Node? left, Node? right) => false;
    public override bool Equals(object? other) => true;
    public override int GetHashCode() => 0;
}

public static class Same
{
    [Ensures("true")]
    public static bool Eq(Node? left, Node? right) => left == right;
}
