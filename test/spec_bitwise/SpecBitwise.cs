using PalLang;

namespace PalCSharp.Tests;

/// <summary>
/// R6.4b: what the bitwise operators mean in a specification.
///
/// <para>The rule is the one R6.4a states for <c>/</c> and <c>%</c>, applied to the rest
/// of the operator table: a specification that quotes a C# expression has to mean the C#.
/// For <c>&amp;</c>, <c>|</c> and <c>^</c> over machine integers there is an exact image —
/// <c>FStar.Int32.logand</c> is specified as <c>v c == Int.logand (v a) (v b)</c>, so
/// naming <c>Int.logand</c> on the operands' values says precisely what the code
/// computes. For a shift there is not, because C# masks the shift count and F* does not
/// model that, so a shift is refused (<c>test/diagnostics/cases/ShiftInSpec.cs</c>).</para>
///
/// <para>What this file pins is that the two sides agree. Every contract here states the
/// result as the same bitwise expression the body evaluates, which is the property a user
/// actually relies on: a postcondition that quotes the code is discharged by the code.
/// Before R6.4b none of this held — the operator table ended in a catch-all that returned
/// <c>+</c>, so <c>x &amp; y</c> in a specification meant <c>x + y</c>, and the false
/// contracts in <c>test/pulse_refusals/cases/BitAndContract.cs</c> were provable.</para>
/// </summary>
public static class SpecBitwise
{
    /// <summary>
    /// The shape that matters: the postcondition quotes the operator the body applies.
    /// Under the catch-all this said <c>Result == x + y</c> and was discharged by a body
    /// computing <c>x &amp; y</c> only by accident of the values chosen.
    /// </summary>
    [Requires("x >= 0 && x < 256 && y >= 0 && y < 256")]
    [Ensures("Result == (x & y)")]
    public static int And(int x, int y)
    {
        return x & y;
    }

    [Requires("x >= 0 && x < 256 && y >= 0 && y < 256")]
    [Ensures("Result == (x | y)")]
    public static int Or(int x, int y)
    {
        return x | y;
    }

    [Requires("x >= 0 && x < 256 && y >= 0 && y < 256")]
    [Ensures("Result == (x ^ y)")]
    public static int Xor(int x, int y)
    {
        return x ^ y;
    }

    /// <summary>
    /// An unsigned operand takes the <c>FStar.UInt</c> family rather than
    /// <c>FStar.Int</c>. The two are different functions on the same syntax, so the
    /// choice is made by the operand type and not by the operator.
    /// </summary>
    [Requires("x < 256u && y < 256u")]
    [Ensures("Result == (x & y)")]
    public static uint AndUnsigned(uint x, uint y)
    {
        return x & y;
    }

    /// <summary>
    /// A bitwise operator in a <em>pre</em>condition, which is the other position a
    /// specification can put one in. Nothing bounds <c>logand</c> for the SMT solver, so
    /// this says what it needs about the operand rather than relying on the operator: see
    /// the incompleteness noted under R6.4b.
    /// </summary>
    [Requires("flags >= 0 && flags < 256 && (flags & 1) == 0")]
    [Ensures("Result == flags")]
    public static int EvenFlags(int flags)
    {
        return flags;
    }

    /// <summary>
    /// The unary half of the same rule. <c>FStar.Int32.lognot</c> is specified as
    /// <c>lognot (v x) == v z</c>, so a contract quoting <c>~x</c> is discharged by a body
    /// computing <c>~x</c>. Before R6.4b the unary table's catch-all returned the operand
    /// with the operator <em>dropped</em>, so <c>~e</c> in a specification meant <c>e</c>.
    /// </summary>
    [Requires("x >= 0 && x < 256")]
    [Ensures("Result == ~x")]
    public static int Complement(int x)
    {
        return ~x;
    }
}
