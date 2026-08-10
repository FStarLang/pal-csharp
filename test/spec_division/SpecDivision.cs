using PalLang;

namespace PalCSharp.Tests;

/// <summary>
/// R6.4a: what <c>/</c> and <c>%</c> mean in a specification.
///
/// <para>C#'s <c>/</c> and <c>%</c> round toward zero; F*'s round toward minus infinity.
/// On a negative operand the two disagree — <c>-7 / 2</c> is <c>-3</c> in C# and
/// <c>-4</c> in F*, and <c>-7 % 2</c> is <c>-1</c> and <c>1</c>. A specification is read
/// by someone who is reading C#, so where it quotes a C# expression it has to mean the
/// C#; otherwise the reader and the prover agree on the string and disagree on the
/// claim, and they disagree only about a sign the reader was not thinking about.</para>
///
/// <para>The rule turns on the operand types, and this file pins both sides of it. Over
/// machine integers, one of them signed, the operators are C#'s. Over a spec-only
/// numeric they are the mathematics they look like, because there is no C# operator
/// there to disagree with. Over unsigned machine integers the question does not arise:
/// the two roundings coincide on non-negative operands, and F*'s are already C#'s.</para>
/// </summary>
public static class SpecDivision
{
    /// <summary>
    /// Division at a negative operand, stated twice: once as a literal answer and once
    /// as the C# expression. The two <c>Ensures</c> are consistent only if the
    /// specification's <c>/</c> truncates. Under F*'s <c>/</c> the method would be
    /// claiming <c>-3 == -4</c>.
    /// </summary>
    [Requires("x == -7")]
    [Ensures("Result == -3")]
    [Ensures("Result == x / 2")]
    public static int DivNegative(int x) => x / 2;

    /// <summary>
    /// The same for the remainder, whose sign follows the dividend in C# and the divisor
    /// in F*: <c>-1</c> against <c>1</c>. The two <c>Ensures</c> agree only on the first.
    /// </summary>
    [Requires("x == -7")]
    [Ensures("Result == -1")]
    [Ensures("Result == x % 2")]
    public static int RemNegative(int x) => x % 2;

    /// <summary>
    /// A general signed division, where the specification names the operator rather than
    /// an answer. The precondition is the one R6.4 already asks for; the point here is
    /// that the postcondition means the division the method performs.
    /// </summary>
    [Requires("y > 0 && x > -1000 && x < 1000")]
    [Ensures("Result == x / y")]
    [Ensures("Result * y + (x % y) == x")]
    public static int DivExact(int x, int y) => x / y;

    /// <summary>
    /// Unsigned operands, where nothing changed: a <c>uint</c> is never negative, so the
    /// two roundings coincide and the specification is discharged by F*'s own operator.
    /// </summary>
    [Requires("y != 0")]
    [Ensures("Result == x % y")]
    [Ensures("Result < y")]
    public static uint RemUnsigned(uint x, uint y) => x % y;

    /// <summary>Floor division, written on a spec-only numeric.</summary>
    [Spec]
    public static SpecInt Floor2(SpecInt n) => n / 2;

    /// <summary>
    /// The two worlds side by side, at the operand where they part. <c>Floor2</c> is
    /// mathematics and rounds down; the literal expression is C# and rounds toward zero.
    /// Both assertions hold, and neither would if the emitter used one rule for both.
    /// </summary>
    [Ensures("Result == 0")]
    public static int TwoWorlds()
    {
        Pal.Assert(Floor2(-7) == -4);
        Pal.Assert(-7 / 2 == -3);
        Pal.Assert(-7 % 2 == -1);
        return 0;
    }
}
