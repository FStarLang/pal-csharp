// EXPECT: PALCS0001
// §18's totality is a property of the frontend, not of the operators it happens to know.
// `>>>=` and `??=` are `AssignmentExpressionSyntax` like every other compound assignment,
// so they reach the same lowering; before this case they reached a `throw` there and
// crashed the translator with a .NET stack trace. A construct outside the subset is
// refused with a diagnostic that names it, like every other one.
using PalLang;

public static class UnsupportedAssignmentOperator
{
    public static int Shift(int x)
    {
        int u = x;
        u >>>= 1;
        return u;
    }
}
