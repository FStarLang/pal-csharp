// EXPECT-PULSE: post_cursor
// R5.3, from the other side. `test/step_once` shows that `a[Bump(ref cursor)]++` advances
// the cursor by one. This is the claim that it advances it by two — the theorem a
// translation that duplicated the L-value used to prove, and did prove: `palcs` emitted
// two calls to `Bump`, F* discharged `cursor == Old(cursor) + 2`, and the C# it was a
// theorem about advanced the cursor by one.
//
// It is here rather than in `test/diagnostics` for the reason the header of `run.sh`
// gives. Nothing about this program is ill-formed: it is an ordinary C# method with an
// ordinary contract, and the only thing wrong with it is that the contract is false. That
// is a question about what the program computes, and the checker is what answers those.
// A frontend rule that recognised it would be a frontend guessing at a proof.
//
// The `EXPECT-PULSE` is the postcondition's own binder, which is what a failed
// postcondition is reported against: the claim that is refused is the one about `cursor`.
using PalLang;

public static class StepCountedTwice
{
    [Requires("0 <= cursor && cursor < 1000")]
    [Ensures("cursor == Old(cursor) + 1")]
    [Ensures("Result == Old(cursor)")]
    public static int Bump(ref int cursor)
    {
        int r = cursor;
        cursor = cursor + 1;
        return r;
    }

    [Requires("0 <= cursor && cursor + 1 < a.Length && a.Length < 1000")]
    [Requires("a[cursor] == 0 && a[cursor + 1] == 0")]
    [Ensures("cursor == Old(cursor) + 2")]
    // MARKER
    public static void PokeOnce(int[] a, ref int cursor)
    {
        a[Bump(ref cursor)]++;
    }
}
