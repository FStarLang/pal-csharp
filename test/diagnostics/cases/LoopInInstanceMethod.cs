// EXPECT: PALCS0001
// R4.10's `unfold`/`fold` bracket is open across an instance method's whole body, so a
// loop inside it sits in the window where the object's invariant does not hold. Pulse
// needs the loop invariant to name every resource the body touches, and here those are the
// *unfolded* ones — `B.pts_to this r`, one `A.pts_to` per array field, `r` and the contents
// existentially quantified — while `Pal.Invariant` clauses would have to be read against
// the representation instead of the model. That is a sub-scheme, and it is not written.
//
// Emitting the folded invariant instead, which is what R5.8's loop rule does unaided,
// produces Pulse that cannot verify and whose failure points at generated code. Refusing
// it points at the loop. The workaround is the one M1 already supports: put the loop in a
// static method that takes the array.
using PalLang;

[Invariant("0 <= n")]
public sealed class Bag
{
    private int[] data;
    private int n;

    [Refine("Result >= 0")]
    [Model]
    private SpecInt Model => n;

    [Spec]
    public SpecInt Count => Model;

    [Ensures("Result >= 0")]
    public int CountUp()
    {
        int found = 0;
        int i = 0;
        while (i < 10)
        {
            Pal.Invariant(0 <= i && i <= 10);
            Pal.Invariant(found >= 0);
            Pal.Decreases(10 - i);
            found = found + 1;
            i = i + 1;
        }
        return found;
    }
}
