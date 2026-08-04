using PalLang;

namespace PalCSharp.Tests;

/// <summary>
/// §7.2's variant of <see cref="Lists"/>: the same three functions, written differently.
/// Every local is renamed, every null test is written at the opposite polarity
/// (<c>!= null</c> with the empty case in the <c>else</c>), and the two results that were
/// returned directly are bound to a local first.
///
/// <para>The polarity is the part that matters. R10.7 opens its window at <em>the test the
/// program writes</em>, so a rule that only recognised <c>== null</c> would be a rule about
/// how the acceptance test happens to be phrased. This file must verify with no change to
/// the emitter.</para>
/// </summary>
public static class ListsVariant
{
    [Requires("cell.Elements.Length < 2147483647")]
    [Ensures("Result == cell.Elements.Length")]
    [Decreases("cell.Elements")]
    public static int Count(Node? cell)
    {
        if (cell != null)
        {
            int rest = Count(cell.next);
            return rest + 1;
        }
        else
        {
            return 0;
        }
    }

    [Ensures("Result.Elements == SpecList.Cons(head, tail.Elements)")]
    public static Node Prepend(int head, [Consumes] Node? tail)
    {
        Node built = new Node(head, tail);
        return built;
    }

    [Ensures("Result.Elements == SpecList.Append(front.Elements, back.Elements)")]
    [Decreases("front.Elements")]
    public static Node? Concat([Consumes] Node? front, [Consumes] Node? back)
    {
        if (front != null)
        {
            front.next = Concat(front.next, back);
            return front;
        }
        else
        {
            return back;
        }
    }
}
