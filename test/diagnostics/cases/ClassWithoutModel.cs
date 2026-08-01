// EXPECT: PALCS0524
// A specified class must declare a [Model] (R3.9).
//
// The two contracts below are perfectly sensible C#, and the class is translatable in
// every other respect -- which is exactly why it has to be refused loudly. Without a
// model there is nothing for the invariant to relate `count` to, so the strongest thing
// the generated Pulse could say about `Increment` is that it does not crash: a contract
// that evaporated is indistinguishable from a contract that was proved.
//
// `Get` is *not* the model. It is an ordinary method; the abstraction function is a
// [Model] member, and making the user name it is what fixes the model of the class
// rather than letting the compiler guess one from the fields (R3.9).
using PalLang;

public sealed class ClassWithoutModel
{
    private int count;

    [Requires("@this.Value >= 0")]
    [Ensures("@this.Value == Old(@this.Value) + 1")]
    public void Increment()
    {
        count = count + 1;
    }

    [Spec]
    public SpecInt Value => 0;

    public int Get() => count;
}
