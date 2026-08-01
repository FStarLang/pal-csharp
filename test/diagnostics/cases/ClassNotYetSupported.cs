// EXPECT: PALCS0530
// An annotated class member must be *refused*, not silently dropped.
//
// Collect keeps only static ordinary methods plus [Spec]/[Lemma] members. Everything
// else used to be discarded without a word, so a file like this one translated to zero
// modules and zero errors -- a contract that evaporated is indistinguishable from a
// contract that was proved. Classes are specified in doc/translation.md §3.4 and §4.5
// but not yet implemented, so until they are, saying so is the whole job.
using PalLang;

public sealed class ClassNotYetSupported
{
    private int count;

    [Requires("@this.Get() >= 0")]
    [Ensures("@this.Get() == Old(@this.Get()) + 1")]
    public void Increment()
    {
        count = count + 1;
    }

    public int Get() => count;
}
