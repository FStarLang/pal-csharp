# `counter` — staged, not yet wired into the suite

`Counter.cs` is the first acceptance test for the object system (`doc/translation.md`
§3.4, §4.5): the walking skeleton that exercises a representation, a user-declared ghost
model, an abstraction function, an observation, an invariant, a constructor, a mutator and
a read-only method — with no array, so that a failure here is unambiguously about objects
rather than about ownership.

It already satisfies the core invariant: `make cs` compiles it with the stock C# compiler,
because every annotation is inert. What it does not yet do is verify, because `palcs` does
not translate classes — it *refuses* them, with `PALCS0530`.

The directory is named `_counter_wip` so that `test/Makefile`'s `TESTS` discovery (which
skips `_*`) leaves it out of the suite. Rename it to `counter`, add `Makefile` containing
`include ../verify.mk`, and run `make -C test configs` when the emitter can translate it.

The refusal itself is tested, at `test/diagnostics/cases/ClassNotYetSupported.cs`; delete
that case when this one starts passing.
