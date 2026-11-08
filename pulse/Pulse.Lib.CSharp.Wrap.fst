module Pulse.Lib.CSharp.Wrap

/// R32.14. Two's-complement wrapping of a mathematical integer to 32 bits, as R22.14's
/// `add_wrap` computes it: `I32.v (add_wrap x y) == int32 (I32.v x + I32.v y)`. Contracts
/// name it to state what a `[Wrapping]` counter becomes (`SortedSet<T>`'s `version`).
let int32 (x: int) : int = FStar.Int.to_int_t 32 x

let int32_add_wrap (x y: FStar.Int32.t)
  : Lemma (FStar.Int32.v (Pulse.Lib.CSharp.Int32.add_wrap x y) == int32 (FStar.Int32.v x + FStar.Int32.v y))
          [SMTPat (Pulse.Lib.CSharp.Int32.add_wrap x y)]
  = ()
