module ComparerFacts

#set-options "--z3rlimit 10"

module O = Pulse.Lib.CSharp.Order
module I32 = FStar.Int32
module I64 = FStar.Int64

[@@expect_failure [19]]
let custom_comparer_need_not_use_numeric_order (c: O.comparer I32.t) (x y: I32.t)
  : Lemma (O.compare c x y < 0 <==> I32.v x < I32.v y)
  = ()

[@@expect_failure [19]]
let other_defaults_do_not_acquire_the_int32_law (x y: I64.t)
  : Lemma (O.compare (O.default_comparer I64.t) x y < 0 <==> I64.v x < I64.v y)
  = ()

[@@expect_failure [19]]
let sign_does_not_specify_the_models_magnitude (x y: I32.t)
  : Lemma (requires I32.v x < I32.v y)
          (ensures O.compare (O.default_comparer I32.t) x y == -1)
  = ()
