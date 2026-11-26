module Pulse.Lib.CSharp.StringComparers

module E = Pulse.Lib.CSharp.EqualityModel
module Raw = Pulse.Lib.CSharp.EqualityOpaque

let is_non_randomized = E.is_non_randomized
let non_randomized_refl (#t: Type0) {| E.has_equality t |} (c: E.handle) (x: t)
  : Lemma (requires is_non_randomized c) (ensures E.equals c x x)
  = E.non_randomized_refl c x

/// A deterministic mathematical exemplar, not the runtime factory.
let randomized_model = E.randomized
let randomized_model_equals (#t: Type0) {| E.has_equality t |}
                            (c: E.handle{is_non_randomized c}) (x y: t)
  : Lemma (E.equals (randomized_model c) x y == E.equals c x y)
          [SMTPat (E.equals (randomized_model c) x y)]
  = E.randomized_equals c x y

/// The runtime factory preserves equality but does not fix a per-input result
/// identity. This relational interface hides the deterministic implementation
/// witness; two calls are not equated, nor are their hash functions.
let randomized_from (c r: E.handle) : prop =
  E.OpaqueHandle? c /\ E.OpaqueHandle? r /\
  (forall (t: Type0) (x y: t).
    Raw.equals (E.token r) x y == Raw.equals (E.token c) x y)

val randomized (c: E.handle)
  : Pulse.Lib.Core.stt E.handle
      (Pulse.Lib.Core.pure (is_non_randomized c))
      (fun r -> Pulse.Lib.Core.pure (randomized_from c r))

val randomized_equals (#t: Type0) {| E.has_equality t |}
                      (c r: E.handle) (x y: t)
  : Lemma (requires randomized_from c r)
          (ensures E.equals r x y == E.equals c x y)
