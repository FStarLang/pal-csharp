module SliceFacts
#lang-pulse

/// §0 probe for `Span<T>` / `ReadOnlySpan<T>`, which §8's *Not yet done* has listed since
/// M1 and which §14 named as the thing unconstrained generics were the prerequisite for.
///
/// Nothing here is a translation rule. This file exists to answer, *before* any rule is
/// written, the one question that decides whether spans are a small milestone or a large
/// one: **is a span an array-like slot, or is it something the §4 slot table cannot
/// describe?** The doc's line 256 has always promised the former --
///
///     | `T[] a`, `Span<T> a` | `var_a: array T` | `array_pts_to_full var_a 1.0R s` | ... |
///
/// -- and the answer below is that this is right for a span that is *never sliced*, and
/// wrong the moment one is, for reasons that are about C# and not about Pulse.
///
/// The Pulse side is nearly free. `Pulse.Lib.Slice` already *is* the `Span<T>` shape: a
/// first-class value with a length and a `pts_to` over its contents, with `split`/`join`,
/// `subslice`, `share`/`gather`, `copy`, and an `is_from_array` token recording provenance.
/// So the probes below are short, and the ones that matter are S2 and S4, which pin the two
/// facts the C# frontend will have to be designed around:
///
///   * **S2.** A subslice is *taken out of* its parent. `subslice` hands back the window
///     and leaves `subslice_rest`, and the parent's own `pts_to` is gone until they are
///     rejoined. In C# nothing marks either point: `var w = s.Slice(i, j - i);` is an
///     ordinary call, `s` stays in scope, and the compiler is happy to let you use it.
///     Recovering the split and the join by flow analysis is a borrow checker, which is
///     what R10.2b refuses to do on principle. So slicing needs *surface syntax*.
///
///   * **S4.** Copying a span value copies the pointer and not the resource. This is the
///     fact `PALCS0511` is about (§3.4: a struct field of reference type would let a struct
///     copy duplicate ownership) -- and a `Span<T>` is exactly such a struct. So a span
///     cannot be a translated struct; it has to be primitive, like `T[]`.
///
/// S6 records the one place the array library's answer carries over unchanged: `Slice.len`
/// is a `SizeT.t` and C#'s `Span<T>.Length` is an `int`, which is the same bridge
/// `Pulse.Lib.CSharp.Array.arr_length` already builds (R3.3), and it should be built the
/// same way -- an `.fsti` of modeling axioms over the Pulse library, not a new theory.

open Pulse
module SZ = FStar.SizeT
module A = Pulse.Lib.Array
module S = Pulse.Lib.Slice
module Seq = FStar.Seq

(* ------------------------------------------------------------------------ *)
(* S1. A span is an array-like slot: one binder, one `pts_to`, and a length  *)
(*     that is a pure function of the binder.                                *)
(* ------------------------------------------------------------------------ *)

/// The read-only shape -- `ReadOnlySpan<T>`, which is the fractional row of §4's table.
/// Note what the signature needs and does not need: a perm, a model, and nothing else. For
/// a span that is only read and indexed, line 256's promise holds exactly.
fn s1_read_only (#t: Type0) (s: S.slice t) (i: SZ.t) (#p: perm)
                (#v: Ghost.erased (Seq.seq t) { SZ.v i < Seq.length v })
  preserves S.pts_to s #p v
  returns  x : t
  ensures  pure (x == Seq.index v (SZ.v i))
{
  S.op_Dot_Lparen_Rparen s i
}

/// The full-permission shape -- `Span<T>`, the `array_pts_to_full` row.
fn s1_write (#t: Type0) (s: S.slice t) (i: SZ.t) (x: t)
            (#v: Ghost.erased (Seq.seq t) { SZ.v i < Seq.length v })
  requires S.pts_to s v
  ensures  S.pts_to s (Seq.upd v (SZ.v i) x)
{
  S.op_Dot_Lparen_Rparen_Less_Minus s i x
}

/// The length is `SZ.t` and is *not* ghost, so `for (int k = 0; k < s.Length; k++)` has a
/// pure guard, exactly as it does for an array. `pts_to_len` is what ties it to the model.
fn s1_length (#t: Type0) (s: S.slice t) (#p: perm) (#v: Ghost.erased (Seq.seq t))
  preserves S.pts_to s #p v
  returns  n : SZ.t
  ensures  pure (SZ.v n == Seq.length v)
{
  S.pts_to_len s;
  S.len s
}

(* ------------------------------------------------------------------------ *)
(* S2. Slicing takes the window *out of* the parent -- and giving it back is  *)
(*     derivable, which is the half of the problem that is not C#'s.          *)
(* ------------------------------------------------------------------------ *)

/// What `s.Slice(i, j - i)` produces. The parent's `pts_to s` does not appear in the
/// postcondition at all: it has been consumed, and what is left of it is the opaque
/// `subslice_rest`. A C# program that goes on using `s` here is using memory it no longer
/// owns, and no amount of care in the *translation* can make that verify -- the annotation
/// has to say when the window closes.
fn s2_take (#t: Type0) (s: S.slice t) (i j: SZ.t) (#p: perm)
           (#v: Ghost.erased (Seq.seq t) { SZ.v i <= SZ.v j /\ SZ.v j <= Seq.length v })
  requires S.pts_to s #p v
  returns  w : S.slice t
  ensures  S.pts_to w #p (Seq.slice v (SZ.v i) (SZ.v j))
  ensures  S.subslice_rest w s p i j v
{
  S.subslice s i j
}

/// Closing the window again. `Pulse.Lib.Slice` exports no `unsubslice`, but it does not
/// need to: `subslice_rest` is a transparent definition over two `is_split`s, so the join
/// is two `Slice.join`s and this lemma is derivable rather than a library request.
///
/// The postcondition is the fact that makes spans *worth* having, and it is the one an
/// aliasing-unaware translation would get wrong: the parent afterwards holds the window's
/// **current** contents `v'`, which may differ from what it lent out, spliced between the
/// two parts outside the window, which are **unchanged**. Writes through a subspan are
/// visible in the parent; writes through the parent are impossible while the window is out.
ghost
fn s2_give_back (#t: Type0) (w: S.slice t) (s: S.slice t) (p: perm) (i j: SZ.t)
                (#v: Ghost.erased (Seq.seq t) { SZ.v i <= SZ.v j /\ SZ.v j <= Seq.length v })
                (#v': Ghost.erased (Seq.seq t))
  requires S.pts_to w #p v'
  requires S.subslice_rest w s p i j v
  ensures  S.pts_to s #p (Seq.append (Seq.slice v 0 (SZ.v i))
                                     (Seq.append v' (Seq.slice v (SZ.v j) (Seq.length v))))
{
  unfold (S.subslice_rest w s p i j v);
  with s1 s2 s3. assert (S.is_split s s1 s2 ** S.is_split s2 w s3);
  S.join w s3 s2;
  S.join s1 s2 s;
}

/// And the special case that says the whole thing is sound: give back a window you did not
/// write to, and the parent is exactly as it was. This is a `Seq` fact, not a Pulse one,
/// but it is the one a `[Lemma]` at the close of a `Pal.Span` scope would have to discharge.
let s2_unchanged (#t: Type0) (v: Seq.seq t) (i j: nat)
  : Lemma (requires i <= j /\ j <= Seq.length v)
          (ensures  Seq.append (Seq.slice v 0 i)
                               (Seq.append (Seq.slice v i j) (Seq.slice v j (Seq.length v)))
                    == v)
  = Seq.lemma_eq_intro
      (Seq.append (Seq.slice v 0 i)
                  (Seq.append (Seq.slice v i j) (Seq.slice v j (Seq.length v))))
      v

(* ------------------------------------------------------------------------ *)
(* S3. Provenance. An array lent out as a span is unusable until returned.    *)
(* ------------------------------------------------------------------------ *)

/// `Span<T> s = arr;` -- the implicit `T[]` to `Span<T>` conversion. `from_array` consumes
/// `A.pts_to` and produces `S.pts_to` **plus a token**, `is_from_array a s`, which is the
/// receipt. The array cannot be indexed again until `to_array` redeems it.
///
/// So a span parameter is *not* one resource in general: it is a resource and, where it
/// came from an array the caller still names, a token. §4's slot table has no column for a
/// token, and this -- not indexing, and not the library -- is where the milestone's real
/// work is.
fn s3_lend_and_redeem (#t: Type0) (a: A.array t) (n: SZ.t) (i: SZ.t) (x: t)
                      (#v: Ghost.erased (Seq.seq t) { SZ.v n == A.length a /\
                                                      SZ.v i < Seq.length v })
  requires A.pts_to a v
  ensures  A.pts_to a (Seq.upd v (SZ.v i) x)
{
  let s = S.from_array a n;
  S.op_Dot_Lparen_Rparen_Less_Minus s i x;
  S.to_array s;
}

(* ------------------------------------------------------------------------ *)
(* S4. A span value may be copied; the resource may not.                     *)
(* ------------------------------------------------------------------------ *)

/// Two C# names for one span. `let s2 = s` is a struct copy -- which is all a `Span<T>`
/// assignment ever is -- and afterwards there is still exactly *one* `pts_to`, so a write
/// through either name is a write to the memory both describe.
///
/// This is why a span cannot go through §3.4's struct rules. `PALCS0511` rejects a struct
/// with a reference-typed field on precisely this ground, and rejecting `Span<T>` on that
/// ground would be right and useless. The alternative is to make it primitive: a span is a
/// *slot kind*, like `T[]`, with its own row in §4's table and no struct copying at all.
fn s4_copy_is_alias (#t: Type0) (s: S.slice t) (i: SZ.t) (x: t)
                    (#v: Ghost.erased (Seq.seq t) { SZ.v i < Seq.length v })
  requires S.pts_to s v
  returns  y : t
  ensures  S.pts_to s (Seq.upd v (SZ.v i) x)
  ensures  pure (y == x)
{
  let s2 = s;
  rewrite (S.pts_to s v) as (S.pts_to s2 v);
  S.op_Dot_Lparen_Rparen_Less_Minus s2 i x;
  with v2. assert (S.pts_to s2 v2);
  rewrite (S.pts_to s2 v2) as (S.pts_to s v2);
  S.op_Dot_Lparen_Rparen s i
}

/// The safe form of the same thing, and the reason `ReadOnlySpan<T>` is the easier half:
/// a fractional view *is* duplicable, so `[Frac]` (R4.9) already says what is wanted and no
/// new surface syntax is needed for a read-only span at all.
ghost
fn s4_share_gather (#t: Type0) (s: S.slice t) (#p: perm) (#v: Ghost.erased (Seq.seq t))
  preserves S.pts_to s #p v
{
  S.share s;
  S.gather s;
}

(* ------------------------------------------------------------------------ *)
(* S5 / S6. Two conveniences that come for free.                             *)
(* ------------------------------------------------------------------------ *)

/// `src.CopyTo(dst)` is `Slice.copy`, with the length equality C# checks at runtime showing
/// up as a precondition -- so the emitter owes an obligation, not a library.
fn s5_copy_to (#t: Type0) (dst: S.slice t) (src: S.slice t) (#p: perm)
              (#v: Ghost.erased (Seq.seq t))
  requires exists* v_dst. S.pts_to dst v_dst ** S.pts_to src #p v **
                          pure (S.len src == S.len dst)
  ensures  S.pts_to dst v ** S.pts_to src #p v
{
  S.copy dst src;
}

/// S6. The index bridge is the *same* one R3.3 already builds for arrays, so it should be
/// built the same way: a `Pulse.Lib.CSharp.Span` `.fsti` of modeling axioms over
/// `Pulse.Lib.Slice`, mirroring `Pulse.Lib.CSharp.Array`'s `arr_length` / `read` / `write`,
/// rather than anything new. This is what its `Length` would look like; the bound on the
/// length is a CLR fact in exactly the way `arr_length_bound` is.
noextract
let span_length_spec (#t: Type0) (s: S.slice t) : GTot nat = SZ.v (S.len s)

let s6_length_is_pure (#t: Type0) (s: S.slice t) (#p: perm) (v: Seq.seq t)
  : Lemma (requires SZ.v (S.len s) == Seq.length v)
          (ensures  span_length_spec s == Seq.length v)
  = ()

(* ------------------------------------------------------------------------ *)
(* S7. The design S2 asked for, now that the surface question is settled.    *)
(*                                                                          *)
(* S2's comment concluded that "slicing needs *surface syntax*", and read    *)
(* that as a demand for a scoped construct -- something that marks where the *)
(* window opens and where it closes, so the translation could insert the     *)
(* split and the join. That was the wrong shape, and it is worth saying why, *)
(* because the right shape is much smaller.                                  *)
(*                                                                          *)
(* Taking the window needs no syntax at all: `a.AsSpan(i, n)` is already an  *)
(* ordinary C# expression, and translating it to `subslice` is an ordinary   *)
(* compositional rule. Only *giving it back* is invisible in C#. And a step  *)
(* that is invisible in C#, needed for the proof and erased at runtime, is   *)
(* precisely what a proof annotation language already has a word for: it is  *)
(* a ghost statement. `Pal.Restore(w)` is written by the user at the point   *)
(* where the borrow ends.                                                    *)
(*                                                                          *)
(* Nothing has to *infer* where that point is, which is the whole of the     *)
(* borrow-checking problem R10.2b refuses on principle. If the user writes   *)
(* it too late, or not at all, the parent's `pts_to` is missing where the    *)
(* postcondition needs it and the proof fails. If the user writes it too     *)
(* early, the window's own `pts_to` is gone and the next `w[k]` fails. Both  *)
(* failures land in the user's annotations, which is where §0 rule 3 says    *)
(* proof difficulty belongs.                                                 *)
(* ------------------------------------------------------------------------ *)

/// The parent's contents after a window is given back: everything outside `[i, j)`
/// unchanged, and `w` in between. This is the pure model that `Pal.Restore` leaves
/// behind, and the only new spec-level vocabulary the milestone needs.
let splice (#t: Type0) (v: Seq.seq t) (i j: nat) (w: Seq.seq t) : Seq.seq t =
  if i <= j && j <= Seq.length v && Seq.length w = j - i
  then Seq.append (Seq.slice v 0 i) (Seq.append w (Seq.slice v j (Seq.length v)))
  else v

/// Length, index, and -- the one that makes a read-only borrow free -- the identity.
let splice_length (#t: Type0) (v: Seq.seq t) (i j: nat) (w: Seq.seq t)
  : Lemma (requires i <= j /\ j <= Seq.length v /\ Seq.length w == j - i)
          (ensures  Seq.length (splice v i j w) == Seq.length v)
  = ()

let splice_index (#t: Type0) (v: Seq.seq t) (i j: nat) (w: Seq.seq t) (k: nat)
  : Lemma (requires i <= j /\ j <= Seq.length v /\ Seq.length w == j - i /\ k < Seq.length v)
          (ensures  Seq.index (splice v i j w) k ==
                    (if k < i then Seq.index v k
                     else if k < j then Seq.index w (k - i)
                     else Seq.index v k))
  = ()

let splice_same (#t: Type0) (v: Seq.seq t) (i j: nat)
  : Lemma (requires i <= j /\ j <= Seq.length v)
          (ensures  splice v i j (Seq.slice v i j) == v)
  = Seq.lemma_eq_intro (splice v i j (Seq.slice v i j)) v

(* ------------------------------------------------------------------------ *)
(* S8. `Pal.Restore(w)` names exactly one thing: the window. Everything else *)
(*     -- the parent, the permission, the bounds, the two contents -- has to *)
(*     come from unification against the receipt in context, or the emitter  *)
(*     would have to reconstruct them, and reconstructing the parent is the  *)
(*     borrow checker again.                                                 *)
(* ------------------------------------------------------------------------ *)

ghost
fn give_back (#t: Type0) (w: S.slice t)
             (#s: S.slice t) (#p: perm) (#i #j: SZ.t)
             (#v: Ghost.erased (Seq.seq t) { SZ.v i <= SZ.v j /\ SZ.v j <= Seq.length v })
             (#v': Ghost.erased (Seq.seq t))
  requires S.pts_to w #p v'
  requires S.subslice_rest w s p i j v
  ensures  S.pts_to s #p (Seq.append (Seq.slice v 0 (SZ.v i))
                                     (Seq.append v' (Seq.slice v (SZ.v j) (Seq.length v))))
{
  unfold (S.subslice_rest w s p i j v);
  with s1 s2 s3. assert (S.is_split s s1 s2 ** S.is_split s2 w s3);
  S.join w s3 s2;
  S.join s1 s2 s;
}

/// And the call, with `w` the only explicit argument -- which is the signature
/// `Pal.Restore(w)` translates to.
fn s8_restore_by_unification (#t: Type0) (s: S.slice t) (i j: SZ.t) (x: t)
    (#v: Ghost.erased (Seq.seq t) { SZ.v i < SZ.v j /\ SZ.v j <= Seq.length v })
  requires S.pts_to s v
  ensures  exists* v'. S.pts_to s v'
{
  let w = S.subslice s i j;
  S.pts_to_len w;
  S.op_Dot_Lparen_Rparen_Less_Minus w 0sz x;
  give_back w;
}

(* ------------------------------------------------------------------------ *)
(* S9. `a.AsSpan(i, n)` is *one* C# construct, so it must be *one* borrow.    *)
(*                                                                          *)
(* Underneath it is two Pulse steps -- `from_array` then `subslice` -- and   *)
(* the intermediate whole-array slice has no C# name. If the receipt were    *)
(* left as the two separate tokens the two steps produce, `Pal.Restore`      *)
(* would have to be written twice, the second time naming something the user *)
(* never wrote. So the receipt is packaged, with the intermediate existentially *)
(* quantified inside it, and one `Pal.Restore` redeems the whole thing.       *)
(*                                                                          *)
(* The receipt also carries the window's length. Without it `restore` cannot *)
(* even *state* its postcondition: `splice v i j v'` is the identity unless  *)
(* `v'` is known to have length `j - i`, and after arbitrary writes through  *)
(* the window that is a fact about the borrow, not about `v'`.                *)
(* ------------------------------------------------------------------------ *)

let is_range_of (#t: Type0) (a: A.array t) (w: S.slice t) (p: perm) (i j: SZ.t)
                (v: Seq.seq t { SZ.v i <= SZ.v j /\ SZ.v j <= Seq.length v })
  : slprop
  = exists* (s: S.slice t).
      S.is_from_array a s **
      S.subslice_rest w s p i j v **
      pure (SZ.v (S.len w) == SZ.v j - SZ.v i)

fn take_range (#t: Type0) (a: A.array t) (n: SZ.t) (i j: SZ.t) (#p: perm)
              (#v: Ghost.erased (Seq.seq t) { SZ.v n == A.length a /\
                                              SZ.v i <= SZ.v j /\ SZ.v j <= Seq.length v })
  requires A.pts_to a #p v
  returns  w : S.slice t
  ensures  S.pts_to w #p (Seq.slice v (SZ.v i) (SZ.v j))
  ensures  is_range_of a w p i j v
{
  let s = S.from_array a n;
  let w = S.subslice s i j;
  S.pts_to_len w;
  fold (is_range_of a w p i j v);
  w
}

ghost
fn restore_range (#t: Type0) (w: S.slice t)
                 (#a: A.array t) (#p: perm) (#i #j: SZ.t)
                 (#v: Ghost.erased (Seq.seq t) { SZ.v i <= SZ.v j /\ SZ.v j <= Seq.length v })
                 (#v': Ghost.erased (Seq.seq t))
  requires S.pts_to w #p v'
  requires is_range_of a w p i j v
  ensures  A.pts_to a #p (splice v (SZ.v i) (SZ.v j) v')
{
  S.pts_to_len w;
  unfold (is_range_of a w p i j v);
  with s. assert (S.is_from_array a s);
  give_back w;
  S.to_array s;
}

/// The round trip, at the shape a translated C# method has: take a window out of an
/// array parameter, write through it, give it back, and be left with a `pts_to` on
/// the *array* strong enough for a postcondition about `a` to be stated.
fn s9_round_trip (#t: Type0) (a: A.array t) (n: SZ.t) (i j: SZ.t) (x: t)
    (#v: Ghost.erased (Seq.seq t) { SZ.v n == A.length a /\
                                    SZ.v i < SZ.v j /\ SZ.v j <= Seq.length v })
  requires A.pts_to a v
  ensures  A.pts_to a (splice v (SZ.v i) (SZ.v j)
                              (Seq.upd (Seq.slice v (SZ.v i) (SZ.v j)) 0 x))
{
  let w = take_range a n i j;
  S.pts_to_len w;
  S.op_Dot_Lparen_Rparen_Less_Minus w 0sz x;
  restore_range w;
}

/// And the read-only trip, which `splice_same` collapses to a no-op: a window taken
/// and given back unwritten leaves the array *syntactically* as it was, so a caller
/// that only reads through a span owes nothing.
fn s9_read_only_trip (#t: Type0) (a: A.array t) (n: SZ.t) (i j: SZ.t) (#p: perm)
    (#v: Ghost.erased (Seq.seq t) { SZ.v n == A.length a /\
                                    SZ.v i <= SZ.v j /\ SZ.v j <= Seq.length v })
  requires A.pts_to a #p v
  ensures  A.pts_to a #p v
{
  let w = take_range a n i j;
  splice_same (reveal v) (SZ.v i) (SZ.v j);
  restore_range w;
}
