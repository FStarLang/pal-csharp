module Pulse.Lib.CSharp.Span
#lang-pulse

open Pulse
open Pulse.Lib.CSharp.Assumptions
open Pulse.Lib.CSharp.Casts
open Pulse.Lib.CSharp.Inhabited
open Pulse.Lib.CSharp.Seq
open Pulse.Lib.SmallType

module A = Pulse.Lib.CSharp.Array
module S = Pulse.Lib.Slice
module I32 = FStar.Int32
module SZ = FStar.SizeT
module Seq = FStar.Seq

let is_from_array (#t: Type0) (a: A.array t) (s: S.slice t) : slprop =
  S.is_from_array (A.storage a) s

let span_length (#t: Type0) (s: span t) : I32.t = sizet_to_int32 (S.len s)

let span_length_v (#t: Type0) (s: span t)
  : Lemma (I32.v (span_length s) == SZ.v (S.len s))
          [SMTPat (I32.v (span_length s))]
  = ()

let span_length_bound (#t: Type0) (s: span t)
  : Lemma (SZ.v (S.len s) < pow2 31)
          [SMTPat (SZ.v (S.len s))]
  = ()

fn length_i32 (#t: Type0) (s: span t) (#p: perm) (#v: Ghost.erased (Seq.seq t))
  preserves S.pts_to s #p v
  returns  n : I32.t
  ensures  rewrites_to n (span_length s)
  ensures  pure (I32.v n == Seq.length v)
{
  S.pts_to_len s;
  span_length s
}

fn read (#t: Type0) (s: span t) (i: I32.t)
        (#p: perm)
        (#v: Ghost.erased (Seq.seq t) { I32.v i >= 0 /\ I32.v i < Seq.length v })
  preserves S.pts_to s #p v
  returns  x : t
  ensures  rewrites_to x (Seq.index v (I32.v i))
{
  S.op_Dot_Lparen_Rparen s (idx i)
}

fn write (#t: Type0) (s: span t) (i: I32.t) (x: t)
         (#v: Ghost.erased (Seq.seq t) { I32.v i >= 0 /\ I32.v i < Seq.length v })
  requires S.pts_to s v
  ensures  S.pts_to s (Seq.upd v (I32.v i) x)
{
  S.op_Dot_Lparen_Rparen_Less_Minus s (idx i) x
}

(* ---------------------------------------------------------------------- *)

fn of_array (#t: Type0) (a: A.array t) (#p: perm) (#v: Ghost.erased (Seq.seq t))
  requires A.pts_to a #p v
  returns  s : span t
  ensures  S.pts_to s #p v
  ensures  is_from_array a s
{
  A.pts_to_len a;
  A.pts_to_not_null a;
  let n = Pulse.Lib.CSharp.Array.length_i32 a;
  A.to_raw a;
  let s = S.from_array (A.storage a) (idx n);
  S.pts_to_len s;
  fold (is_from_array a s);
  s
}

ghost
fn restore_array (#t: Type0) (s: S.slice t)
                 (#a: A.array t) (#p: perm) (#v: Ghost.erased (Seq.seq t))
  requires S.pts_to s #p v
  requires is_from_array a s
  ensures  A.pts_to a #p v
{
  unfold (is_from_array a s);
  S.to_array s;
  A.of_raw a
}

(* ---------------------------------------------------------------------- *)

/// What is left of a parent while a window `[i, j)` is out on loan.
///
/// This is `Slice.subslice_rest` with its two `is_split`s written out, and the
/// difference is not cosmetic. `subslice_rest` is indexed by `size_t` bounds, and its
/// refinement `SZ.v i <= SZ.v j /\ SZ.v j <= Seq.length v` cannot be discharged for
/// bounds bound by an `exists*`, so a receipt that quantified over them would not
/// typecheck. Indexing by `nat` moves the refinement onto the receipt's own binder,
/// where it is available -- and `nat` is the right index anyway, because it is what
/// `splice` and every user-written specification speak.
let rest (#t: Type0) (s: S.slice t) (w: S.slice t) (p: perm) (i j: nat)
         (v: Seq.seq t { i <= j /\ j <= Seq.length v })
  : slprop
  = exists* (s1 s2 s3: S.slice t).
      S.is_split s s1 s2 **
      S.is_split s2 w s3 **
      S.pts_to s1 #p (Seq.slice v 0 i) **
      S.pts_to s3 #p (Seq.slice v j (Seq.length v))

ghost
fn intro_rest (#t: Type0) (w: S.slice t) (s: S.slice t) (#p: perm) (#i #j: SZ.t)
              (#v: Ghost.erased (Seq.seq t) { SZ.v i <= SZ.v j /\ SZ.v j <= Seq.length v })
  requires S.subslice_rest w s p i j v
  ensures  rest s w p (SZ.v i) (SZ.v j) v
{
  unfold (S.subslice_rest w s p i j v);
  fold (rest s w p (SZ.v i) (SZ.v j) v);
}

/// Giving the window back: two `Slice.join`s, which is why `Pulse.Lib.Slice` needs to
/// export no `unsubslice` (SliceFacts S8). The length hypothesis is what makes the
/// postcondition reduce to `splice` rather than to a raw `Seq.append`.
ghost
fn elim_rest (#t: Type0) (w: S.slice t) (#s: S.slice t) (#p: perm) (#i #j: nat)
             (#v: Ghost.erased (Seq.seq t) { i <= j /\ j <= Seq.length v })
             (#v': Ghost.erased (Seq.seq t))
  requires S.pts_to w #p v'
  requires rest s w p i j v
  requires pure (Seq.length v' == j - i)
  ensures  S.pts_to s #p (splice v i j v')
{
  unfold (rest s w p i j v);
  with s1 s2 s3. assert (S.is_split s s1 s2 ** S.is_split s2 w s3);
  S.join w s3 s2;
  S.join s1 s2 s;
}

(* ---------------------------------------------------------------------- *)

let is_range_of (#t: Type0) (a: A.array t) (w: S.slice t) (p: perm) (i j: nat)
                (v: Seq.seq t { i <= j /\ j <= Seq.length v })
  : slprop
  = exists* (s: S.slice t).
      S.is_from_array (A.storage a) s **
      rest s w p i j v **
      pure (SZ.v (S.len w) == j - i)

fn of_array_range (#t: Type0) (a: A.array t) (i: I32.t) (n: I32.t)
                  (#p: perm)
                  (#v: Ghost.erased (Seq.seq t) { I32.v i >= 0 /\ I32.v n >= 0 /\
                                                  I32.v i + I32.v n <= Seq.length v })
  requires A.pts_to a #p v
  returns  w : span t
  ensures  S.pts_to w #p (Seq.slice v (I32.v i) (I32.v i + I32.v n))
  ensures  is_range_of a w p (I32.v i) (I32.v i + I32.v n) v
{
  A.pts_to_len a;
  A.pts_to_not_null a;
  let alen = Pulse.Lib.CSharp.Array.length_i32 a;
  A.to_raw a;
  let s = S.from_array (A.storage a) (idx alen);
  let lo = idx i;
  let hi = idx (I32.add i n);
  let w = S.subslice s lo hi;
  S.pts_to_len w;
  intro_rest w s;
  rewrite (rest s w p (SZ.v lo) (SZ.v hi) v)
       as (rest s w p (I32.v i) (I32.v i + I32.v n) v);
  fold (is_range_of a w p (I32.v i) (I32.v i + I32.v n) v);
  w
}

ghost
fn restore_array_range (#t: Type0) (w: S.slice t)
                       (#a: A.array t) (#p: perm) (#i #j: nat)
                       (#v: Ghost.erased (Seq.seq t) { i <= j /\ j <= Seq.length v })
                       (#v': Ghost.erased (Seq.seq t))
  requires S.pts_to w #p v'
  requires is_range_of a w p i j v
  ensures  A.pts_to a #p (splice v i j v')
{
  S.pts_to_len w;
  unfold (is_range_of a w p i j v);
  with s. assert (S.is_from_array (A.storage a) s);
  elim_rest w;
  S.to_array s;
  A.of_raw a;
}

(* ---------------------------------------------------------------------- *)

let is_sub_of (#t: Type0) (s: S.slice t) (w: S.slice t) (p: perm) (i j: nat)
              (v: Seq.seq t { i <= j /\ j <= Seq.length v })
  : slprop
  = rest s w p i j v ** pure (SZ.v (S.len w) == j - i)

fn sub (#t: Type0) (s: span t) (i: I32.t) (n: I32.t)
       (#p: perm)
       (#v: Ghost.erased (Seq.seq t) { I32.v i >= 0 /\ I32.v n >= 0 /\
                                       I32.v i + I32.v n <= Seq.length v })
  requires S.pts_to s #p v
  returns  w : span t
  ensures  S.pts_to w #p (Seq.slice v (I32.v i) (I32.v i + I32.v n))
  ensures  is_sub_of s w p (I32.v i) (I32.v i + I32.v n) v
{
  S.pts_to_len s;
  let lo = idx i;
  let hi = idx (I32.add i n);
  let w = S.subslice s lo hi;
  S.pts_to_len w;
  intro_rest w s;
  rewrite (rest s w p (SZ.v lo) (SZ.v hi) v)
       as (rest s w p (I32.v i) (I32.v i + I32.v n) v);
  fold (is_sub_of s w p (I32.v i) (I32.v i + I32.v n) v);
  w
}

ghost
fn restore_sub (#t: Type0) (w: S.slice t)
               (#s: S.slice t) (#p: perm) (#i #j: nat)
               (#v: Ghost.erased (Seq.seq t) { i <= j /\ j <= Seq.length v })
               (#v': Ghost.erased (Seq.seq t))
  requires S.pts_to w #p v'
  requires is_sub_of s w p i j v
  ensures  S.pts_to s #p (splice v i j v')
{
  S.pts_to_len w;
  unfold (is_sub_of s w p i j v);
  elim_rest w;
}

(* ---------------------------------------------------------------------- *)

fn copy_to (#t: Type0) (src: S.slice t) (dst: S.slice t) (#p: perm)
           (#v: Ghost.erased (Seq.seq t))
  requires exists* v_dst. S.pts_to dst v_dst ** S.pts_to src #p v **
                          pure (Seq.length v_dst == Seq.length v)
  ensures  S.pts_to dst v ** S.pts_to src #p v
{
  with v_dst. assert (S.pts_to dst v_dst);
  S.pts_to_len dst;
  S.pts_to_len src;
  S.copy dst src
}
