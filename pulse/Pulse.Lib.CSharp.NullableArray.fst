module Pulse.Lib.CSharp.NullableArray
#lang-pulse

/// A C# array reference that may be `null` (`T[]?`), as a field of a class owns it
/// (doc/translation.md R24.7).
///
/// `pts_to a #p s` is `Pulse.Lib.Array.pts_to a #p s` when `a` is not null, and owns
/// nothing, with empty contents, when it is. Every operation on such an array is the
/// ordinary one (`Pulse.Lib.CSharp.Array`) bracketed by `elim`, which needs the array
/// to be non-null, and `intro`; storing a fresh array into the field is `intro`, and a
/// field left `null` by a constructor is `intro_null`. Nothing here is assumed.

open Pulse
module A = Pulse.Lib.Array
module Seq = FStar.Seq
module T = FStar.Tactics

let pts_to (#t: Type0) (a: A.array t) (#[T.exact (`1.0R)] p: perm) (s: Seq.seq t) : slprop =
  if A.is_null a then pure (s == Seq.empty #t) else A.pts_to a #p s

ghost
fn elim (#t: Type0) (a: A.array t) (#p: perm) (#s: Seq.seq t)
  requires pts_to a #p s
  requires pure (not (A.is_null a))
  ensures  A.pts_to a #p s
{
  unfold (pts_to a #p s);
  rewrite (if A.is_null a then pure (s == Seq.empty #t) else A.pts_to a #p s)
       as (A.pts_to a #p s);
}

ghost
fn intro (#t: Type0) (a: A.array t) (#p: perm) (#s: Seq.seq t)
  requires A.pts_to a #p s
  ensures  pts_to a #p s ** pure (not (A.is_null a))
{
  A.pts_to_not_null a;
  rewrite (A.pts_to a #p s)
       as (if A.is_null a then pure (s == Seq.empty #t) else A.pts_to a #p s);
  fold (pts_to a #p s);
}

ghost
fn intro_null_at (#t: Type0) (a: A.array t) (#p: perm) (s: Seq.seq t)
  requires pure (A.is_null a /\ s == Seq.empty #t)
  ensures  pts_to a #p s
{
  rewrite (pure (s == Seq.empty #t))
       as (if A.is_null a then pure (s == Seq.empty #t) else A.pts_to a #p s);
  fold (pts_to a #p s);
}

ghost
fn intro_null (t: Type0) (_: unit)
  requires emp
  ensures  pts_to (A.null #t) (Seq.empty #t)
{
  intro_null_at (A.null #t) #1.0R (Seq.empty #t);
}

/// A fresh name for `null` that owns nothing: what a field write of `null` stores. The
/// name, rather than the literal, is what lets the prover find the field's ownership later.
fn alloc_null (t: Type0) (_: unit)
  returns  r: A.array t
  ensures  pts_to r (Seq.empty #t) ** pure (A.is_null r)
{
  let r = A.null #t;
  intro_null_at r #1.0R (Seq.empty #t);
  r
}

/// A null array owns nothing and holds nothing.
ghost
fn null_empty (#t: Type0) (a: A.array t) (#p: perm) (#s: Seq.seq t)
  preserves pts_to a #p s
  ensures  pure (A.is_null a ==> s == Seq.empty #t)
{
  if (A.is_null a)
  {
    unfold (pts_to a #p s);
    rewrite (if A.is_null a then pure (s == Seq.empty #t) else A.pts_to a #p s)
         as (pure (s == Seq.empty #t));
    rewrite (pure (s == Seq.empty #t))
         as (if A.is_null a then pure (s == Seq.empty #t) else A.pts_to a #p s);
    fold (pts_to a #p s);
  }
}

ghost
fn share (#t: Type0) (a: A.array t) (#s: Seq.seq t) (#p: perm)
  requires pts_to a #p s
  ensures  pts_to a #(p /. 2.0R) s ** pts_to a #(p /. 2.0R) s
{
  if (A.is_null a)
  {
    unfold (pts_to a #p s);
    rewrite (if A.is_null a then pure (s == Seq.empty #t) else A.pts_to a #p s)
         as (pure (s == Seq.empty #t));
    rewrite (pure (s == Seq.empty #t))
         as (if A.is_null a then pure (s == Seq.empty #t) else A.pts_to a #(p /. 2.0R) s);
    fold (pts_to a #(p /. 2.0R) s);
    rewrite (pure (s == Seq.empty #t))
         as (if A.is_null a then pure (s == Seq.empty #t) else A.pts_to a #(p /. 2.0R) s);
    fold (pts_to a #(p /. 2.0R) s);
  }
  else
  {
    elim a;
    A.share a;
    intro a #(p /. 2.0R);
    intro a #(p /. 2.0R);
  }
}

[@@allow_ambiguous]
ghost
fn gather (#t: Type0) (a: A.array t) (#s0 #s1: Seq.seq t) (#p0 #p1: perm)
  requires pts_to a #p0 s0 ** pts_to a #p1 s1
  ensures  pts_to a #(p0 +. p1) s0 ** pure (s0 == s1)
{
  if (A.is_null a)
  {
    unfold (pts_to a #p0 s0);
    unfold (pts_to a #p1 s1);
    rewrite (if A.is_null a then pure (s0 == Seq.empty #t) else A.pts_to a #p0 s0)
         as (pure (s0 == Seq.empty #t));
    rewrite (if A.is_null a then pure (s1 == Seq.empty #t) else A.pts_to a #p1 s1)
         as (pure (s1 == Seq.empty #t));
    rewrite (pure (s0 == Seq.empty #t))
         as (if A.is_null a then pure (s0 == Seq.empty #t) else A.pts_to a #(p0 +. p1) s0);
    fold (pts_to a #(p0 +. p1) s0);
  }
  else
  {
    elim a #p0 #s0;
    elim a #p1 #s1;
    A.gather a #s0 #s1 #p0 #p1;
    intro a #(p0 +. p1) #s0;
  }
}
