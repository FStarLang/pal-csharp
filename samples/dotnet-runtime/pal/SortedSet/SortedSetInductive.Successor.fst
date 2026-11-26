module SortedSetInductive.Successor
#lang-pulse

open Pulse.Lib.Pervasives
module C = SortedSetInductive.Cursor
module O = SortedSetInductive.Ownership
module F = SortedSetInductive.Frontier
module N = Class_Node
module D = Pulse.Lib.CSharp.TopDown
module U = Pulse.Lib.CSharp.TopDownSucc
module R = Pulse.Lib.CSharp.TopDownRemove
module P = Pulse.Lib.CSharp.RegionPath
module K = SortedSetInductive.Relink
module T = Pulse.Lib.CSharp.Tree
module B = Pulse.Lib.Box
module L = FStar.List.Tot

#set-options "--z3rlimit 10"

let rec all_left_append (#a: Type0) (fs gs: list (C.frame a))
  : Lemma (requires R.all_left fs /\ R.all_left gs)
      (ensures R.all_left (L.append fs gs)) (decreases fs)
  = match fs with [] -> () | _::rest -> all_left_append rest gs

let rec min_decomp (#a: Type0) (n: O.tree a)
  : Lemma
      (ensures n == P.plug (U.lspine n) (U.lmin n) /\ R.all_left (U.lspine n) /\
        (T.Branch? n ==> T.Branch? (U.lmin n) /\ T.left (U.lmin n) == T.Leaf))
      (decreases n)
  = match n with
    | T.Leaf -> ()
    | T.Branch l e r ->
      if T.Branch? l then (
        min_decomp l;
        let f = {P.went_right=false; P.fbox=fst e; P.fval=snd e; P.fsib=r} in
        R.plug_append (U.lspine l) [f] (U.lmin l);
        all_left_append (U.lspine l) [f])

let remaining (#a: Type0) (m: O.tree a) =
  P.plug (U.lspine (T.right m)) (D.recolorn (T.right (U.lmin (T.right m))) false)

let replaced (#a: Type0) (m: O.tree a) = D.recolorn (U.pre_col m) (D.nred m)

let layout (#a: Type0) (m: O.tree a) (succ pos: N.class_Node__opt a) =
  O.good (T.left m) /\ O.good (T.right m) /\
  (succ == P.top m <==> T.right m == T.Leaf) /\
  (succ =!= P.top m ==>
    (let r = T.right m in
     let s = P.sub r succ in
     O.member r succ /\ T.Branch? s /\ P.top s == succ /\
     s == U.lmin r /\ T.left s == T.Leaf /\
     P.replace r succ (D.recolorn (T.right s) false) == remaining m /\
     (pos == P.top m <==> D.parent_of r succ == B.null) /\
     (pos =!= P.top m ==>
       pos == D.parent_of r succ /\ pos =!= B.null /\ not (K.side (K.path r succ))) /\
     U.pre_col m == T.Branch (T.left m) (T.Branch?._1 s) (remaining m)))

let layout_lemma (#a: Type0) (m: O.tree a) (succ pos: N.class_Node__opt a)
  : Lemma
      (requires O.good m /\ T.Branch? m /\ succ == U.succ_of m /\
        (T.Branch? (T.right m) ==> pos == U.pos_of m))
      (ensures layout m succ pos)
  = let T.Branch l e r = m in
    let nonnull_l (x: N.class_Node__opt a) : Lemma (O.member l x ==> x =!= B.null) = () in
    let nonnull_r (x: N.class_Node__opt a) : Lemma (O.member r x ==> x =!= B.null) = () in
    FStar.Classical.forall_intro nonnull_l;
    FStar.Classical.forall_intro nonnull_r;
    if T.Branch? r then (
      min_decomp r;
      D.focus_at (U.lspine r) (U.lmin r);
      assert (O.member r succ);
      assert (succ =!= P.top m);
      match U.lspine r with
      | [] -> ()
      | f::rest ->
        P.mem_plug f.P.fbox (f::rest) (U.lmin r);
        assert (f.P.fbox =!= P.top m))

ghost fn empty (#a: Type0) (n: O.tree a)
  requires O.owns n 1.0R ** pure (n == T.Leaf)
  ensures emp
{
  rewrite (O.owns n 1.0R) as emp;
}

ghost fn no_right (#a: Type0) (m: O.tree a)
  requires O.owns (T.left m) 1.0R ** O.owns (T.right m) 1.0R **
    pure (T.Branch? m /\ T.right m == T.Leaf)
  ensures O.owns (U.pre_col m) 1.0R
{
  empty (T.right m);
  rewrite (O.owns (T.left m) 1.0R) as (O.owns (U.pre_col m) 1.0R);
}

ghost fn successor_leaves (#a: Type0) (m: O.tree a)
  requires O.owns (T.left m) 1.0R ** O.owns (remaining m) 1.0R **
    pure (T.Branch? m /\ T.Branch? (T.right m))
  ensures O.owns (T.left (U.pre_col m)) 1.0R ** O.owns (T.right (U.pre_col m)) 1.0R
{
  min_decomp (T.right m);
  rewrite (O.owns (T.left m) 1.0R) as (O.owns (T.left (U.pre_col m)) 1.0R);
  rewrite (O.owns (remaining m) 1.0R) as (O.owns (T.right (U.pre_col m)) 1.0R);
}

// Removal preserves the match's original record, including its non-owning
// links. The ordinary owner retains this cell instead of clearing or dropping it.
unfold let cell (#a: Type0) (x: N.class_Node__opt a) (m: O.tree a) =
  exists* (v: N.class_Node__raw a).
    O.raw x v 1.0R **
    pure (m == T.Branch (T.left m) (x, O.entry v) (T.right m) /\
      v.N.fld_Left == P.top (T.left m) /\ v.N.fld_Right == P.top (T.right m))

let matches (#a: Type0) (m: O.tree a) (v: N.class_Node__raw a) = F.optional m == Some v

ghost fn canonical_cell (#a: Type0) (x: N.class_Node__opt a) (m: O.tree a) (v: N.class_Node__raw a)
  requires cell x m ** pure (matches m v)
  ensures O.raw x v 1.0R
{
  unfold (cell x m);
  with old. _;
  F.snapshot_facts m v;
  rewrite (O.raw x old 1.0R) as (O.raw x v 1.0R);
}
