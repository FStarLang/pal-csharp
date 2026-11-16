module InductiveSuccessor
#lang-pulse

open Pulse.Lib.Pervasives
module C = InductiveCursor
module H = InductiveOwnership
module N = Class_RbNode
module D = Pulse.Lib.CSharp.TopDown
module U = Pulse.Lib.CSharp.TopDownSucc
module R = Pulse.Lib.CSharp.TopDownRemove
module P = Pulse.Lib.CSharp.RegionPath
module RT = Pulse.Lib.CSharp.RegionTree
module K = InductiveRelink
module T = Pulse.Lib.CSharp.Tree
module B = Pulse.Lib.Box
module L = FStar.List.Tot

#set-options "--z3rlimit 10"

let rec all_left_append (#a: Type0) (fs gs: list (C.frame a))
  : Lemma (requires R.all_left fs /\ R.all_left gs)
    (ensures R.all_left (L.append fs gs)) (decreases fs)
  = match fs with
    | [] -> ()
    | _::rest -> all_left_append rest gs

let rec min_decomp (#a: Type0) (n: C.tree a)
  : Lemma
    (ensures n == P.plug (U.lspine n) (U.lmin n) /\
      R.all_left (U.lspine n) /\
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

let remaining (#a: Type0) (m: C.tree a) =
  let r = T.right m in
  P.plug (U.lspine r) (D.recolorn (T.right (U.lmin r)) false)

let replaced (#a: Type0) (m: C.tree a) = D.recolorn (U.pre_col m) (D.nred m)

let layout (#a: Type0) (m: C.tree a) (succ pos: N.class_RbNode__opt a) : prop =
  C.good (T.left m) /\ C.good (T.right m) /\
  (succ == P.top m <==> T.right m == T.Leaf) /\
  (succ =!= P.top m ==>
    (let r = T.right m in
     let s = P.sub r succ in
     C.member r succ /\ T.Branch? s /\ P.top s == succ /\
     s == U.lmin r /\ T.left s == T.Leaf /\
     P.replace r succ (D.recolorn (T.right s) false) == remaining m /\
     (pos == P.top m <==> D.parent_of r succ == B.null) /\
     (pos =!= P.top m ==>
       pos == D.parent_of r succ /\ pos =!= B.null /\ not (K.side (K.path r succ))) /\
     U.pre_col m == T.Branch (T.left m) (T.Branch?._1 s) (remaining m)))

let layout_lemma (#a: Type0) (m: C.tree a) (succ pos: N.class_RbNode__opt a)
  : Lemma
    (requires C.good m /\ T.Branch? m /\ succ == U.succ_of m /\
      (T.Branch? (T.right m) ==> pos == U.pos_of m))
    (ensures layout m succ pos)
  = let T.Branch l e r = m in
    let nonnull_l (x: N.class_RbNode__opt a) : Lemma (C.member l x ==> x =!= B.null) = () in
    let nonnull_r (x: N.class_RbNode__opt a) : Lemma (C.member r x ==> x =!= B.null) = () in
    FStar.Classical.forall_intro nonnull_l;
    FStar.Classical.forall_intro nonnull_r;
    if T.Branch? r then (
      min_decomp r;
      D.focus_at (U.lspine r) (U.lmin r);
      assert (C.member r succ);
      assert (succ =!= P.top m);
      match U.lspine r with
      | [] -> ()
      | f::rest ->
        P.mem_plug f.P.fbox (f::rest) (U.lmin r);
        assert (f.P.fbox =!= P.top m))

ghost fn empty (#a: Type0) (n: C.tree a)
  requires C.owns n ** pure (n == T.Leaf)
  ensures emp
{
  rewrite (C.owns n) as emp;
}

ghost fn no_right (#a: Type0) (m: C.tree a)
  requires C.owns (T.left m) ** C.owns (T.right m) **
    pure (T.Branch? m /\ T.right m == T.Leaf)
  ensures C.owns (U.pre_col m)
{
  empty (T.right m);
  rewrite (C.owns (T.left m)) as (C.owns (U.pre_col m));
}

ghost fn successor_leaves (#a: Type0) (m: C.tree a)
  requires C.owns (T.left m) ** C.owns (remaining m) **
    pure (T.Branch? m /\ T.Branch? (T.right m))
  ensures C.owns (T.left (U.pre_col m)) ** C.owns (T.right (U.pre_col m))
{
  min_decomp (T.right m);
  rewrite (C.owns (T.left m)) as (C.owns (T.left (U.pre_col m)));
  rewrite (C.owns (remaining m)) as (C.owns (T.right (U.pre_col m)));
}

unfold let vacant (#a: Type0) (x: N.class_RbNode__opt a) (m: C.tree a) =
  exists* (key: a) (red: bool).
    H.held x key red B.null B.null **
    pure (m == T.Branch (T.left m) (x, (key, red)) (T.right m))

unfold let cell (#a: Type0) (x: N.class_RbNode__opt a) (m: C.tree a) =
  exists* (key: a) (red: bool) (l r: N.class_RbNode__opt a).
    H.held x key red l r **
    pure (m == T.Branch (T.left m) (x, (key, red)) (T.right m) /\
      l == P.top (T.left m) /\ r == P.top (T.right m))

ghost fn detach (#a: Type0) (x: N.class_RbNode__opt a) (m: C.tree a)
  requires vacant x m **
    pure (T.Branch? m /\ x =!= B.null)
  ensures H.detached x
{
  unfold (vacant x m);
  with key red. _;
  H.detach x key red;
}
