module SortedSetInductive.Construction
#lang-pulse
open Pulse.Lib.Pervasives
module B = Pulse.Lib.Box
module N = Class_Node
module T = Pulse.Lib.CSharp.Tree
module O = SortedSetInductive.Ownership
module E = SortedSetInductive.Edit
module S = Pulse.Lib.CSharp.SearchTree
module Build = Pulse.Lib.CSharp.SortedBuild

// Fresh construction does not know the allocated pointer labels in advance.
// This ordinary inductive predicate binds the actual child pointers locally.
let rec holds (#a: Type0) ([@@@mkey] root: N.class_Node__opt a)
    (t: T.tree (a & bool)) (p: perm) : Tot slprop (decreases t) =
  match t with
  | T.Leaf -> pure (root == B.null)
  | T.Branch l e r ->
    exists* (left right: N.class_Node__opt a).
      O.held root (fst e) (snd e) left right p **
      holds left l p ** holds right r p

ghost fn empty (#a: Type0) (root: N.class_Node__opt a) (p: perm)
  requires pure (root == B.null)
  ensures holds root (T.Leaf <: T.tree (a & bool)) p
{
  fold (holds root (T.Leaf <: T.tree (a & bool)) p);
}

ghost fn cases (#a: Type0) (root: N.class_Node__opt a) (t: T.tree (a & bool)) (p: perm)
  preserves holds root t p
  ensures pure (B.is_null root <==> T.Leaf? t)
{
  match t {
    T.Leaf -> {
      rewrite (holds root t p) as (holds root (T.Leaf <: T.tree (a & bool)) p);
      unfold (holds root (T.Leaf <: T.tree (a & bool)) p);
      fold (holds root (T.Leaf <: T.tree (a & bool)) p);
    }
    T.Branch l e r -> {
      rewrite (holds root t p) as (holds root (T.Branch l e r) p);
      unfold (holds root (T.Branch l e r) p);
      with left right. _;
      B.pts_to_not_null root;
      fold (holds root (T.Branch l e r) p);
    }
  }
}

ghost fn reindex (#a: Type0) (old root: N.class_Node__opt a) (t: T.tree (a & bool))
  requires holds old t 1.0R ** pure (old == root)
  ensures holds root t 1.0R
{
  rewrite (holds old t 1.0R) as (holds root t 1.0R);
}

ghost fn seal (#a: Type0) (root: N.class_Node__opt a) (record: N.class_Node__raw a)
    (l r: T.tree (a & bool))
  requires O.raw root record 1.0R ** holds (O.left record) l 1.0R ** holds (O.right record) r 1.0R
  ensures holds root (T.Branch l (O.entry record) r) 1.0R
{
  rewrite (O.raw root record 1.0R) as
    (O.held root (O.item record) (O.red record) (O.left record) (O.right record) 1.0R);
  fold (holds root (T.Branch l (O.entry record) r) 1.0R);
}

ghost fn seal_as (#a: Type0) (root: N.class_Node__opt a) (record: N.class_Node__raw a)
    (l r t: T.tree (a & bool))
  requires O.raw root record 1.0R ** holds (O.left record) l 1.0R ** holds (O.right record) r 1.0R **
    pure (t == T.Branch l (O.entry record) r)
  ensures holds root t 1.0R
{
  seal root record l r;
  rewrite (holds root (T.Branch l (O.entry record) r) 1.0R) as (holds root t 1.0R);
}

ghost fn seal_left_input (#a: Type0) (root old_left: N.class_Node__opt a)
    (record: N.class_Node__raw a) (l r t: T.tree (a & bool))
  requires O.raw root record 1.0R ** holds old_left l 1.0R ** holds (O.right record) r 1.0R **
    pure (old_left == O.left record /\ t == T.Branch l (O.entry record) r)
  ensures holds root t 1.0R
{
  reindex old_left (O.left record) l;
  seal_as root record l r t;
}

ghost fn seal_left_child (#a: Type0) (root old_left: N.class_Node__opt a)
    (parent child: N.class_Node__raw a) (l r t: T.tree (a & bool))
  preserves O.raw root parent 1.0R
  requires O.raw (O.left parent) child 1.0R ** holds old_left l 1.0R ** holds (O.right child) r 1.0R **
    pure (old_left == O.left child /\ t == T.Branch l (O.entry child) r)
  ensures holds (O.left parent) t 1.0R
{
  seal_left_input (O.left parent) old_left child l r t;
}

ghost fn seal_right_leaf (#a: Type0) (root: N.class_Node__opt a)
    (parent child: N.class_Node__raw a) (t: T.tree (a & bool))
  preserves O.raw root parent 1.0R
  requires O.raw (O.right parent) child 1.0R **
    pure (O.left child == B.null /\ O.right child == B.null /\
      t == T.Branch T.Leaf (O.entry child) T.Leaf)
  ensures holds (O.right parent) t 1.0R
{
  empty (O.left child) 1.0R;
  empty (O.right child) 1.0R;
  seal_as (O.right parent) child T.Leaf T.Leaf t;
}

let build_facts (#a: Type0) (s: FStar.Seq.seq a) (lo hi: int) (red: T.tree (a & bool))
  : Lemma (requires 0 <= lo /\ lo <= hi + 1 /\ hi < FStar.Seq.length s)
      (ensures T.Leaf? red ==> S.red_black (Build.build s lo hi red) /\
        S.keys (Build.build s lo hi red) == FStar.Seq.slice s lo (hi + 1))
  = if T.Leaf? red then Build.build_ok s lo hi

// The recursive equation is pure mathematics, independent of any heap model.
let build_step (#a: Type0) (s: FStar.Seq.seq a) (lo hi mid: int)
    (even: bool) (red: T.tree (a & bool))
  : Lemma
      (requires 0 <= lo /\ hi < FStar.Seq.length s /\ hi - lo + 1 >= 4 /\
        2 * mid <= lo + hi /\ lo + hi <= 2 * mid + 1 /\
        even == ((hi - lo + 1) % 2 = 0))
      (ensures Build.build s lo hi red ==
        T.Branch (Build.build s lo (mid - 1) red) (FStar.Seq.index s mid, false)
          (if even then Build.build s (mid + 2) hi (Build.leaf_of (FStar.Seq.index s (mid + 1)) true)
           else Build.build s (mid + 1) hi T.Leaf))
  = assert (mid == (lo + hi) / 2)

ghost fn empty_build (#a: Type0) (root: N.class_Node__opt a) (red: T.tree (a & bool))
    (s: FStar.Seq.seq a) (lo hi: int)
  requires holds root red 1.0R ** pure (B.is_null root /\ lo == hi + 1)
  ensures holds (B.null #(N.class_Node__raw a)) (Build.build s lo hi red) 1.0R
{
  cases root red 1.0R;
  rewrite (holds root red 1.0R) as (holds root (T.Leaf <: T.tree (a & bool)) 1.0R);
  unfold (holds root (T.Leaf <: T.tree (a & bool)) 1.0R);
  empty (B.null #(N.class_Node__raw a)) 1.0R;
  rewrite (holds (B.null #(N.class_Node__raw a)) (T.Leaf <: T.tree (a & bool)) 1.0R) as
    (holds (B.null #(N.class_Node__raw a)) (Build.build s lo hi red) 1.0R);
}

ghost fn seal_fresh (#a: Type0) (root: N.class_Node a) (key: a) (color: S.node_color)
  requires O.fresh root key color
  ensures holds root (Build.leaf_of key (S.Red? color)) 1.0R
{
  empty (B.null #(N.class_Node__raw a)) 1.0R;
  empty (B.null #(N.class_Node__raw a)) 1.0R;
  let record = { N.fld_Item = key; N.fld_Color = color; N.fld_Left = B.null; N.fld_Right = B.null };
  rewrite (O.fresh root key color) as (O.raw root record 1.0R);
  rewrite (holds (B.null #(N.class_Node__raw a)) T.Leaf 1.0R) as
    (holds (O.left record) T.Leaf 1.0R);
  rewrite (holds (B.null #(N.class_Node__raw a)) T.Leaf 1.0R) as
    (holds (O.right record) T.Leaf 1.0R);
  seal root record T.Leaf T.Leaf;
  rewrite (holds root (T.Branch T.Leaf (O.entry record) T.Leaf) 1.0R) as
    (holds root (Build.leaf_of key (S.Red? color)) 1.0R);
}

unfold let opened (#a: Type0) (root: N.class_Node__opt a) (t: T.tree (a & bool)) =
  exists* (record: N.class_Node__raw a).
    O.raw root record 1.0R **
    holds (O.left record) (T.left t) 1.0R ** holds (O.right record) (T.right t) 1.0R **
    pure (t == T.Branch (T.left t) (O.entry record) (T.right t))

ghost fn open_tree (#a: Type0) (root: N.class_Node__opt a) (t: T.tree (a & bool))
  requires holds root t 1.0R ** pure (T.Branch? t)
  ensures opened root t
{
  rewrite (holds root t 1.0R) as
    (holds root (T.Branch (T.left t) (T.Branch?._1 t) (T.right t)) 1.0R);
  unfold (holds root (T.Branch (T.left t) (T.Branch?._1 t) (T.right t)) 1.0R);
  with left right. _;
  let record = {
    N.fld_Item = fst (T.Branch?._1 t); N.fld_Color = O.color (snd (T.Branch?._1 t));
    N.fld_Left = left; N.fld_Right = right
  };
  rewrite (O.held root (fst (T.Branch?._1 t)) (snd (T.Branch?._1 t)) left right 1.0R) as
    (O.raw root record 1.0R);
  rewrite (holds left (T.left t) 1.0R) as (holds (O.left record) (T.left t) 1.0R);
  rewrite (holds right (T.right t) 1.0R) as (holds (O.right record) (T.right t) 1.0R);
  fold (opened root t);
}

ghost fn rec label_tree (#a: Type0) (root: N.class_Node__opt a)
    (t: T.tree (a & bool)) (p: perm)
  requires holds root t p
  returns labels: erased (O.tree a)
  ensures O.owns (reveal labels) p **
    pure (O.top (reveal labels) == root /\ O.values (reveal labels) == t)
  decreases t
{
  match t {
    T.Leaf -> {
      rewrite (holds root t p) as (holds root (T.Leaf <: T.tree (a & bool)) p);
      unfold (holds root (T.Leaf <: T.tree (a & bool)) p);
      fold (O.owns (T.Leaf <: O.tree a) p);
      hide (T.Leaf <: O.tree a)
    }
    T.Branch l e r -> {
      rewrite (holds root t p) as (holds root (T.Branch l e r) p);
      unfold (holds root (T.Branch l e r) p);
      with left right. _;
      let nl = label_tree left l p;
      let nr = label_tree right r p;
      rewrite (O.held root (fst e) (snd e) left right p) as
        (O.held root (fst e) (snd e) (O.top (reveal nl)) (O.top (reveal nr)) p);
      fold (O.owns (T.Branch (reveal nl) (root, e) (reveal nr)) p);
      hide (T.Branch (reveal nl) (root, e) (reveal nr))
    }
  }
}

ghost fn rec unlabel (#a: Type0) (n: O.tree a) (p: perm)
  requires O.owns n p
  ensures holds (O.top n) (O.values n) p
  decreases n
{
  match n {
    T.Leaf -> {
      rewrite (O.owns n p) as (O.owns (T.Leaf <: O.tree a) p);
      unfold (O.owns (T.Leaf <: O.tree a) p);
      empty (O.top n) p;
    }
    T.Branch l e r -> {
      rewrite (O.owns n p) as (O.owns (T.Branch l e r) p);
      unfold (O.owns (T.Branch l e r) p);
      unlabel l p;
      unlabel r p;
      fold (holds (fst e) (T.Branch (O.values l) (snd e) (O.values r)) p);
      rewrite (holds (fst e) (T.Branch (O.values l) (snd e) (O.values r)) p) as
        (holds (O.top n) (O.values n) p);
    }
  }
}

let adopted (#a: Type0) (old: O.state a) (labels: erased (O.tree a)) : Tot (O.state a) =
  O.replace (O.cleared old) labels

// Replacing a root retains the complete old active tree, not just its contents.
// The fresh labels are those obtained by unpacking `holds`, never a chosen map.
ghost fn adopt (#a: Type0) (old_root root: N.class_Node__opt a)
    (old: O.state a) (labels: erased (O.tree a))
  requires O.owner old_root old 1.0R ** O.owns (reveal labels) 1.0R **
    pure (O.top (reveal labels) == root)
  ensures O.owner root (adopted old labels) 1.0R **
    pure (O.good (O.active (adopted old labels)) /\
      O.active (adopted old labels) == reveal labels /\
      O.retired_state (adopted old labels) == O.Forest (O.active old) (O.retired_state old))
{
  E.facts (reveal labels);
  unfold (O.owner old_root old 1.0R);
  fold (O.retained (O.Forest (O.active old) (O.retired_state old)) 1.0R);
  fold (O.owner root (adopted old labels) 1.0R);
}
