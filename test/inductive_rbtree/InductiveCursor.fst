module InductiveCursor
#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Trade.Util
open Pulse.Lib.Forall.Util
module B = Pulse.Lib.Box
module N = Class_RbNode
module T = Pulse.Lib.CSharp.Tree
module P = Pulse.Lib.CSharp.RegionPath
module D = Pulse.Lib.CSharp.TopDown
module O = InductiveOwnership
module M = InductiveModel
module L = FStar.List.Tot
module RT = Pulse.Lib.CSharp.RegionTree
module R = Pulse.Lib.Reference

#set-options "--z3rlimit 10"

// RegionPath is used only for pure labelled trees, frames and plug.
// Ownership is the recursive separating predicate below, not a region/heap.
let tree (a: Type0) = D.nt (N.class_RbNode__raw a) a
let frame (a: Type0) = D.fr (N.class_RbNode__raw a) a
let same (#a: Type0) (n u: tree a) = n == u

let rec owns (#a: Type0) (t: tree a) : Tot slprop (decreases t) =
  match t with
  | T.Leaf -> emp
  | T.Branch l e r ->
    O.held (fst e) (fst (snd e)) (snd (snd e)) (P.top l) (P.top r) ** owns l ** owns r

ghost fn change (#a: Type0) (n u: tree a)
  requires owns n ** pure (same n u)
  ensures owns u
{
  rewrite (owns n) as (owns u);
}

ghost
fn rec label_tree (#a: Type0) (root: N.class_RbNode__opt a) (t: M.tree a)
  requires O.holds root t
  ensures exists* (n: tree a). owns n ** pure (P.top n == root /\ D.strip n == t)
  decreases t
{
  match t {
    T.Leaf -> {
      rewrite (O.holds root t) as (O.holds root (T.Leaf <: M.tree a));
      unfold (O.holds root (T.Leaf <: M.tree a));
      fold (owns (T.Leaf <: tree a));
      introduce exists* (n: tree a). owns n ** pure (P.top n == root /\ D.strip n == t)
        with (T.Leaf <: tree a);
    }
    T.Branch l e r -> {
      let k = fst e;
      let red = snd e;
      rewrite (O.holds root t) as (O.holds root (T.Branch l e r));
      unfold (O.holds root (T.Branch l e r));
      with v. _;
      label_tree v.fld_left l;
      with nl. _;
      label_tree v.fld_right r;
      with nr. _;
      rewrite (B.pts_to root v) as (O.held root k red (P.top nl) (P.top nr));
      fold (owns (T.Branch nl (root, (k, red)) nr));
      introduce exists* (n: tree a). owns n ** pure (P.top n == root /\ D.strip n == t)
        with (T.Branch nl (root, (k, red)) nr);
    }
  }
}

ghost
fn rec unlabel (#a: Type0) (t: tree a)
  requires owns t
  ensures O.holds (P.top t) (D.strip t)
  decreases t
{
  match t {
    T.Leaf -> {
      rewrite (owns t) as (owns (T.Leaf <: tree a));
      unfold (owns (T.Leaf <: tree a));
      O.empty #a ();
    }
    T.Branch l e r -> {
      rewrite (owns t) as (owns (T.Branch l e r));
      unfold (owns (T.Branch l e r));
      unlabel l;
      unlabel r;
      O.close_tree (fst e) (fst (snd e)) (snd (snd e)) (P.top l) (P.top r) (D.strip l) (D.strip r);
      rewrite (O.holds (fst e)
        (M.node (D.strip l) (fst (snd e)) (snd (snd e)) (D.strip r)))
        as (O.holds (P.top t) (D.strip t));
    }
  }
}

// The path owns the ancestors and off-path siblings. Its innermost link
// still points to hole; changing that pointer requires a real C# write.
let rec context (#a: Type0) (fs: list (frame a)) (hole: N.class_RbNode__opt a)
  : Tot slprop (decreases fs) =
  match fs with
  | [] -> emp
  | f :: rest ->
    O.held f.P.fbox (fst f.P.fval) (snd f.P.fval)
      (if f.P.went_right then P.top f.P.fsib else hole)
      (if f.P.went_right then hole else P.top f.P.fsib) **
    owns f.P.fsib ** context rest f.P.fbox

ghost
fn rec join (#a: Type0) (fs: list (frame a)) (t: tree a)
  requires context fs (P.top t) ** owns t
  ensures owns (P.plug fs t)
  decreases fs
{
  match fs {
    [] -> { unfold (context fs (P.top t)); }
    f :: rest -> {
      unfold (context fs (P.top t));
      if (f.P.went_right) {
        fold (owns (T.Branch f.P.fsib (f.P.fbox, f.P.fval) t));
        rewrite (owns (T.Branch f.P.fsib (f.P.fbox, f.P.fval) t)) as (owns (P.fill f t));
      } else {
        fold (owns (T.Branch t (f.P.fbox, f.P.fval) f.P.fsib));
        rewrite (owns (T.Branch t (f.P.fbox, f.P.fval) f.P.fsib)) as (owns (P.fill f t));
      };
      rewrite (context rest f.P.fbox) as (context rest (P.top (P.fill f t)));
      join rest (P.fill f t);
    }
  }
}

ghost
fn rec split (#a: Type0) (fs: list (frame a)) (t: tree a)
  requires owns (P.plug fs t)
  ensures context fs (P.top t) ** owns t
  decreases fs
{
  match fs {
    [] -> { fold (context fs (P.top t)); }
    f :: rest -> {
      split rest (P.fill f t);
      rewrite (context rest (P.top (P.fill f t))) as (context rest f.P.fbox);
      if (f.P.went_right) {
        rewrite (owns (P.fill f t)) as (owns (T.Branch f.P.fsib (f.P.fbox, f.P.fval) t));
        unfold (owns (T.Branch f.P.fsib (f.P.fbox, f.P.fval) t));
      } else {
        rewrite (owns (P.fill f t)) as (owns (T.Branch t (f.P.fbox, f.P.fval) f.P.fsib));
        unfold (owns (T.Branch t (f.P.fbox, f.P.fval) f.P.fsib));
      };
      fold (context fs (P.top t));
    }
  }
}

let restore (#a: Type0) (fs: list (frame a)) (hole: N.class_RbNode__opt a) =
  forall* (t: tree a).
    (pure (P.top t == hole) ** owns t) @==> owns (P.plug fs t)

ghost
fn context_trade (#a: Type0) (fs: list (frame a)) (hole: N.class_RbNode__opt a)
  requires context fs hole
  ensures restore fs hole
{
  intro (forall* (t: tree a).
    (pure (P.top t == hole) ** owns t) @==> owns (P.plug fs t))
    #(context fs hole) fn _ t {
      rewrite (context fs hole) as (context fs (P.top t));
      join fs t;
    };
  fold (restore fs hole);
}

ghost
fn focus (#a: Type0) (t: tree a) (x: N.class_RbNode__opt a)
  requires owns t
  ensures owns (P.sub t x) **
    restore (fst (P.focus t x)) (P.top (P.sub t x))
{
  P.focus_plug t x;
  rewrite (owns t) as (owns (P.plug (fst (P.focus t x)) (P.sub t x)));
  split (fst (P.focus t x)) (P.sub t x);
  context_trade (fst (P.focus t x)) (P.top (P.sub t x));
}

ghost
fn restore_focus (#a: Type0) (fs: list (frame a)) (t: tree a)
  requires owns t ** restore fs (P.top t)
  ensures owns (P.plug fs t)
{
  unfold (restore fs (P.top t));
  Pulse.Lib.Forall.Util.elim
    #_ #(fun s -> (pure (P.top s == P.top t) ** owns s) @==> owns (P.plug fs s)) t;
  Pulse.Lib.Trade.Util.elim _ _;
}

ghost fn cells_distinct (#a: Type0) (x y: N.class_RbNode__opt a)
    (vx vy: N.class_RbNode__raw a)
  preserves B.pts_to x vx ** B.pts_to y vy
  ensures pure (x =!= y)
{
  if (Pulse.Lib.CSharp.Region.eq_box x y) {
    rewrite (B.pts_to y vy) as (B.pts_to x vy);
    B.to_ref_pts_to x #1.0R #vx;
    B.to_ref_pts_to x #1.0R #vy;
    R.gather (B.box_to_ref x);
    R.pts_to_perm_bound (B.box_to_ref x);
    unreachable ();
  }
}

ghost fn rec apart_cell (#a: Type0) (t: tree a) (x: N.class_RbNode__opt a)
    (v: N.class_RbNode__raw a)
  preserves owns t ** B.pts_to x v
  ensures pure (~ (L.memP x (P.nboxes t)))
  decreases t
{
  match t {
    T.Leaf -> {}
    T.Branch l e r -> {
      rewrite (owns t) as (owns (T.Branch l e r));
      unfold (owns (T.Branch l e r));
      cells_distinct x (fst e) v
        {N.fld_key = fst (snd e); N.fld_red = snd (snd e);
         N.fld_left = P.top l; N.fld_right = P.top r};
      apart_cell l x v;
      apart_cell r x v;
      fold (owns (T.Branch l e r));
    }
  }
}

ghost fn rec apart (#a: Type0) (t u: tree a)
  preserves owns t ** owns u
  ensures pure (RT.disjoint (P.nboxes t) (P.nboxes u))
  decreases t
{
  match t {
    T.Leaf -> {}
    T.Branch l e r -> {
      rewrite (owns t) as (owns (T.Branch l e r));
      unfold (owns (T.Branch l e r));
      apart_cell u (fst e)
        {N.fld_key = fst (snd e); N.fld_red = snd (snd e);
         N.fld_left = P.top l; N.fld_right = P.top r};
      apart l u;
      apart r u;
      fold (owns (T.Branch l e r));
    }
  }
}

ghost fn rec facts (#a: Type0) (t: tree a)
  preserves owns t
  ensures pure (RT.distinct (P.nboxes t) /\ D.all_nonnull t)
  decreases t
{
  match t {
    T.Leaf -> {}
    T.Branch l e r -> {
      rewrite (owns t) as (owns (T.Branch l e r));
      unfold (owns (T.Branch l e r));
      B.pts_to_not_null (fst e);
      apart_cell l (fst e)
        {N.fld_key = fst (snd e); N.fld_red = snd (snd e);
         N.fld_left = P.top l; N.fld_right = P.top r};
      apart_cell r (fst e)
        {N.fld_key = fst (snd e); N.fld_red = snd (snd e);
         N.fld_left = P.top l; N.fld_right = P.top r};
      apart l r;
      facts l;
      facts r;
      RT.distinct_append (P.nboxes l) (P.nboxes r);
      fold (owns (T.Branch l e r));
    }
  }

}

  unfold let labelled (#a: Type0) (root: N.class_RbNode__opt a) (t: M.tree a) =
    exists* (n: tree a). owns n **
      pure (P.top n == root /\ D.strip n == t /\
        RT.distinct (P.nboxes n) /\ D.all_nonnull n)

  ghost fn label_public (#a: Type0) (root: N.class_RbNode__opt a) (t: M.tree a)
    requires O.holds root t
    ensures labelled root t
  {
    label_tree root t;
    with n. _;
    facts n;
  }

  ghost fn unlabel_public (#a: Type0) (root: N.class_RbNode__opt a) (t: M.tree a) (n: tree a)
    requires owns n ** pure (P.top n == root /\ D.strip n == t)
    ensures O.holds root t
  {
    unlabel n;
    rewrite (O.holds (P.top n) (D.strip n)) as (O.holds root t);
  }

  ghost fn unlabel_exists (#a: Type0) (root: N.class_RbNode__opt a) (t: M.tree a)
    requires labelled root t
    ensures O.holds root t
  {
    unfold (labelled root t);
    with n. _;
    unlabel_public root t n;
  }

  let lookup (#a: Type0) (n: tree a) (x: N.class_RbNode__opt a) = D.strip (P.sub n x)
  let member (#a: Type0) (n: tree a) (x: N.class_RbNode__opt a) = L.memP x (P.nboxes n)
  let good (#a: Type0) (n: tree a) = RT.distinct (P.nboxes n) /\ D.all_nonnull n

  let lookup_root (#a: Type0) (n: tree a)
    : Lemma (requires good n)
        (ensures lookup n (P.top n) == D.strip n /\
          (P.top n =!= B.null ==> member n (P.top n)) /\
          lookup n B.null == T.Leaf)
    = D.sub_top [] n; D.sub_absent n B.null

  let lookup_children (#a: Type0) (n: tree a) (x: N.class_RbNode__opt a)
    : Lemma (requires good n /\ member n x)
        (ensures (
          let s = P.sub n x in
          T.Branch? s /\ P.top s == x /\
          P.sub n (P.top (T.left s)) == T.left s /\
          P.sub n (P.top (T.right s)) == T.right s /\
          (P.top (T.left s) =!= B.null ==> member n (P.top (T.left s))) /\
          (P.top (T.right s) =!= B.null ==> member n (P.top (T.right s)))))
    = P.focus_plug n x;
      let fs = fst (P.focus n x) in
      let s = P.sub n x in
      match s with
      | T.Branch l e r ->
        let fl = {P.went_right=false; P.fbox=fst e; P.fval=snd e; P.fsib=r} in
        let fr = {P.went_right=true; P.fbox=fst e; P.fval=snd e; P.fsib=l} in
        D.sub_top (fl::fs) l;
        D.sub_top (fr::fs) r;
        P.mem_plug (P.top l) (fl::fs) l;
        P.mem_plug (P.top r) (fr::fs) r

  unfold let opened (#a: Type0) (n: tree a) (x: N.class_RbNode__opt a) =
    exists* (k: a) (red: bool) (l r: N.class_RbNode__opt a).
      O.held x k red l r **
      owns (T.left (P.sub n x)) ** owns (T.right (P.sub n x)) **
      restore (fst (P.focus n x)) x **
      pure (
        P.sub n x == T.Branch (T.left (P.sub n x)) (x, (k, red)) (T.right (P.sub n x)) /\
        l == P.top (T.left (P.sub n x)) /\ r == P.top (T.right (P.sub n x)) /\
        lookup n x == M.node (lookup n l) k red (lookup n r) /\
        T.size (lookup n l) < T.size (lookup n x) /\
        T.size (lookup n r) < T.size (lookup n x) /\
        (l =!= B.null ==> member n l) /\ (r =!= B.null ==> member n r))

  ghost fn open_node (#a: Type0) (n: tree a) (x: N.class_RbNode__opt a)
    requires owns n ** pure (good n /\ member n x)
    ensures opened n x
  {
    lookup_children n x;
    focus n x;
    rewrite (restore (fst (P.focus n x)) (P.top (P.sub n x)))
      as (restore (fst (P.focus n x)) x);
    rewrite (owns (P.sub n x)) as
      (owns (T.Branch (T.left (P.sub n x)) (T.Branch?._1 (P.sub n x)) (T.right (P.sub n x))));
    unfold (owns (T.Branch (T.left (P.sub n x)) (T.Branch?._1 (P.sub n x)) (T.right (P.sub n x))));
    rewrite each (fst (T.Branch?._1 (P.sub n x))) as x;
  }

  ghost fn close_node (#a: Type0) (n: tree a) (x: N.class_RbNode__opt a)
    requires opened n x
    ensures owns n
  {
    unfold (opened n x);
    with k red l r. _;
    rewrite (O.held x k red l r) as
      (O.held x k red (P.top (T.left (P.sub n x))) (P.top (T.right (P.sub n x))));
    fold (owns (T.Branch (T.left (P.sub n x)) (x, (k, red)) (T.right (P.sub n x))));
    rewrite (owns (T.Branch (T.left (P.sub n x)) (x, (k, red)) (T.right (P.sub n x))))
      as (owns (P.sub n x));
    rewrite (restore (fst (P.focus n x)) x) as
      (restore (fst (P.focus n x)) (P.top (P.sub n x)));
    restore_focus (fst (P.focus n x)) (P.sub n x);
    P.focus_plug n x;
    rewrite (owns (P.plug (fst (P.focus n x)) (P.sub n x))) as (owns n);
  }
