module SortedSetInductive.Frontier
#lang-pulse

open Pulse.Lib.Pervasives
module O = SortedSetInductive.Ownership
module L = SortedSetInductive.Local
module K = SortedSetInductive.Relink
module N = Class_Node
module T = Pulse.Lib.CSharp.Tree
module P = Pulse.Lib.CSharp.RegionPath
module D = Pulse.Lib.CSharp.TopDown
module B = Pulse.Lib.Box

#set-options "--z3rlimit 10"

let snapshot (#a: Type0) (n: O.tree a{T.Branch? n}) : N.class_Node__raw a =
  let T.Branch l (_, (key, red)) r = n in
  { N.fld_Item=key; N.fld_Color=O.color red; N.fld_Left=P.top l; N.fld_Right=P.top r }

let optional (#a: Type0) (n: O.tree a) =
  match n with T.Leaf -> None | T.Branch _ _ _ -> Some (snapshot n)

let snapshot_facts (#a: Type0) (n: O.tree a) (v: N.class_Node__raw a)
  : Lemma (requires optional n == Some v)
      (ensures T.Branch? n /\
        n == T.Branch (T.left n) (P.top n, O.entry v) (T.right n) /\
        v.N.fld_Left == P.top (T.left n) /\ v.N.fld_Right == P.top (T.right n))
  = match n with
    | T.Leaf -> ()
    | T.Branch l (x, (key, red)) r -> if red then () else ()

let optional_red (#a: Type0) (n: O.tree a)
  : Lemma (O.nullable_red (optional n) == D.nred n)
  = match n with
    | T.Leaf -> ()
    | T.Branch l (x, (key, red)) r -> if red then () else ()

let read_facts (#a: Type0) (n: O.tree a)
  : Lemma (D.is4 n ==
      (O.nullable_red (optional (T.left n)) && O.nullable_red (optional (T.right n))))
  = optional_red (T.left n); optional_red (T.right n)

unfold let below (#a: Type0) (n: O.tree a) =
  O.owns (T.left n) 1.0R ** O.owns (T.right n) 1.0R

ghost fn open_optional (#a: Type0) (n: O.tree a)
  requires O.owns n 1.0R
  ensures O.nullable_raw (P.top n) (optional n) 1.0R ** below n
{
  match n {
    T.Leaf -> {
      unfold (O.owns n 1.0R);
      fold (O.owns (T.Leaf <: O.tree a) 1.0R);
      fold (O.owns (T.Leaf <: O.tree a) 1.0R);
      rewrite (pure (optional n == None)) as
        (O.nullable_raw (P.top n) (optional n) 1.0R);
    }
    T.Branch l e r -> {
      L.open_node (P.top n) n;
      unfold (L.opened (P.top n) n);
      with v. _;
      rewrite (O.raw (P.top n) v 1.0R) as (O.raw (P.top n) (snapshot n) 1.0R);
      O.close_nullable (P.top n) (optional n) 1.0R;
    }
  }
}

ghost fn close_optional (#a: Type0) (n: O.tree a)
  requires O.nullable_raw (P.top n) (optional n) 1.0R ** below n
  ensures O.owns n 1.0R
{
  match n {
    T.Leaf -> {
      rewrite (O.nullable_raw (P.top n) (optional n) 1.0R) as (pure (optional n == None));
      unfold (below n);
      rewrite (O.owns (T.left n) 1.0R) as emp;
      rewrite (O.owns (T.right n) 1.0R) as emp;
      fold (O.owns n 1.0R);
    }
    T.Branch l e r -> {
      if (B.is_null (P.top n)) {
        rewrite (O.nullable_raw (P.top n) (optional n) 1.0R) as (pure (optional n == None));
        assert (pure False);
      } else {
        O.open_nullable (P.top n) (optional n) 1.0R;
        unfold (O.nullable_opened (P.top n) (optional n) 1.0R);
        with v. _;
        fold (L.opened (P.top n) n);
        L.close_node (P.top n) n;
      }
    }
  }
}

// The receiver's actual raw fields index the child resources. This is an
// ordinary predicate, not compiler-directed discovery of child ownership.
unfold let read_cells (#a: Type0) (x: N.class_Node__opt a) (n: O.tree a) =
  exists* (v: N.class_Node__raw a).
    O.raw x v 1.0R **
    O.nullable_raw v.N.fld_Left (optional (T.left n)) 1.0R **
    O.nullable_raw v.N.fld_Right (optional (T.right n)) 1.0R **
    below (T.left n) ** below (T.right n) **
    pure (x == P.top n /\ optional n == Some v)

unfold let split_cells (#a: Type0) (x: N.class_Node__opt a) (n: O.tree a) =
  exists* (v vl vr: N.class_Node__raw a).
    O.raw x v 1.0R ** O.raw v.N.fld_Left vl 1.0R ** O.raw v.N.fld_Right vr 1.0R **
    below (T.left n) ** below (T.right n) **
    pure (x == P.top n /\ optional n == Some v /\
      optional (T.left n) == Some vl /\ optional (T.right n) == Some vr)

unfold let split_after (#a: Type0) (x: N.class_Node__opt a) (n: O.tree a) =
  exists* (v vl vr: N.class_Node__raw a).
    O.raw x v 1.0R ** O.raw v.N.fld_Left vl 1.0R ** O.raw v.N.fld_Right vr 1.0R **
    below (T.left n) ** below (T.right n) **
    pure (x == P.top (D.split4n n) /\ optional (D.split4n n) == Some v /\
      optional (T.left (D.split4n n)) == Some vl /\ optional (T.right (D.split4n n)) == Some vr)

ghost fn open_read (#a: Type0) (n: O.tree a) (x: N.class_Node__opt a)
  requires O.owns n 1.0R ** pure (O.good n /\ O.member n x)
  ensures read_cells x (P.sub n x) ** K.pending n x
{
  SortedSetInductive.Cursor.lookup_children n x;
  K.cut n x;
  L.open_node x (P.sub n x);
  unfold (L.opened x (P.sub n x));
  with v. _;
  open_optional (T.left (P.sub n x));
  open_optional (T.right (P.sub n x));
  rewrite (O.nullable_raw (P.top (T.left (P.sub n x))) (optional (T.left (P.sub n x))) 1.0R)
    as (O.nullable_raw v.N.fld_Left (optional (T.left (P.sub n x))) 1.0R);
  rewrite (O.nullable_raw (P.top (T.right (P.sub n x))) (optional (T.right (P.sub n x))) 1.0R)
    as (O.nullable_raw v.N.fld_Right (optional (T.right (P.sub n x))) 1.0R);
  fold (read_cells x (P.sub n x));
}

ghost fn close_read (#a: Type0) (n: O.tree a) (x: N.class_Node__opt a)
  requires read_cells x (P.sub n x) ** K.pending n x ** pure (O.member n x)
  ensures O.owns n 1.0R
{
  unfold (read_cells x (P.sub n x));
  with v. _;
  snapshot_facts (P.sub n x) v;
  rewrite each v.N.fld_Left as (P.top (T.left (P.sub n x)));
  rewrite each v.N.fld_Right as (P.top (T.right (P.sub n x)));
  close_optional (T.left (P.sub n x));
  close_optional (T.right (P.sub n x));
  fold (L.opened x (P.sub n x));
  L.close_node x (P.sub n x);
  K.join_same n x (P.sub n x);
  P.focus_plug n x;
  rewrite (O.owns (P.replace n x (P.sub n x)) 1.0R) as (O.owns n 1.0R);
}

ghost fn open_split (#a: Type0) (n: O.tree a) (x: N.class_Node__opt a)
  requires O.owns n 1.0R ** pure (O.member n x /\ D.is4 (P.sub n x))
  ensures split_cells x (P.sub n x) ** K.pending n x
{
  P.focus_plug n x;
  K.cut n x;
  L.open_node x (P.sub n x);
  unfold (L.opened x (P.sub n x));
  with v. _;
  L.open_node v.N.fld_Left (T.left (P.sub n x));
  L.open_node v.N.fld_Right (T.right (P.sub n x));
  unfold (L.opened v.N.fld_Left (T.left (P.sub n x)));
  with vl. _;
  unfold (L.opened v.N.fld_Right (T.right (P.sub n x)));
  with vr. _;
  fold (split_cells x (P.sub n x));
}

ghost fn close_split (#a: Type0) (n: O.tree a) (x: N.class_Node__opt a)
  requires split_after x (P.sub n x) ** K.pending n x **
    pure (O.member n x /\ D.is4 (P.sub n x))
  ensures O.owns (P.replace n x (D.split4n (P.sub n x))) 1.0R
{
  let u = D.split4n (P.sub n x);
  unfold (split_after x (P.sub n x));
  with v vl vr. _;
  snapshot_facts u v;
  snapshot_facts (T.left u) vl;
  snapshot_facts (T.right u) vr;
  unfold (below (T.left (P.sub n x)));
  unfold (below (T.right (P.sub n x)));
  L.color_leaves (T.left (P.sub n x)) false;
  L.color_leaves (T.right (P.sub n x)) false;
  rewrite each (D.recolorn (T.left (P.sub n x)) false) as (T.left u);
  rewrite each (D.recolorn (T.right (P.sub n x)) false) as (T.right u);
  fold (L.opened v.N.fld_Left (T.left u));
  fold (L.opened v.N.fld_Right (T.right u));
  L.close_node v.N.fld_Left (T.left u);
  L.close_node v.N.fld_Right (T.right u);
  fold (L.opened x u);
  L.close_node x u;
  K.join_same n x u;
  rewrite (O.owns (P.replace n x u) 1.0R) as
    (O.owns (P.replace n x (D.split4n (P.sub n x))) 1.0R);
}

let optional_at (#a: Type0) (n: O.tree a) (x: N.class_Node__opt a) =
  if B.is_null x then None else optional (P.sub n x)

let optional_rest (#a: Type0) (n: O.tree a) (x: N.class_Node__opt a) =
  if B.is_null x then O.owns n 1.0R
  else below (P.sub n x) ** K.pending n x

ghost fn open_optional_at (#a: Type0) (n: O.tree a) (x: N.class_Node__opt a)
  requires O.owns n 1.0R ** pure (O.good n /\ (x == B.null \/ O.member n x))
  ensures O.nullable_raw x (optional_at n x) 1.0R ** optional_rest n x **
    pure (O.nullable_red (optional_at n x) == D.nred (P.sub n x))
{
  if (B.is_null x) {
    D.sub_absent n x;
    rewrite (pure (optional_at n x == None)) as (O.nullable_raw x (optional_at n x) 1.0R);
    rewrite (O.owns n 1.0R) as (optional_rest n x);
  } else {
    SortedSetInductive.Cursor.lookup_children n x;
    K.cut n x;
    open_optional (P.sub n x);
    optional_red (P.sub n x);
    rewrite (O.nullable_raw (P.top (P.sub n x)) (optional (P.sub n x)) 1.0R)
      as (O.nullable_raw x (optional_at n x) 1.0R);
    rewrite (below (P.sub n x) ** K.pending n x) as (optional_rest n x);
  }
}

ghost fn close_optional_at (#a: Type0) (n: O.tree a) (x: N.class_Node__opt a)
  requires O.nullable_raw x (optional_at n x) 1.0R ** optional_rest n x **
    pure (O.good n /\ (x == B.null \/ O.member n x))
  ensures O.owns n 1.0R
{
  if (B.is_null x) {
    rewrite (O.nullable_raw x (optional_at n x) 1.0R) as (pure (optional_at n x == None));
    rewrite (optional_rest n x) as (O.owns n 1.0R);
  } else {
    SortedSetInductive.Cursor.lookup_children n x;
    rewrite (optional_rest n x) as (below (P.sub n x) ** K.pending n x);
    rewrite (O.nullable_raw x (optional_at n x) 1.0R)
      as (O.nullable_raw (P.top (P.sub n x)) (optional (P.sub n x)) 1.0R);
    close_optional (P.sub n x);
    K.join_same n x (P.sub n x);
    P.focus_plug n x;
    rewrite (O.owns (P.replace n x (P.sub n x)) 1.0R) as (O.owns n 1.0R);
  }
}
