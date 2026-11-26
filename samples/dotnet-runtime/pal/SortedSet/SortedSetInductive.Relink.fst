module SortedSetInductive.Relink
#lang-pulse

open Pulse.Lib.Pervasives
module C = SortedSetInductive.Cursor
module O = SortedSetInductive.Ownership
module N = Class_Node
module P = Pulse.Lib.CSharp.RegionPath
module D = Pulse.Lib.CSharp.TopDown
module T = Pulse.Lib.CSharp.Tree
module B = Pulse.Lib.Box

#set-options "--z3rlimit 10"

let path (#a: Type0) (n: O.tree a) (x: N.class_Node__opt a) = fst (P.focus n x)
let replace (#a: Type0) (n: O.tree a) (x: N.class_Node__opt a) (u: O.tree a) =
  P.replace n x u
let parent (#a: Type0) (n: O.tree a) (x: N.class_Node__opt a) = D.parent_of n x
let pending (#a: Type0) (n: O.tree a) (x: N.class_Node__opt a) =
  C.context (path n x) x 1.0R

ghost fn cut (#a: Type0) (n: O.tree a) (x: N.class_Node__opt a)
  requires O.owns n 1.0R ** pure (O.member n x)
  ensures O.owns (P.sub n x) 1.0R ** pending n x
{
  P.focus_plug n x;
  rewrite (O.owns n 1.0R) as (O.owns (P.plug (path n x) (P.sub n x)) 1.0R);
  C.split (path n x) (P.sub n x) 1.0R;
  rewrite (C.context (path n x) (P.top (P.sub n x)) 1.0R) as (pending n x);
}

ghost fn join_same (#a: Type0) (n: O.tree a) (x: N.class_Node__opt a) (u: O.tree a)
  requires pending n x ** O.owns u 1.0R ** pure (P.top u == x)
  ensures O.owns (P.replace n x u) 1.0R
{
  rewrite (pending n x) as (C.context (path n x) (P.top u) 1.0R);
  C.join (path n x) u 1.0R;
  rewrite (O.owns (P.plug (path n x) u) 1.0R) as (O.owns (P.replace n x u) 1.0R);
}

let side (#a: Type0) (fs: list (C.frame a)) =
  match fs with [] -> false | f::_ -> f.P.went_right
let key (#a: Type0) (fs: list (C.frame a)) (d: a) =
  match fs with [] -> d | f::_ -> fst f.P.fval
let red (#a: Type0) (fs: list (C.frame a)) =
  match fs with [] -> false | f::_ -> snd f.P.fval
let sib (#a: Type0) (fs: list (C.frame a)) : O.tree a =
  match fs with [] -> T.Leaf | f::_ -> f.P.fsib
let left (#a: Type0) (fs: list (C.frame a)) (hole: N.class_Node__opt a) =
  if side fs then P.top (sib fs) else hole
let right (#a: Type0) (fs: list (C.frame a)) (hole: N.class_Node__opt a) =
  if side fs then hole else P.top (sib fs)
let tail (#a: Type0) (fs: list (C.frame a)) : slprop =
  match fs with
  | [] -> emp
  | f::rest -> O.owns f.P.fsib 1.0R ** C.context rest f.P.fbox 1.0R

unfold let cell (#a: Type0) (n: O.tree a) (x p hole: N.class_Node__opt a) =
  exists* (v: N.class_Node__raw a).
    O.raw p v 1.0R ** tail (path n x) **
    pure (Cons? (path n x) /\ p == D.parent_of n x /\
      v.N.fld_Item == key (path n x) v.N.fld_Item /\
      v.N.fld_Color == O.color (red (path n x)) /\
      v.N.fld_Left == left (path n x) hole /\ v.N.fld_Right == right (path n x) hole /\
      (left (path n x) x == x <==> not (side (path n x))))

let rec top_plug (#a: Type0) (fs: list (C.frame a)) (s u: O.tree a)
  : Lemma (requires Cons? fs)
      (ensures P.top (P.plug fs s) == P.top (P.plug fs u))
      (decreases fs)
  = match fs with
    | f::[] -> ()
    | f::rest -> top_plug rest (P.fill f s) (P.fill f u)

let link_facts (#a: Type0) (n: O.tree a) (x: N.class_Node__opt a)
  : Lemma (requires O.good n /\ O.member n x)
      (ensures
        (D.parent_of n x == B.null <==> Nil? (path n x)) /\
        (Cons? (path n x) ==> P.top (sib (path n x)) =!= x))
  = P.focus_plug n x;
    P.distinct_plug (path n x) (P.sub n x);
    match path n x with
    | [] -> ()
    | f::rest ->
      P.mem_plug f.P.fbox (f::rest) (P.sub n x);
      P.mem_plug (P.top f.P.fsib) (f::rest) (P.sub n x);
      if T.Branch? f.P.fsib then () else ()

let replace_top (#a: Type0) (n: O.tree a) (x: N.class_Node__opt a) (u: O.tree a)
  : Lemma (requires Cons? (path n x))
      (ensures P.top (P.replace n x u) == P.top n)
  = P.focus_plug n x;
    top_plug (path n x) (P.sub n x) u

ghost fn open_parent (#a: Type0) (n: O.tree a) (x p: N.class_Node__opt a)
  requires pending n x **
    pure (O.good n /\ O.member n x /\ p == D.parent_of n x /\ p =!= B.null)
  ensures cell n x p x ** pure (left (path n x) x == x <==> not (side (path n x)))
{
  link_facts n x;
  let fs = path n x;
  match fs {
    f::rest -> {
      rewrite (pending n x) as (C.context (f::rest) x 1.0R);
      unfold (C.context (f::rest) x 1.0R);
      rewrite (O.held f.P.fbox (fst f.P.fval) (snd f.P.fval)
        (if f.P.went_right then P.top f.P.fsib else x)
        (if f.P.went_right then x else P.top f.P.fsib) 1.0R)
        as (O.held p (fst f.P.fval) (snd f.P.fval)
          (left fs x) (right fs x) 1.0R);
      rewrite (O.owns f.P.fsib 1.0R ** C.context rest f.P.fbox 1.0R) as (tail (path n x));
    }
  }
}

ghost fn close_parent (#a: Type0) (n: O.tree a) (x p: N.class_Node__opt a) (u: O.tree a)
  requires cell n x p (P.top u) ** O.owns u 1.0R
  ensures O.owns (P.replace n x u) 1.0R ** pure (P.top (P.replace n x u) == P.top n)
{
  unfold (cell n x p (P.top u));
  with v. _;
  let fs = path n x;
  match fs {
    f::rest -> {
      rewrite (tail (path n x)) as (O.owns f.P.fsib 1.0R ** C.context rest f.P.fbox 1.0R);
      rewrite (O.raw p v 1.0R) as
        (O.held f.P.fbox (fst f.P.fval) (snd f.P.fval)
          (if f.P.went_right then P.top f.P.fsib else P.top u)
          (if f.P.went_right then P.top u else P.top f.P.fsib) 1.0R);
      fold (C.context (f::rest) (P.top u) 1.0R);
      C.join fs u 1.0R;
      rewrite (O.owns (P.plug fs u) 1.0R) as (O.owns (P.replace n x u) 1.0R);
      replace_top n x u;
      assert (pure (P.top (P.replace n x u) == P.top n));
    }
  }
}

ghost fn close_root (#a: Type0) (n: O.tree a) (x: N.class_Node__opt a) (u: O.tree a)
  requires pending n x ** O.owns u 1.0R **
    pure (O.good n /\ O.member n x /\ D.parent_of n x == B.null)
  ensures O.owns (P.replace n x u) 1.0R ** pure (P.top (P.replace n x u) == P.top u)
{
  link_facts n x;
  rewrite (pending n x) as (C.context ([] <: list (C.frame a)) x 1.0R);
  unfold (C.context ([] <: list (C.frame a)) x 1.0R);
  rewrite (O.owns u 1.0R) as (O.owns (P.replace n x u) 1.0R);
}
