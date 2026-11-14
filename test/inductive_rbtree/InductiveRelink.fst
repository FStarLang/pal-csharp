module InductiveRelink
#lang-pulse

open Pulse.Lib.Pervasives
module C = InductiveCursor
module O = InductiveOwnership
module N = Class_RbNode
module P = Pulse.Lib.CSharp.RegionPath
module D = Pulse.Lib.CSharp.TopDown
module RT = Pulse.Lib.CSharp.RegionTree
module T = Pulse.Lib.CSharp.Tree
module B = Pulse.Lib.Box
module L = FStar.List.Tot

#set-options "--z3rlimit 10"

let path (#a: Type0) (n: C.tree a) (x: N.class_RbNode__opt a) = fst (P.focus n x)
let pending (#a: Type0) (n: C.tree a) (x: N.class_RbNode__opt a) =
  C.context (path n x) x

ghost fn cut (#a: Type0) (n: C.tree a) (x: N.class_RbNode__opt a)
  requires C.owns n ** pure (C.member n x)
  ensures C.owns (P.sub n x) ** pending n x
{
  P.focus_plug n x;
  rewrite (C.owns n) as (C.owns (P.plug (path n x) (P.sub n x)));
  C.split (path n x) (P.sub n x);
  rewrite (C.context (path n x) (P.top (P.sub n x))) as (pending n x);
}

ghost fn join_same (#a: Type0) (n: C.tree a) (x: N.class_RbNode__opt a) (u: C.tree a)
  requires pending n x ** C.owns u ** pure (P.top u == x)
  ensures C.owns (P.replace n x u)
{
  rewrite (pending n x) as (C.context (path n x) (P.top u));
  C.join (path n x) u;
  rewrite (C.owns (P.plug (path n x) u)) as (C.owns (P.replace n x u));
}

let side (#a: Type0) (fs: list (C.frame a)) =
  match fs with [] -> false | f::_ -> f.P.went_right
let key (#a: Type0) (fs: list (C.frame a)) (d: a) =
  match fs with [] -> d | f::_ -> fst f.P.fval
let red (#a: Type0) (fs: list (C.frame a)) =
  match fs with [] -> false | f::_ -> snd f.P.fval
let sib (#a: Type0) (fs: list (C.frame a)) : C.tree a =
  match fs with [] -> T.Leaf | f::_ -> f.P.fsib
let left (#a: Type0) (fs: list (C.frame a)) (hole: N.class_RbNode__opt a) =
  if side fs then P.top (sib fs) else hole
let right (#a: Type0) (fs: list (C.frame a)) (hole: N.class_RbNode__opt a) =
  if side fs then hole else P.top (sib fs)
let tail (#a: Type0) (fs: list (C.frame a)) : slprop =
  match fs with
  | [] -> emp
  | f::rest -> C.owns f.P.fsib ** C.context rest f.P.fbox

unfold let cell (#a: Type0) (n: C.tree a) (x p hole: N.class_RbNode__opt a) =
  exists* (k: a) (col: bool) (l r: N.class_RbNode__opt a).
    O.held p k col l r ** tail (path n x) **
    pure (Cons? (path n x) /\ p == D.parent_of n x /\
      k == key (path n x) k /\ col == red (path n x) /\
      l == left (path n x) hole /\ r == right (path n x) hole /\
      (left (path n x) x == x <==> not (side (path n x))))

let rec top_plug (#a: Type0) (fs: list (C.frame a)) (s u: C.tree a)
  : Lemma (requires Cons? fs)
      (ensures P.top (P.plug fs s) == P.top (P.plug fs u))
      (decreases fs)
  = match fs with
    | f::[] -> ()
    | f::rest -> top_plug rest (P.fill f s) (P.fill f u)

let link_facts (#a: Type0) (n: C.tree a) (x: N.class_RbNode__opt a)
  : Lemma (requires C.good n /\ C.member n x)
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

let replace_top (#a: Type0) (n: C.tree a) (x: N.class_RbNode__opt a) (u: C.tree a)
  : Lemma (requires Cons? (path n x))
      (ensures P.top (P.replace n x u) == P.top n)
  = P.focus_plug n x;
    top_plug (path n x) (P.sub n x) u

ghost fn open_parent (#a: Type0) (n: C.tree a) (x p: N.class_RbNode__opt a)
  requires pending n x **
    pure (C.good n /\ C.member n x /\ p == D.parent_of n x /\ p =!= B.null)
  ensures cell n x p x ** pure (left (path n x) x == x <==> not (side (path n x)))
{
  link_facts n x;
  let fs = path n x;
  match fs {
    f::rest -> {
      rewrite (pending n x) as (C.context (f::rest) x);
      unfold (C.context (f::rest) x);
      rewrite (O.held f.P.fbox (fst f.P.fval) (snd f.P.fval)
        (if f.P.went_right then P.top f.P.fsib else x)
        (if f.P.went_right then x else P.top f.P.fsib))
        as (O.held p (fst f.P.fval) (snd f.P.fval)
          (left fs x) (right fs x));
      rewrite (C.owns f.P.fsib ** C.context rest f.P.fbox) as (tail (path n x));
    }
  }
}

ghost fn close_parent (#a: Type0) (n: C.tree a) (x p: N.class_RbNode__opt a) (u: C.tree a)
  requires cell n x p (P.top u) ** C.owns u
  ensures C.owns (P.replace n x u) ** pure (P.top (P.replace n x u) == P.top n)
{
  unfold (cell n x p (P.top u));
  with k col l r. _;
  let fs = path n x;
  match fs {
    f::rest -> {
      rewrite (tail (path n x)) as (C.owns f.P.fsib ** C.context rest f.P.fbox);
      rewrite (O.held p k col l r) as
        (O.held f.P.fbox (fst f.P.fval) (snd f.P.fval)
          (if f.P.went_right then P.top f.P.fsib else P.top u)
          (if f.P.went_right then P.top u else P.top f.P.fsib));
      fold (C.context (f::rest) (P.top u));
      C.join fs u;
      rewrite (C.owns (P.plug fs u)) as (C.owns (P.replace n x u));
      replace_top n x u;
      assert (pure (P.top (P.replace n x u) == P.top n));
    }
  }
}

ghost fn close_root (#a: Type0) (n: C.tree a) (x: N.class_RbNode__opt a) (u: C.tree a)
  requires pending n x ** C.owns u **
    pure (C.good n /\ C.member n x /\ D.parent_of n x == B.null)
  ensures C.owns (P.replace n x u) ** pure (P.top (P.replace n x u) == P.top u)
{
  link_facts n x;
  rewrite (pending n x) as (C.context ([] <: list (C.frame a)) x);
  unfold (C.context ([] <: list (C.frame a)) x);
  rewrite (C.owns u) as (C.owns (P.replace n x u));
}
