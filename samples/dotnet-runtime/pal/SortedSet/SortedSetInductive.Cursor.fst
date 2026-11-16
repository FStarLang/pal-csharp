module SortedSetInductive.Cursor
#lang-pulse

open Pulse.Lib.Pervasives
module O = SortedSetInductive.Ownership
module N = Class_Node
module T = Pulse.Lib.CSharp.Tree
module P = Pulse.Lib.CSharp.RegionPath
module D = Pulse.Lib.CSharp.TopDown
module B = Pulse.Lib.Box

#set-options "--z3rlimit 10"

let frame (a: Type0) = D.fr (N.class_Node__raw a) a

// Ancestors and off-path siblings, with the original child link to the hole.
let rec context (#a: Type0) (fs: list (frame a)) (hole: N.class_Node__opt a) (p: perm)
  : Tot slprop (decreases fs) =
  match fs with
  | [] -> emp
  | f :: rest ->
    O.held f.P.fbox (fst f.P.fval) (snd f.P.fval)
      (if f.P.went_right then P.top f.P.fsib else hole)
      (if f.P.went_right then hole else P.top f.P.fsib) p **
    O.owns f.P.fsib p ** context rest f.P.fbox p

ghost fn rec join (#a: Type0) (fs: list (frame a)) (t: O.tree a) (p: perm)
  requires context fs (P.top t) p ** O.owns t p
  ensures O.owns (P.plug fs t) p
  decreases fs
{
  match fs {
    [] -> { unfold (context fs (P.top t) p); }
    f :: rest -> {
      unfold (context fs (P.top t) p);
      if (f.P.went_right) {
        fold (O.owns (T.Branch f.P.fsib (f.P.fbox, f.P.fval) t) p);
        rewrite (O.owns (T.Branch f.P.fsib (f.P.fbox, f.P.fval) t) p)
          as (O.owns (P.fill f t) p);
      } else {
        fold (O.owns (T.Branch t (f.P.fbox, f.P.fval) f.P.fsib) p);
        rewrite (O.owns (T.Branch t (f.P.fbox, f.P.fval) f.P.fsib) p)
          as (O.owns (P.fill f t) p);
      };
      rewrite (context rest f.P.fbox p) as (context rest (P.top (P.fill f t)) p);
      join rest (P.fill f t) p;
    }
  }
}

ghost fn rec split (#a: Type0) (fs: list (frame a)) (t: O.tree a) (p: perm)
  requires O.owns (P.plug fs t) p
  ensures context fs (P.top t) p ** O.owns t p
  decreases fs
{
  match fs {
    [] -> { fold (context fs (P.top t) p); }
    f :: rest -> {
      split rest (P.fill f t) p;
      rewrite (context rest (P.top (P.fill f t)) p) as (context rest f.P.fbox p);
      if (f.P.went_right) {
        rewrite (O.owns (P.fill f t) p) as (O.owns (T.Branch f.P.fsib (f.P.fbox, f.P.fval) t) p);
        unfold (O.owns (T.Branch f.P.fsib (f.P.fbox, f.P.fval) t) p);
      } else {
        rewrite (O.owns (P.fill f t) p) as (O.owns (T.Branch t (f.P.fbox, f.P.fval) f.P.fsib) p);
        unfold (O.owns (T.Branch t (f.P.fbox, f.P.fval) f.P.fsib) p);
      };
      fold (context fs (P.top t) p);
    }
  }
}

let present (#a: Type0) (t: O.tree a) (x: N.class_Node__opt a) =
  T.Branch? (P.sub t x) /\ P.top (P.sub t x) == x

let lookup_root (#a: Type0) (t: O.tree a)
  : Lemma (requires O.good t)
      (ensures O.lookup t (P.top t) == O.values t /\
        (P.top t =!= B.null ==> O.member t (P.top t)) /\
        O.lookup t B.null == T.Leaf)
  = D.sub_top [] t; D.sub_absent t B.null

let lookup_children (#a: Type0) (t: O.tree a) (x: N.class_Node__opt a)
  : Lemma (requires O.good t /\ O.member t x)
      (ensures (
        let s = P.sub t x in
        present t x /\
        P.sub t (P.top (T.left s)) == T.left s /\
        P.sub t (P.top (T.right s)) == T.right s /\
        (P.top (T.left s) =!= B.null ==> O.member t (P.top (T.left s))) /\
        (P.top (T.right s) =!= B.null ==> O.member t (P.top (T.right s)))))
  = P.focus_plug t x;
    let fs = fst (P.focus t x) in
    let s = P.sub t x in
    match s with
    | T.Branch l e r ->
      let fl = {P.went_right=false; P.fbox=fst e; P.fval=snd e; P.fsib=r} in
      let fr = {P.went_right=true; P.fbox=fst e; P.fval=snd e; P.fsib=l} in
      D.sub_top (fl::fs) l;
      D.sub_top (fr::fs) r;
      P.mem_plug (P.top l) (fl::fs) l;
      P.mem_plug (P.top r) (fr::fs) r

unfold let window (#a: Type0) (t: O.tree a) (x: N.class_Node__opt a) (p: perm) : slprop =
  exists* (key: a) (red: bool) (l r: N.class_Node__opt a).
    O.held x key red l r p **
    O.owns (T.left (P.sub t x)) p ** O.owns (T.right (P.sub t x)) p **
    context (fst (P.focus t x)) x p **
    pure (P.sub t x == T.Branch (T.left (P.sub t x)) (x, (key, red)) (T.right (P.sub t x)) /\
      l == P.top (T.left (P.sub t x)) /\ r == P.top (T.right (P.sub t x)) /\
      O.lookup t x == T.Branch (O.lookup t l) (key, red) (O.lookup t r) /\
      T.size (O.lookup t l) < T.size (O.lookup t x) /\
      T.size (O.lookup t r) < T.size (O.lookup t x) /\
      (l =!= B.null ==> O.member t l) /\
      (r =!= B.null ==> O.member t r))

ghost fn open_node (#a: Type0) (t: O.tree a) (x: N.class_Node__opt a) (p: perm)
  requires O.owns t p ** pure (O.good t /\ O.member t x)
  ensures window t x p
{
  lookup_children t x;
  P.focus_plug t x;
  rewrite (O.owns t p) as (O.owns (P.plug (fst (P.focus t x)) (P.sub t x)) p);
  split (fst (P.focus t x)) (P.sub t x) p;
  rewrite (context (fst (P.focus t x)) (P.top (P.sub t x)) p)
    as (context (fst (P.focus t x)) x p);
  rewrite (O.owns (P.sub t x) p)
    as (O.owns (T.Branch (T.left (P.sub t x)) (T.Branch?._1 (P.sub t x)) (T.right (P.sub t x))) p);
  unfold (O.owns (T.Branch (T.left (P.sub t x)) (T.Branch?._1 (P.sub t x)) (T.right (P.sub t x))) p);
  rewrite each (fst (T.Branch?._1 (P.sub t x))) as x;
}

ghost fn close_node (#a: Type0) (t: O.tree a) (x: N.class_Node__opt a) (p: perm)
  requires window t x p
  ensures O.owns t p
{
  unfold (window t x p);
  with key red l r. _;
  rewrite (O.held x key red l r p) as
    (O.held x key red (P.top (T.left (P.sub t x))) (P.top (T.right (P.sub t x))) p);
  fold (O.owns (T.Branch (T.left (P.sub t x)) (x, (key, red)) (T.right (P.sub t x))) p);
  rewrite (O.owns (T.Branch (T.left (P.sub t x)) (x, (key, red)) (T.right (P.sub t x))) p)
    as (O.owns (P.sub t x) p);
  rewrite (context (fst (P.focus t x)) x p)
    as (context (fst (P.focus t x)) (P.top (P.sub t x)) p);
  join (fst (P.focus t x)) (P.sub t x) p;
  P.focus_plug t x;
  rewrite (O.owns (P.plug (fst (P.focus t x)) (P.sub t x)) p) as (O.owns t p);
}

unfold let owner_window (#a: Type0) (root: N.class_Node__opt a)
    (s: O.state a) (x: N.class_Node__opt a) (p: perm) : slprop =
  window (O.active s) x p ** O.retained (O.retired_state s) p **
  pure (root == P.top (O.active s))

ghost fn open_owner (#a: Type0) (root: N.class_Node__opt a)
    (s: O.state a) (x: N.class_Node__opt a) (p: perm)
  requires O.owner root s p ** pure (O.good (O.active s) /\ O.member (O.active s) x)
  ensures owner_window root s x p
{
  unfold (O.owner root s p);
  open_node (O.active s) x p;
}

ghost fn close_owner (#a: Type0) (root: N.class_Node__opt a)
    (s: O.state a) (x: N.class_Node__opt a) (p: perm)
  requires owner_window root s x p
  ensures O.owner root s p
{
  unfold (owner_window root s x p);
  close_node (O.active s) x p;
  fold (O.owner root s p);
}

unfold let any_owner_window (#a: Type0) (root: N.class_Node__opt a)
    (s: O.state a) (p: perm) : slprop =
  exists* (x: N.class_Node__opt a). owner_window root s x p

[@@pulse_intro]
ghost fn close_any_owner (#a: Type0) (root: N.class_Node__opt a)
    (s: O.state a) (p: perm)
  requires any_owner_window root s p
  ensures O.owner root s p
{
  unfold (any_owner_window root s p);
  with x. _;
  close_owner root s x p;
}
