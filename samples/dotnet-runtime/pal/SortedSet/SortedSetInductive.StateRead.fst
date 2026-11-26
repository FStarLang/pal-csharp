module SortedSetInductive.StateRead
#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Trade.Util
module O = SortedSetInductive.Ownership
module Q = SortedSetInductive.State
module N = Class_Node
module T = Pulse.Lib.CSharp.Tree
module B = Pulse.Lib.Box
module E = Pulse.Lib.CSharp.RefEq

#set-options "--z3rlimit 10"

// Arbitrary positive fractional permission; no distinctness/freshness or
// reachability-from-active-root precondition is needed for a read.
ghost fn rec open_tree (#a: Type0) (t: O.tree a) (x: N.class_Node__opt a) (p: perm)
  requires O.owns t p ** pure (Some? (Q.find_tree t x))
  ensures exists* (v: N.class_Node__raw a).
    pure (Q.find_tree t x == Some v) ** O.raw x v p **
    (O.raw x v p @==> O.owns t p)
  decreases t
{
  match t {
    T.Leaf -> { unreachable (); }
    T.Branch l e r -> {
      unfold (O.owns t p);
      if (E.ref_eq (fst e) x) {
        rewrite (O.held (fst e) (fst (snd e)) (snd (snd e)) (O.top l) (O.top r) p)
          as (O.raw x (Q.record l e r) p);
        intro (O.raw x (Q.record l e r) p @==> O.owns t p)
          #(O.owns l p ** O.owns r p) fn _ {
            rewrite (O.raw x (Q.record l e r) p)
              as (O.held (fst e) (fst (snd e)) (snd (snd e)) (O.top l) (O.top r) p);
            fold (O.owns t p);
          };
      } else {
        if (Some? (Q.find_tree l x)) {
          open_tree l x p;
          with v. _;
          intro (O.raw x v p @==> O.owns t p)
            #((O.raw x v p @==> O.owns l p) **
              O.held (fst e) (fst (snd e)) (snd (snd e)) (O.top l) (O.top r) p **
              O.owns r p) fn _ {
                elim (O.raw x v p) (O.owns l p);
                fold (O.owns t p);
              };
        } else {
          open_tree r x p;
          with v. _;
          intro (O.raw x v p @==> O.owns t p)
            #((O.raw x v p @==> O.owns r p) **
              O.held (fst e) (fst (snd e)) (snd (snd e)) (O.top l) (O.top r) p **
              O.owns l p) fn _ {
                elim (O.raw x v p) (O.owns r p);
                fold (O.owns t p);
              };
        }
      }
    }
  }
}

ghost fn rec open_retired (#a: Type0) (r: O.retired a) (x: N.class_Node__opt a) (p: perm)
  requires O.retained r p ** pure (Some? (Q.find_retired r x))
  ensures exists* (v: N.class_Node__raw a).
    pure (Q.find_retired r x == Some v) ** O.raw x v p **
    (O.raw x v p @==> O.retained r p)
  decreases r
{
  match r {
    O.End -> { unreachable (); }
    O.Cell y value rest -> {
      unfold (O.retained r p);
      if (E.ref_eq y x) {
        rewrite (O.raw y value p) as (O.raw x value p);
        intro (O.raw x value p @==> O.retained r p)
          #(O.retained rest p) fn _ {
            rewrite (O.raw x value p) as (O.raw y value p);
            fold (O.retained r p);
          };
      } else {
        open_retired rest x p;
        with v. _;
        intro (O.raw x v p @==> O.retained r p)
          #((O.raw x v p @==> O.retained rest p) ** O.raw y value p) fn _ {
            elim (O.raw x v p) (O.retained rest p);
            fold (O.retained r p);
          };
      }
    }
    O.Forest t rest -> {
      unfold (O.retained r p);
      if (Some? (Q.find_tree t x)) {
        open_tree t x p;
        with v. _;
        intro (O.raw x v p @==> O.retained r p)
          #((O.raw x v p @==> O.owns t p) ** O.retained rest p) fn _ {
            elim (O.raw x v p) (O.owns t p);
            fold (O.retained r p);
          };
      } else {
        open_retired rest x p;
        with v. _;
        intro (O.raw x v p @==> O.retained r p)
          #((O.raw x v p @==> O.retained rest p) ** O.owns t p) fn _ {
            elim (O.raw x v p) (O.retained rest p);
            fold (O.retained r p);
          };
      }
    }
    O.Frame h rest -> {
      unfold (O.retained r p);
      open_retired rest x p;
      with v. _;
      intro (O.raw x v p @==> O.retained r p)
        #((O.raw x v p @==> O.retained rest p) ** O.frame_owns h p) fn _ {
          elim (O.raw x v p) (O.retained rest p);
          fold (O.retained r p);
        };
    }
  }
}

unfold let window (#a: Type0) (root: N.class_Node__opt a) (s: O.state a)
    (x: N.class_Node__opt a) (p: perm) =
  exists* (v: N.class_Node__raw a).
    pure (Q.find (Q.observe s) x == Some v) ** O.raw x v p **
    (O.raw x v p @==> O.owner root s p)

ghost fn open_owner (#a: Type0) (root: N.class_Node__opt a) (s: O.state a)
    (x: N.class_Node__opt a) (p: perm)
  requires O.owner root s p ** pure (Q.mem (Q.observe s) x)
  ensures window root s x p
{
  unfold (O.owner root s p);
  let active = O.active s;
  if (Some? (Q.find_tree active x)) {
    open_tree (O.active s) x p;
    with v. _;
    intro (O.raw x v p @==> O.owner root s p)
      #((O.raw x v p @==> O.owns (O.active s) p) ** O.retained (O.retired_state s) p) fn _ {
        elim (O.raw x v p) (O.owns (O.active s) p);
        fold (O.owner root s p);
      };
  } else {
    open_retired (O.retired_state s) x p;
    with v. _;
    intro (O.raw x v p @==> O.owner root s p)
      #((O.raw x v p @==> O.retained (O.retired_state s) p) ** O.owns (O.active s) p) fn _ {
        elim (O.raw x v p) (O.retained (O.retired_state s) p);
        fold (O.owner root s p);
      };
  }
}

ghost fn close_owner (#a: Type0) (root: N.class_Node__opt a) (s: O.state a)
    (x: N.class_Node__opt a) (p: perm)
  requires window root s x p
  ensures O.owner root s p
{
  unfold (window root s x p);
  with v. _;
  elim (O.raw x v p) (O.owner root s p);
}

unfold let read_window (#a: Type0) (root: N.class_Node__opt a) (s: O.state a)
    (x: N.class_Node__opt a) (p: perm) =
  exists* (v: N.class_Node__raw a).
    pure (Q.find (Q.observe s) x == Some v /\ not (B.is_null x) /\
      Q.tree_at (Q.observe s) x ==
        T.Branch (Q.tree_n (fst (Q.observe s)) (Q.observe s) (O.left v)) (O.entry v)
                 (Q.tree_n (fst (Q.observe s)) (Q.observe s) (O.right v))) **
    O.raw x v p ** (O.raw x v p @==> O.owner root s p)

ghost fn open_read (#a: Type0) (root: N.class_Node__opt a) (s: O.state a)
    (x: N.class_Node__opt a) (p: perm)
  requires O.owner root s p ** pure (Q.mem (Q.observe s) x)
  ensures read_window root s x p
{
  open_owner root s x p;
  unfold (window root s x p);
  with v. _;
  B.pts_to_not_null x;
  let h = Q.observe s;
  Q.root_step h x;
  fold (read_window root s x p);
}

ghost fn close_read (#a: Type0) (root: N.class_Node__opt a) (s: O.state a)
    (x: N.class_Node__opt a) (p: perm)
  requires read_window root s x p
  ensures O.owner root s p
{
  unfold (read_window root s x p);
  with v. _;
  elim (O.raw x v p) (O.owner root s p);
}

[@@pulse_intro]
ghost fn close_return (#a: Type0) (root: N.class_Node__opt a) (s: O.state a) (p: perm)
  requires exists* (x: N.class_Node__opt a) (v: N.class_Node__raw a).
    O.raw x v p ** (O.raw x v p @==> O.owner root s p)
  ensures O.owner root s p
{
  with x v. assert (O.raw x v p ** (O.raw x v p @==> O.owner root s p));
  elim (O.raw x v p) (O.owner root s p);
}

// Expression-position child reads (including short-circuit range tests) use
// the SAME checked recursive read. The owner determines state and permission;
// membership must be proved. The restoration trade is never discarded.
[@@pulse_intro]
ghost fn auto_read (#a: Type0) (x: N.class_Node__opt a) (root: N.class_Node__opt a)
    (s: O.state a{Q.mem (Q.observe s) x}) (p: perm)
  requires O.owner root s p
  ensures B.pts_to x #p (Q.get (Q.observe s) x) **
    (O.raw x (Q.get (Q.observe s) x) p @==> O.owner root s p)
{
  open_owner root s x p;
  unfold (window root s x p);
  with v. _;
  rewrite (O.raw x v p) as (O.raw x (Q.get (Q.observe s) x) p);
  rewrite (O.raw x v p @==> O.owner root s p)
    as (O.raw x (Q.get (Q.observe s) x) p @==> O.owner root s p);
}

fn read (#a: Type0) (root: N.class_Node__opt a) (s: O.state a)
    (x: N.class_Node__opt a) (p: perm)
  preserves O.owner root s p
  requires pure (Q.mem (Q.observe s) x)
  returns v: N.class_Node__raw a
  ensures pure (Q.find (Q.observe s) x == Some v /\ not (B.is_null x))
{
  open_owner root s x p;
  unfold (window root s x p);
  with expected. _;
  B.pts_to_not_null x;
  let v = B.(!x);
  elim (O.raw x expected p) (O.owner root s p);
  v
}
