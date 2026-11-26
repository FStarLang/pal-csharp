module SortedSetInductive.Item.Point
#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Forall.Util
open Pulse.Lib.Trade.Util
module O = SortedSetInductive.Ownership
module U = SortedSetInductive.Item.Spec
module N = Class_Node
module T = Pulse.Lib.CSharp.Tree
module ST = Pulse.Lib.CSharp.SearchTree
module P = Pulse.Lib.CSharp.RegionPath
module D = Pulse.Lib.CSharp.TopDown
module E = Pulse.Lib.CSharp.RefEq

#set-options "--z3rlimit 10"

unfold let with_item (#a: Type0) (v: N.class_Node__raw a) (item: a) =
  { v with N.fld_Item = item }

let restore (#a: Type0) (t: O.tree a) (x: N.class_Node__opt a)
    (v: N.class_Node__raw a) (p: perm) =
  forall* (item: a).
    O.raw x (with_item v item) p @==> O.owns (U.updated t x item) p

ghost fn restore_at (#a: Type0) (t: O.tree a) (x: N.class_Node__opt a)
    (v: N.class_Node__raw a) (item: a) (p: perm)
  requires restore t x v p ** O.raw x (with_item v item) p
  ensures O.owns (U.updated t x item) p
{
  unfold (restore t x v p);
  Pulse.Lib.Forall.Util.elim
    #_ #(fun item -> O.raw x (with_item v item) p @==> O.owns (U.updated t x item) p) item;
  Pulse.Lib.Trade.Util.elim _ _;
}

ghost fn rec open_tree (#a: Type0) (t: O.tree a) (x: N.class_Node__opt a) (p: perm)
  requires O.owns t p ** pure (O.good t /\ O.member t x)
  returns before: erased (N.class_Node__raw a)
  ensures O.raw x before p ** restore t x before p **
    pure (O.item before == ST.root_key (O.lookup t x) (O.item before))
  decreases t
{
  match t {
    T.Branch l e r -> {
      D.distinct_nbranch l (fst e) (snd e) r;
      U.sub_step l r (fst e) x (snd e);
      P.mem_box_nboxes x l;
      unfold (O.owns t p);
      if (E.ref_eq (fst e) x) {
        let v = { N.fld_Item=fst (snd e); N.fld_Color=O.color (snd (snd e));
          N.fld_Left=O.top l; N.fld_Right=O.top r };
        rewrite (O.held (fst e) (fst (snd e)) (snd (snd e)) (O.top l) (O.top r) p) as (O.raw x v p);
        intro (forall* (item: a).
          O.raw x (with_item v item) p @==> O.owns (U.updated t x item) p)
          #(O.owns l p ** O.owns r p) fn _ item {
            U.updated_outside l x item;
            U.updated_outside r x item;
            rewrite (O.raw x (with_item v item) p)
              as (O.held (fst e) item (snd (snd e)) (O.top l) (O.top r) p);
            fold (O.owns (T.Branch l (fst e, (item, snd (snd e))) r) p);
            rewrite (O.owns (T.Branch l (fst e, (item, snd (snd e))) r) p)
              as (O.owns (U.updated t x item) p);
          };
        fold (restore t x v p);
        hide v
      } else if (P.mem_box x l) {
        let v = open_tree l x p;
        intro (forall* (item: a).
          O.raw x (with_item v item) p @==> O.owns (U.updated t x item) p)
          #(restore l x v p **
            O.held (fst e) (fst (snd e)) (snd (snd e)) (O.top l) (O.top r) p ** O.owns r p)
          fn _ item {
            restore_at l x v item p;
            U.updated_labels l x item;
            U.updated_outside r x item;
            rewrite (O.held (fst e) (fst (snd e)) (snd (snd e)) (O.top l) (O.top r) p)
              as (O.held (fst e) (fst (snd e)) (snd (snd e)) (O.top (U.updated l x item)) (O.top r) p);
            fold (O.owns (T.Branch (U.updated l x item) e r) p);
            rewrite (O.owns (T.Branch (U.updated l x item) e r) p)
              as (O.owns (U.updated t x item) p);
          };
        fold (restore t x v p);
        v
      } else {
        let v = open_tree r x p;
        intro (forall* (item: a).
          O.raw x (with_item v item) p @==> O.owns (U.updated t x item) p)
          #(restore r x v p **
            O.held (fst e) (fst (snd e)) (snd (snd e)) (O.top l) (O.top r) p ** O.owns l p)
          fn _ item {
            restore_at r x v item p;
            U.updated_labels r x item;
            U.updated_outside l x item;
            rewrite (O.held (fst e) (fst (snd e)) (snd (snd e)) (O.top l) (O.top r) p)
              as (O.held (fst e) (fst (snd e)) (snd (snd e)) (O.top l) (O.top (U.updated r x item)) p);
            fold (O.owns (T.Branch l e (U.updated r x item)) p);
            rewrite (O.owns (T.Branch l e (U.updated r x item)) p)
              as (O.owns (U.updated t x item) p);
          };
        fold (restore t x v p);
        v
      }
    }
  }
}
