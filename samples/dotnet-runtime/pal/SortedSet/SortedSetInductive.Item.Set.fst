module SortedSetInductive.Item.Set
#lang-pulse

open Pulse.Lib.Pervasives
module O = SortedSetInductive.Ownership
module U = SortedSetInductive.Item.Spec
module P = SortedSetInductive.Item.Point
module I = SortedSetInductive.Item
module H = SortedSetInductive.RetainedHolder
module Q = SortedSetInductive.State
module S = Class_SortedSet
module M = Struct_SortedSetModel
module N = Class_Node
module ST = Pulse.Lib.CSharp.SearchTree
module Seq = FStar.Seq

#set-options "--z3rlimit 10"

noeq type ticket (a: Type0) = {
  holder: I.holder_snapshot a;
  node: N.class_Node__raw a;
  model: S.class_SortedSet__model a;
}

noeq type result (a: Type0) = {
  payload: H.payload a;
  after: S.class_SortedSet__model a;
}

let holder_of (#a: Type0) (q: ticket a) = q.holder
let node_of (#a: Type0) (q: ticket a) = q.node
let model_of (#a: Type0) (q: ticket a) = q.model
let payload_of (#a: Type0) (r: result a) = r.payload
let model_after (#a: Type0) (r: result a) = r.after

unfold let rest (#a: Type0) (set: S.class_SortedSet a) (x: N.class_Node__opt a)
    (q: ticket a) =
  I.raw set q.holder **
  O.retained (O.retired_state q.holder.S.fld_ownershipState) 1.0R **
  P.restore q.model.M.fld_Labels x q.node 1.0R **
  pure (I.matches q.holder (H.payload_of q.holder.S.fld_ownershipState) q.model /\
    O.member q.model.M.fld_Labels x /\
    O.item q.node == ST.root_key (O.lookup q.model.M.fld_Labels x) (O.item q.node))

ghost fn open_set (#a: Type0) (set: S.class_SortedSet a)
    (m: S.class_SortedSet__model a) (x: N.class_Node__opt a)
  requires SortedSetInductive.Read.inv set m 1.0R ** pure (O.member m.M.fld_Labels x)
  returns q: erased (ticket a)
  ensures O.raw x (node_of q) 1.0R ** rest set x q **
    pure (model_of q == m /\
      U.position m.M.fld_Labels x < Seq.length (ST.keys m.M.fld_Tree) /\
      Seq.index (ST.keys m.M.fld_Tree) (U.position m.M.fld_Labels x) == O.item (node_of q))
{
  unfold (SortedSetInductive.Read.inv set m 1.0R);
  unfold (S.class_SortedSet__inv set m);
  with r. _;
  unfold (O.owner r.S.fld_root r.S.fld_ownershipState 1.0R);
  rewrite (O.owns (O.active r.S.fld_ownershipState) 1.0R) as (O.owns m.M.fld_Labels 1.0R);
  let v = P.open_tree m.M.fld_Labels x 1.0R;
  U.updated_keys m.M.fld_Labels x (O.item v);
  fold (rest set x { holder=r; node=reveal v; model=m });
  hide ({ holder=r; node=reveal v; model=m })
}

ghost fn finish (#a: Type0) (set: S.class_SortedSet a) (x: N.class_Node__opt a)
    (q: ticket a) (item: a)
  requires rest set x q ** O.raw x (P.with_item q.node item) 1.0R **
    pure (U.equivalent q.model.M.fld_Comparer (O.item q.node) item)
  returns r: erased (result a)
  ensures I.pending set q.holder (payload_of r) (model_after r) **
    pure (
      O.active (H.state_of (payload_of r)) == U.updated q.model.M.fld_Labels x item /\
      O.retired_state (H.state_of (payload_of r)) == O.retired_state q.holder.S.fld_ownershipState /\
      (model_after r).M.fld_Root == q.model.M.fld_Root /\
      (model_after r).M.fld_Count == q.model.M.fld_Count /\
      (model_after r).M.fld_Version == q.model.M.fld_Version /\
      (model_after r).M.fld_Comparer == q.model.M.fld_Comparer /\
      U.position q.model.M.fld_Labels x < Seq.length (ST.keys q.model.M.fld_Tree) /\
      Seq.equal (ST.keys (model_after r).M.fld_Tree)
        (Seq.upd (ST.keys q.model.M.fld_Tree) (U.position q.model.M.fld_Labels x) item))
{
  unfold (rest set x q);
  P.restore_at q.model.M.fld_Labels x q.node item 1.0R;
  U.updated_labels q.model.M.fld_Labels x item;
  U.updated_balanced q.model.M.fld_Labels x item;
  U.updated_keys q.model.M.fld_Labels x item;
  U.updated_sorted q.model.M.fld_Labels x q.model.M.fld_Comparer (O.item q.node) item;
  let payload = (U.updated q.model.M.fld_Labels x item,
    O.retired_state q.holder.S.fld_ownershipState);
  let m = { q.model with
    M.fld_Tree=O.values (fst payload);
    M.fld_Labels=fst payload;
    M.fld_Observation=Q.observe (H.state_of payload) };
  rewrite (O.owns (U.updated q.model.M.fld_Labels x item) 1.0R)
    as (O.owns (O.active (H.state_of payload)) 1.0R);
  rewrite (O.retained (O.retired_state q.holder.S.fld_ownershipState) 1.0R)
    as (O.retained (O.retired_state (H.state_of payload)) 1.0R);
  fold (O.owner q.holder.S.fld_root (H.state_of payload) 1.0R);
  fold (I.pending set q.holder payload m);
  hide ({ payload=payload; after=m })
}
