module SortedSetInductive.Ownership
#lang-pulse

open Pulse.Lib.Pervasives
module B = Pulse.Lib.Box
module N = Class_Node
module T = Pulse.Lib.CSharp.Tree
module S = Pulse.Lib.CSharp.SearchTree
module P = Pulse.Lib.CSharp.RegionPath
module D = Pulse.Lib.CSharp.TopDown
module RT = Pulse.Lib.CSharp.RegionTree
module F = Pulse.Lib.CSharp.Ownership
module G = Pulse.Lib.GhostReference

#set-options "--z3rlimit 10"

// Pointer-labelled mathematical trees. RegionPath and TopDown are used only
// for their pure tree operations; no region predicate or heap map is involved.
let tree (a: Type0) = D.nt (N.class_Node__raw a) a
let top (#a: Type0) (t: tree a) = P.top t
let values (#a: Type0) (t: tree a) = D.strip t
let good (#a: Type0) (t: tree a) = RT.distinct (P.nboxes t) /\ D.all_nonnull t
let member (#a: Type0) (t: tree a) (x: N.class_Node__opt a) = FStar.List.Tot.memP x (P.nboxes t)
let lookup (#a: Type0) (t: tree a) (x: N.class_Node__opt a) = D.strip (P.sub t x)

let item (#a: Type0) (r: N.class_Node__raw a) = r.N.fld_Item
let red (#a: Type0) (r: N.class_Node__raw a) = S.Red? r.N.fld_Color
let entry (#a: Type0) (r: N.class_Node__raw a) = (item r, red r)
let node_color (#a: Type0) (r: N.class_Node__raw a) = r.N.fld_Color
unfold let left (#a: Type0) (r: N.class_Node__raw a) = r.N.fld_Left
unfold let right (#a: Type0) (r: N.class_Node__raw a) = r.N.fld_Right
let with_left (#a: Type0) (r: N.class_Node__raw a) (x: N.class_Node__opt a) =
  { r with N.fld_Left = x }
let with_right (#a: Type0) (r: N.class_Node__raw a) (x: N.class_Node__opt a) =
  { r with N.fld_Right = x }
let with_children (#a: Type0) (r: N.class_Node__raw a) (l rr: N.class_Node__opt a) =
  { r with N.fld_Left = l; N.fld_Right = rr }
let color (r: bool) = if r then S.Red else S.Black

let recolor (#a: Type0) (r: N.class_Node__raw a) (red: bool) =
  { r with N.fld_Color = color red }

unfold let fresh (#a: Type0) (x: N.class_Node a) (key: a) (c: S.node_color) : slprop =
  B.pts_to x { N.fld_Item = key; N.fld_Color = c; N.fld_Left = B.null; N.fld_Right = B.null }

unfold let raw (#a: Type0) (x: N.class_Node__opt a) (r: N.class_Node__raw a)
    (p: perm) : slprop = B.pts_to x #p r

let nullable_snapshot (a: Type0) = option (N.class_Node__raw a)
let nullable_red (#a: Type0) (s: nullable_snapshot a) =
  match s with | None -> false | Some r -> red r
let nullable_raw (#a: Type0) (x: N.class_Node__opt a) (s: nullable_snapshot a)
    (p: perm) : slprop =
  if B.is_null x then pure (s == None)
  else exists* (r: N.class_Node__raw a). pure (s == Some r) ** raw x r p

unfold let nullable_opened (#a: Type0) (x: N.class_Node__opt a) (s: nullable_snapshot a)
    (p: perm) : slprop =
  exists* (r: N.class_Node__raw a). pure (s == Some r) ** raw x r p

ghost fn open_nullable (#a: Type0) (x: N.class_Node a) (s: nullable_snapshot a) (p: perm)
  requires nullable_raw x s p
  ensures nullable_opened x s p
{
  rewrite (nullable_raw x s p) as (nullable_opened x s p);
}

ghost fn close_nullable (#a: Type0) (x: N.class_Node a) (s: nullable_snapshot a) (p: perm)
  requires nullable_opened x s p
  ensures nullable_raw x s p
{
  rewrite (nullable_opened x s p) as (nullable_raw x s p);
}

ghost fn nullable_null (#a: Type0) (x: N.class_Node__opt a) (s: nullable_snapshot a) (p: perm)
  requires nullable_raw x s p ** pure (B.is_null x)
  ensures nullable_raw x s p ** pure (not (nullable_red s))
{
  rewrite (nullable_raw x s p) as (pure (s == None));
  rewrite (pure (s == None)) as (nullable_raw x s p);
}

unfold let held (#a: Type0) (x: N.class_Node__opt a) (key: a) (is_red: bool)
    (left right: N.class_Node__opt a) (p: perm) : slprop =
  B.pts_to x #p {
    N.fld_Item = key; N.fld_Color = color is_red;
    N.fld_Left = left; N.fld_Right = right
  }

// The active tree owns each cell once by recursive separating conjunction.
let rec owns (#a: Type0) (t: tree a) (p: perm)
  : Tot slprop (decreases t) =
  match t with
  | T.Leaf -> emp
  | T.Branch l e r ->
    held (fst e) (fst (snd e)) (snd (snd e)) (top l) (top r) p **
    owns l p ** owns r p

ghost fn rec share_tree (#a: Type0) (t: tree a) (p: perm) ()
  requires owns t p
  ensures owns t (p /. 2.0R) ** owns t (p /. 2.0R)
  decreases t
{
  match t {
    T.Leaf -> { unfold (owns t p); fold (owns t (p /. 2.0R)); fold (owns t (p /. 2.0R)); }
    T.Branch l e r -> {
      unfold (owns t p);
      B.share (fst e);
      share_tree l p ();
      share_tree r p ();
      fold (owns t (p /. 2.0R));
      fold (owns t (p /. 2.0R));
    }
  }
}

ghost fn rec gather_tree (#a: Type0) (t: tree a) (p q: perm) ()
  requires owns t p ** owns t q
  ensures owns t (p +. q)
  decreases t
{
  match t {
    T.Leaf -> {
      unfold (owns t p); unfold (owns t q);
      fold (owns t (p +. q));
    }
    T.Branch l e r -> {
      unfold (owns t p); unfold (owns t q);
      B.gather (fst e);
      gather_tree l p q ();
      gather_tree r p q ();
      fold (owns t (p +. q));
    }
  }
}

// A package of an actual boxed cell, not an arbitrary spatial predicate.
// The higher-universe proof capability is computed from this Type1 witness;
// only the witness is stored in a standard ghost reference.
noeq type frame_payload =
  | Boxed: #a:Type0 -> B.box a -> a -> frame_payload

let frame_pred (v: frame_payload) (p: perm) : slprop =
  match v with
  | Boxed box value -> B.pts_to box #p value

ghost fn share_payload (v: frame_payload) (p: perm) ()
  requires frame_pred v p
  ensures frame_pred v (p /. 2.0R) ** frame_pred v (p /. 2.0R)
{
  match v {
    Boxed box value -> {
      unfold (frame_pred v p);
      B.share box;
      fold (frame_pred v (p /. 2.0R));
      fold (frame_pred v (p /. 2.0R));
    }
  }
}

ghost fn gather_payload (v: frame_payload) (p q: perm) ()
  requires frame_pred v p ** frame_pred v q
  ensures frame_pred v (p +. q)
{
  match v {
    Boxed box value -> {
      unfold (frame_pred v p); unfold (frame_pred v q);
      B.gather box;
      fold (frame_pred v (p +. q));
    }
  }
}

let frame_capability (v: frame_payload) : F.fractional (frame_pred v) =
  F.Mkfractional #(frame_pred v) (share_payload v) (gather_payload v)

let frame_ref = G.ref frame_payload

let frame_owns (h: frame_ref) (p: perm) : slprop =
  exists* (v: frame_payload). G.pts_to h #p v ** frame_pred v p

ghost fn share_frame (h: frame_ref) (p: perm)
  requires frame_owns h p
  ensures frame_owns h (p /. 2.0R) ** frame_owns h (p /. 2.0R)
{
  unfold (frame_owns h p);
  with v. _;
  G.share h;
  let capability = frame_capability v;
  capability.F.share_half_op p ();
  fold (frame_owns h (p /. 2.0R));
  fold (frame_owns h (p /. 2.0R));
}

ghost fn gather_frame (h: frame_ref) (p q: perm)
  requires frame_owns h p ** frame_owns h q
  ensures frame_owns h (p +. q)
{
  unfold (frame_owns h p);
  with v. assert (G.pts_to h #p v ** frame_pred v p);
  unfold (frame_owns h q);
  with w. assert (G.pts_to h #q w ** frame_pred w q);
  G.gather h;
  rewrite (frame_pred w q) as (frame_pred v q);
  let capability = frame_capability v;
  capability.F.gather_op p q ();
  fold (frame_owns h (p +. q));
}

// A retired node owns its original record, including non-owning links which
// may still refer to live nodes. Retirement never clears a runtime link.
// Clear can retain a complete detached tree in one constructor.
noeq type retired (a: Type0) =
  | End
  | Cell: N.class_Node__opt a -> N.class_Node__raw a -> retired a -> retired a
  | Forest: tree a -> retired a -> retired a
  // Non-node holder cells are retained with their checked fractional operations.
  // Node cells always use Cell/Forest, so they remain observable to stale cursors.
  | Frame: frame_ref -> retired a -> retired a

let rec retained (#a: Type0) (r: retired a) (p: perm)
  : Tot slprop (decreases r) =
  match r with
  | End -> emp
  | Cell x v rest -> raw x v p ** retained rest p
  | Forest t rest -> owns t p ** retained rest p
  | Frame h rest -> frame_owns h p ** retained rest p

ghost fn rec share_retired (#a: Type0) (r: retired a) (p: perm) ()
  requires retained r p
  ensures retained r (p /. 2.0R) ** retained r (p /. 2.0R)
  decreases r
{
  match r {
    End -> {
      unfold (retained r p);
      fold (retained r (p /. 2.0R)); fold (retained r (p /. 2.0R));
    }
    Cell x v rest -> {
      unfold (retained r p);
      B.share x;
      share_retired rest p ();
      fold (retained r (p /. 2.0R)); fold (retained r (p /. 2.0R));
    }
    Forest t rest -> {
      unfold (retained r p);
      share_tree t p ();
      share_retired rest p ();
      fold (retained r (p /. 2.0R)); fold (retained r (p /. 2.0R));
    }
    Frame h rest -> {
      unfold (retained r p);
      share_frame h p;
      share_retired rest p ();
      fold (retained r (p /. 2.0R)); fold (retained r (p /. 2.0R));
    }
  }
}

ghost fn rec gather_retired (#a: Type0) (r: retired a) (p q: perm) ()
  requires retained r p ** retained r q
  ensures retained r (p +. q)
  decreases r
{
  match r {
    End -> {
      unfold (retained r p); unfold (retained r q);
      fold (retained r (p +. q));
    }
    Cell x v rest -> {
      unfold (retained r p); unfold (retained r q);
      B.gather x;
      gather_retired rest p q ();
      fold (retained r (p +. q));
    }
    Forest t rest -> {
      unfold (retained r p); unfold (retained r q);
      gather_tree t p q ();
      gather_retired rest p q ();
      fold (retained r (p +. q));
    }
    Frame h rest -> {
      unfold (retained r p); unfold (retained r q);
      gather_frame h p q;
      gather_retired rest p q ();
      fold (retained r (p +. q));
    }
  }
}

let rec append_retired (#a: Type0) (r s: retired a) : Tot (retired a) (decreases r) =
  match r with
  | End -> s
  | Cell x v rest -> Cell x v (append_retired rest s)
  | Forest t rest -> Forest t (append_retired rest s)
  | Frame h rest -> Frame h (append_retired rest s)

let rec append_retired_assoc (#a: Type0) (r s t: retired a)
  : Lemma
      (append_retired (append_retired r s) t == append_retired r (append_retired s t))
      (decreases r) =
  match r with
  | End -> ()
  | Cell _ _ rest -> append_retired_assoc rest s t
  | Forest _ rest -> append_retired_assoc rest s t
  | Frame _ rest -> append_retired_assoc rest s t

ghost fn rec join_retired (#a: Type0) (r s: retired a) (p: perm)
  requires retained r p ** retained s p
  ensures retained (append_retired r s) p
  decreases r
{
  match r {
    End -> { unfold (retained r p); }
    Cell x v rest -> {
      unfold (retained r p);
      join_retired rest s p;
      fold (retained (Cell x v (append_retired rest s)) p);
      rewrite (retained (Cell x v (append_retired rest s)) p) as (retained (append_retired r s) p);
    }
    Forest t rest -> {
      unfold (retained r p);
      join_retired rest s p;
      fold (retained (Forest t (append_retired rest s)) p);
      rewrite (retained (Forest t (append_retired rest s)) p) as (retained (append_retired r s) p);
    }
    Frame h rest -> {
      unfold (retained r p);
      join_retired rest s p;
      fold (retained (Frame h (append_retired rest s)) p);
      rewrite (retained (Frame h (append_retired rest s)) p) as (retained (append_retired r s) p);
    }
  }
}

let state (a: Type0) = erased (tree a & retired a)
let active (#a: Type0) (s: state a) : GTot (tree a) = fst (reveal s)
let retired_state (#a: Type0) (s: state a) : GTot (retired a) = snd (reveal s)
let empty (a: Type0) : Tot (state a) = hide (T.Leaf, End)
let replace (#a: Type0) (s: state a) (t: erased (tree a)) : Tot (state a) =
  hide (reveal t, retired_state s)
let cleared (#a: Type0) (s: state a) : Tot (state a) =
  hide (T.Leaf, Forest (active s) (retired_state s))
let retired_cell (#a: Type0) (s: state a) (x: N.class_Node__opt a)
    (v: erased (N.class_Node__raw a)) : Tot (state a) =
  hide (active s, Cell x (reveal v) (retired_state s))

let owner (#a: Type0) (root: N.class_Node__opt a) (s: state a) (p: perm) : slprop =
  owns (active s) p ** retained (retired_state s) p ** pure (root == top (active s))

ghost fn empty_owner (#a: Type0) ()
  requires emp
  ensures owner (B.null #(N.class_Node__raw a)) (empty a) 1.0R
{
  fold (owns (T.Leaf <: tree a) 1.0R);
  fold (retained (End <: retired a) 1.0R);
  fold (owner (B.null #(N.class_Node__raw a)) (empty a) 1.0R);
}

// A view's base constructor starts empty. No cell ownership is discarded:
// both recursive predicates reduce to emp.
ghost fn consume_empty (#a: Type0) ()
  requires owner (B.null #(N.class_Node__raw a)) (empty a) 1.0R
  ensures emp
{
  unfold (owner (B.null #(N.class_Node__raw a)) (empty a) 1.0R);
  unfold (owns (T.Leaf <: tree a) 1.0R);
  unfold (retained (End <: retired a) 1.0R);
}

ghost fn retain_clear (#a: Type0) (root: N.class_Node__opt a) (s: state a)
  requires owner root s 1.0R
  ensures owner (B.null #(N.class_Node__raw a)) (cleared s) 1.0R
{
  unfold (owner root s 1.0R);
  fold (retained (Forest (active s) (retired_state s)) 1.0R);
  fold (owns (T.Leaf <: tree a) 1.0R);
  fold (owner (B.null #(N.class_Node__raw a)) (cleared s) 1.0R);
}

ghost fn retain_cell (#a: Type0) (root x: N.class_Node__opt a)
    (s: state a) (v: erased (N.class_Node__raw a))
  requires owner root s 1.0R ** raw x (reveal v) 1.0R
  ensures owner root (retired_cell s x v) 1.0R
{
  unfold (owner root s 1.0R);
  fold (retained (Cell x (reveal v) (retired_state s)) 1.0R);
  fold (owner root (retired_cell s x v) 1.0R);
}

ghost fn share_owner (#a: Type0) (root: N.class_Node__opt a) (s: state a) (p: perm) ()
  requires owner root s p
  ensures owner root s (p /. 2.0R) ** owner root s (p /. 2.0R)
{
  unfold (owner root s p);
  share_tree (active s) p ();
  share_retired (retired_state s) p ();
  fold (owner root s (p /. 2.0R)); fold (owner root s (p /. 2.0R));
}

ghost fn gather_owner (#a: Type0) (root: N.class_Node__opt a) (s: state a) (p q: perm) ()
  requires owner root s p ** owner root s q
  ensures owner root s (p +. q)
{
  unfold (owner root s p); unfold (owner root s q);
  gather_tree (active s) p q ();
  gather_retired (retired_state s) p q ();
  fold (owner root s (p +. q));
}

instance fractional_owner (#a: Type0) (root: N.class_Node__opt a) (s: state a)
  : F.fractional (fun p -> owner root s p) =
  F.Mkfractional #(fun p -> owner root s p)
    (fun p () -> share_owner root s p ())
    (fun p q () -> gather_owner root s p q ())
