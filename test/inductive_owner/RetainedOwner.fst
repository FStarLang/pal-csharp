module RetainedOwner
#lang-pulse
open Pulse.Lib.Pervasives
module C = Class_CellOwner
module F = Pulse.Lib.CSharp.Ownership
#set-options "--z3rlimit 10"

type payload = C.class_CellOwner & C.class_CellOwner__model
let pair (owner: C.class_CellOwner) (m: C.class_CellOwner__model) : payload = owner, m
let describes (r: payload) owner m = r == pair owner m
let model_value (m: C.class_CellOwner__model) = m
let value (r: payload) = snd r
unfold let held (r: payload) (p: perm) : slprop = C.class_CellOwner__inv (fst r) #p (snd r)
unfold let full (r: payload) : slprop = held r 1.0R
type state = erased (option payload)
let empty : state = hide None
unfold let of_payload (r: payload) : Tot state = hide (Some r)
let state_value (s: state) : GTot int = match reveal s with None -> 0 | Some r -> value r
unfold let state_held (s: state) (p: perm) : slprop = match reveal s with None -> emp | Some r -> held r p

ghost fn share_state (s: option payload) (p: perm) ()
  requires state_held (hide s) p
  ensures state_held (hide s) (p /. 2.0R) ** state_held (hide s) (p /. 2.0R)
{
  unfold (state_held (hide s) p);
  match s {
    None -> { }
    Some r -> { unfold (held r p); C.class_CellOwner__inv_share (fst r); }
  }
}
ghost fn gather_state (s: option payload) (p q: perm) ()
  requires state_held (hide s) p ** state_held (hide s) q
  ensures state_held (hide s) (p +. q)
{
  unfold (state_held (hide s) p); unfold (state_held (hide s) q);
  match s {
    None -> { }
    Some r -> {
      unfold (held r p); unfold (held r q);
      C.class_CellOwner__inv_gather_gen (fst r) p q;
    }
  }
}
instance fractional_state (s: state) : F.fractional (state_held s) =
  F.Mkfractional #(state_held s) (share_state (reveal s)) (gather_state (reveal s))

ghost fn retain (owner: C.class_CellOwner) (m: C.class_CellOwner__model)
  requires C.class_CellOwner__inv owner m
  returns r: erased payload
  ensures full (reveal r) ** pure (value (reveal r) == m)
{
  fold (held (owner, m) 1.0R);
  fold (full (owner, m));
  hide (owner, m)
}

ghost fn retain_void (owner: C.class_CellOwner) (m: C.class_CellOwner__model) (r: payload)
  requires C.class_CellOwner__inv owner m ** pure (describes r owner m)
  ensures full r
{
  assert (pure (r == (owner, m)));
  fold (held (owner, m) 1.0R);
  fold (full (owner, m));
  rewrite (full (owner, m)) as (full r);
}
