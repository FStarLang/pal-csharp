module SortedSetInductive.Balance

module C = SortedSetInductive.Ownership
module N = Class_Node
module P = Pulse.Lib.CSharp.RegionPath
module D = Pulse.Lib.CSharp.TopDown
module M = SortedSetInductive.Mutation
module K = SortedSetInductive.Relink
module T = Pulse.Lib.CSharp.Tree
module B = Pulse.Lib.Box
module EQ = Pulse.Lib.CSharp.RefEq

#set-options "--z3rlimit 10"

let right_of (#a: Type0) (n: C.tree a) (x: N.class_Node__opt a) = P.top (T.right (P.sub n x))
let current_right (#a: Type0) (n: C.tree a) (cur par: N.class_Node__opt a) =
  EQ.ref_eq (right_of n par) cur
let parent_right (#a: Type0) (n: C.tree a) (par gp: N.class_Node__opt a) =
  EQ.ref_eq (right_of n gp) par
let can_rotate (#a: Type0) (w0 w1: bool) (s: C.tree a) =
  T.Branch? s /\
  (if w0 = w1 then (if w0 then T.Branch? (T.right s) else T.Branch? (T.left s))
   else if w0 then T.Branch? (T.left s) /\ T.Branch? (T.right (T.left s))
   else T.Branch? (T.right s) /\ T.Branch? (T.left (T.right s)))

let top_color (#a: Type0) (n: C.tree a) (x: N.class_Node__opt a) (red: bool)
  : Lemma (requires C.good n /\ (x == B.null \/ C.member n x))
      (ensures P.top (M.recolor n x red) == P.top n)
  = if B.is_null x then () else
    P.focus_plug n x;
    match K.path n x with
    | [] -> ()
    | _::_ -> K.replace_top n x (D.recolorn (P.sub n x) red)

let root_color (#a: Type0) (n: C.tree a) (red: bool)
  : Lemma (requires C.good n)
      (ensures M.recolor n (P.top n) red == D.recolorn n red)
  = match n with
    | T.Leaf -> ()
    | T.Branch _ _ _ -> D.focus_at [] n

let layout (#a: Type0) (n: C.tree a) (cur par gp ggp: N.class_Node__opt a)
  : Lemma (requires D.balance_ready n cur par gp ggp)
      (ensures
        C.good n /\ C.member n par /\ C.member n gp /\
        D.parent_of n gp == ggp /\
        C.good (P.sub n gp) /\
        (let w0 = EQ.ref_eq (P.top (T.right (P.sub n par))) cur in
         let w1 = EQ.ref_eq (P.top (T.right (P.sub n gp))) par in
         D.same_side n cur == (w0 = w1) /\
         (if w0 = w1 then
            (if w0 then T.Branch? (T.right (P.sub n gp)) else T.Branch? (T.left (P.sub n gp)))
          else if w0 then T.Branch? (T.left (P.sub n gp)) /\ T.Branch? (T.right (T.left (P.sub n gp)))
          else T.Branch? (T.right (P.sub n gp)) /\ T.Branch? (T.left (T.right (P.sub n gp)))) /\
        T.Branch? (P.sub n gp) /\
        D.balance n cur == P.replace n gp
          (D.balance_sub
            (EQ.ref_eq (P.top (T.right (P.sub n par))) cur)
            (EQ.ref_eq (P.top (T.right (P.sub n gp))) par)
            (P.sub n gp))))
  = P.focus_plug n cur;
    let f0::f1::rest = fst (P.focus n cur) in
    let s = P.sub n cur in
    let ps = P.fill f0 s in
    let gs = P.fill f1 ps in
    D.focus_at (f1::rest) ps;
    D.focus_at rest gs;
    P.distinct_plug rest gs;
    P.mem_plug par (f1::rest) ps;
    P.mem_plug gp rest gs;
    let nonnull (y: B.box (N.class_Node__raw a)) :
      Lemma (FStar.List.Tot.memP y (P.nboxes gs) ==> B.is_null y == false)
      = P.mem_plug y rest gs in
    FStar.Classical.forall_intro nonnull;
    D.balance_sub_shape f0 f1 s;
    D.balance_shape f0 f1 rest s

let rotated_facts (#a: Type0) (s: C.tree a) (w0 w1: bool)
  : Lemma (requires C.good s /\ T.Branch? s /\ can_rotate w0 w1 s)
      (ensures C.member (D.rot_for w0 w1 s) (P.top s))
  = if w0 = w1 then () else ()

let balance_result (#a: Type0) (s: C.tree a) (w0 w1: bool)
  : Lemma (requires C.good (M.recolor (D.rot_for w0 w1 s) (P.top s) true) /\ P.top s =!= B.null)
      (ensures
        M.recolor (M.recolor (D.rot_for w0 w1 s) (P.top s) true)
          (P.top (M.recolor (D.rot_for w0 w1 s) (P.top s) true)) false
        == D.balance_sub w0 w1 s)
  = root_color (M.recolor (D.rot_for w0 w1 s) (P.top s) true) false
