module InductiveRemoveRepair

module C = InductiveCursor
module N = Class_RbNode
module D = Pulse.Lib.CSharp.TopDown
module R = Pulse.Lib.CSharp.TopDownRemove
module P = Pulse.Lib.CSharp.RegionPath
module T = Pulse.Lib.CSharp.Tree
module O = Pulse.Lib.CSharp.Order
module B = Pulse.Lib.Box
module Seq = FStar.Seq
module I = InductiveRemove
module A = InductiveLift
module W = InductiveBorrow
module X = InductiveRemoveRotation

#set-options "--z3rlimit 10"

let frame_layout (#a: Type0) (f: C.frame a) (rest: list (C.frame a)) (s: C.tree a)
  : Lemma (requires C.good (P.plug (f::rest) s) /\ T.Branch? s /\ T.Branch? f.P.fsib)
    (ensures (
      let n = P.plug (f::rest) s in
      let par = f.P.fbox in
      let sib = P.top f.P.fsib in
      let cur = P.top s in
      par =!= B.null /\ sib =!= B.null /\ cur =!= B.null /\
      C.member n par /\ C.member n sib /\
      P.sub n par == P.fill f s /\ P.sub n sib == f.P.fsib /\
      I.sibling n par cur == sib /\
      Pulse.Lib.CSharp.Region.eq_box (P.top (T.left (P.sub n par))) cur == not f.P.went_right /\
      A.child (P.sub n par) sib /\ A.right (P.sub n par) sib == not f.P.went_right /\
      T.Branch? (T.left (P.sub n par)) /\ T.Branch? (T.right (P.sub n par))))
  = I.path_facts (f::rest) s;
    D.focus_at rest (P.fill f s);
    let other = {f with P.went_right=not f.P.went_right; P.fsib=s} in
    assert (P.fill other f.P.fsib == P.fill f s);
    D.focus_at (other::rest) f.P.fsib;
    P.distinct_plug rest (P.fill f s);
    assert (P.top s =!= P.top f.P.fsib)

let sibling_node (#a: Type0) (c: O.comparer a) (ks: Seq.seq a)
    (f: C.frame a) (rest: list (C.frame a)) (s: C.tree a)
  : Lemma (requires D.ok c ks (P.plug (f::rest) s) /\ R.is2 s)
    (ensures T.Branch? f.P.fsib)
  = D.rb_plug_sub rest (P.fill f s);
    D.rb_fill f s;
    R.bh_black s;
    R.bh_branch f.P.fsib

let at_sib (#a: Type0) (c: O.comparer a) (ks: Seq.seq a) (k: a) (n: C.tree a)
    (cur par gp mt pom: N.class_RbNode__opt a) (found: bool)
  : Lemma (requires I.inv c ks k n cur par gp mt pom found /\ cur =!= B.null /\
      par =!= B.null /\ R.is2 (P.sub n cur))
    (ensures (
      let sib = I.sibling n par cur in
      sib =!= B.null /\ C.member n sib /\ A.child (P.sub n par) sib))
  = let (fs,s) = R.rdesc_elim c k n cur par gp mt pom found in
    I.path_facts fs s;
    let f::rest = fs in
    sibling_node c ks f rest s;
    frame_layout f rest s

let at_mid (#a: Type0) (c: O.comparer a) (ks: Seq.seq a) (k: a) (n: C.tree a)
    (cur par gp mt pom: N.class_RbNode__opt a) (found: bool) (m: int)
  : Lemma (requires I.mid c ks k n cur par gp mt pom found m)
    (ensures (
      let sib = I.sibling n par cur in
      C.good n /\ cur =!= B.null /\ par =!= B.null /\ sib =!= B.null /\
      C.member n cur /\ C.member n par /\ C.member n sib /\
      D.parent_of n par == gp /\
      T.Branch? (T.left (P.sub n par)) /\ T.Branch? (T.right (P.sub n par))))
  = let (fs,s) = R.mdesc_elim c k n cur par gp mt pom found in
    I.path_facts fs s;
    let f::rest = fs in
    frame_layout f rest s

let lifted (#a: Type0) (n: C.tree a) (par cur: N.class_RbNode__opt a) =
  A.whole n par (I.sibling n par cur)

let lift (#a: Type0) (c: O.comparer a) (ks: Seq.seq a) (k: a) (n: C.tree a)
    (cur par gp mt pom: N.class_RbNode__opt a) (found: bool)
  : Lemma (requires I.inv c ks k n cur par gp mt pom found /\ cur =!= B.null /\
      par =!= B.null /\ R.is2 (P.sub n cur) /\ D.nred (P.sub n (I.sibling n par cur)))
    (ensures (
      let sib = I.sibling n par cur in
      I.mid c ks k (lifted n par cur) cur par sib mt (R.pom_a par mt sib pom) found (I.measure n cur)))
  = let (fs,s) = R.rdesc_elim c k n cur par gp mt pom found in
    I.path_facts fs s;
    let f::rest = fs in
    sibling_node c ks f rest s;
    frame_layout f rest s;
    R.fix_a c ks k f rest s cur par gp mt pom found;
    let (f0,f1) = R.a_frames f in
    let fs' = f0::f1::rest in
    let sib = P.top f.P.fsib in
    assert (A.rotated (P.fill f s) sib == R.arot f.P.went_right (P.fill f s));
    D.focus_at rest (P.fill f s);
    assert (A.lifted (P.fill f s) sib ==
      D.recolorn (R.rcol (R.arot f.P.went_right (P.fill f s)) par true) false);
    assert (lifted n par cur == P.plug fs' s);
    R.mdesc_intro c k fs' s cur par sib mt (R.pom_a par mt sib pom) found;
    D.sub_top fs' s

let rotation (#a: Type0) (n: C.tree a) (par cur: N.class_RbNode__opt a) =
  W.choose (Pulse.Lib.CSharp.Region.eq_box (P.top (T.left (P.sub n par))) cur)
    (D.nred (T.left (P.sub n (I.sibling n par cur))))
let borrowed (#a: Type0) (n: C.tree a) (par cur: N.class_RbNode__opt a) =
  P.replace n par (W.borrowed (P.sub n par) cur (rotation n par cur))
let new_parent (#a: Type0) (n: C.tree a) (par cur: N.class_RbNode__opt a) =
  P.top (R.rotn (rotation n par cur) (P.sub n par))

let borrow (#a: Type0) (c: O.comparer a) (ks: Seq.seq a) (k: a) (n: C.tree a)
    (cur par gp mt pom: N.class_RbNode__opt a) (found: bool) (m: int)
  : Lemma (requires I.mid c ks k n cur par gp mt pom found m /\
      not (R.is2 (P.sub n (I.sibling n par cur))))
    (ensures W.ready (P.sub n par) cur (rotation n par cur) /\
      I.fixed c ks k (borrowed n par cur) cur par mt
        (R.pom_a par mt (new_parent n par cur) pom) found m)
  = let (fs,s) = R.mdesc_elim c k n cur par gp mt pom found in
    I.path_facts fs s;
    let f::rest = fs in
    frame_layout f rest s;
    D.focus_at rest (P.fill f s);
    R.fix_b2 c ks k f rest s cur par gp mt pom found;
    P.distinct_plug rest (P.fill f s);
    R.b2_shape f s;
    assert (rotation n par cur == R.b2_rot f.P.went_right f.P.fsib);
    let (f0,f1) = R.b2_frames f in
    let fs' = f0::f1::rest in
    assert (W.ready (P.sub n par) cur (rotation n par cur));
    assert (borrowed n par cur == P.plug fs' (D.recolorn s true));
    R.fdesc_intro c k fs' (D.recolorn s true) cur par mt
      (R.pom_a par mt f1.P.fbox pom) found;
    D.sub_top fs' (D.recolorn s true)
