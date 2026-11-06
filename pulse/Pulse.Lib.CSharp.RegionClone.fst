module Pulse.Lib.CSharp.RegionClone

/// R27.43. Copying a region's tree into fresh nodes of the same region, top-down, from a
/// stack of (source, target) pairs (`SortedSet<T>.Node.DeepClone`).
///
/// The copy so far is the *zip* of the source tree with the target pointer: the source's
/// shape, cut wherever a target link is still null, each node pairing a source box with
/// the target box made for it. A pair on the stack is a *pending* node, whose links are
/// not yet set; every other node of the zip has a target link exactly where the source
/// has one. The invariant (`cloning`) says what each node of the zip is
/// (`node_ok`), that the targets are distinct, fresh and every pair of the stack is a node,
/// and that nothing the source reaches has moved. Linking a pending node's child to a
/// fresh copy of the source child (`link`) grows the zip by one node; popping a node whose
/// children are both linked (`done_`) leaves it complete. With the stack empty the zip is
/// the whole source tree, and the target's tree is the source's (`finish`).
///
/// Nothing here is trusted: it is built on `Pulse.Lib.CSharp.Region` and `RegionTree`.

open Pulse.Lib.CSharp.Region
open Pulse.Lib.CSharp.RegionTree
module B = Pulse.Lib.Box
module L = FStar.List.Tot
module LP = FStar.List.Tot.Properties
module T = Pulse.Lib.CSharp.Tree
module Seq = FStar.Seq

let lnk (#r: Type0) (left right: r -> B.box r) (d: bool) (v: r) : B.box r =
  if d then left v else right v

(* ------------------------------------------------------------------------------------ *)
(* The zip of a source tree with a target pointer                                        *)

let rec zip (#r: Type0) (left right: r -> B.box r) (h: heap r) (st: T.tree (B.box r & r))
    (y: B.box r) : Tot (T.tree (B.box r & B.box r)) (decreases st)
  = match st with
    | T.Leaf -> T.Leaf
    | T.Branch sl (s, _) sr ->
      if B.is_null y then T.Leaf
      else match lookup h y with
        | None -> T.Leaf
        | Some ry -> T.Branch (zip left right h sl (left ry)) (s, y) (zip left right h sr (right ry))

let rec nodes (#a: Type) (t: T.tree a) : Tot (list a) (decreases t) =
  match t with
  | T.Leaf -> []
  | T.Branch l k rr -> k :: L.append (nodes l) (nodes rr)

let rec tgts (#r: Type0) (t: T.tree (B.box r & B.box r)) : Tot (list (B.box r)) (decreases t) =
  match t with
  | T.Leaf -> []
  | T.Branch l (_, y) rr -> y :: L.append (tgts l) (tgts rr)

/// The target tree the zip describes, each node with the record the heap holds for it.
let rec ctree (#r: Type0) (left right: r -> B.box r) (h: heap r) (st: T.tree (B.box r & r))
    (y: B.box r) : Tot (T.tree (B.box r & r)) (decreases st)
  = match st with
    | T.Leaf -> T.Leaf
    | T.Branch sl _ sr ->
      if B.is_null y then T.Leaf
      else match lookup h y with
        | None -> T.Leaf
        | Some ry -> T.Branch (ctree left right h sl (left ry)) (y, ry) (ctree left right h sr (right ry))

let rec nodes_tgts (#r: Type0) (t: T.tree (B.box r & B.box r)) (s y: B.box r)
  : Lemma (requires L.memP (s, y) (nodes t)) (ensures L.memP y (tgts t)) (decreases t)
  = match t with
    | T.Branch l _ rr ->
      if FStar.IndefiniteDescription.strong_excluded_middle (L.memP (s, y) (nodes l))
      then nodes_tgts l s y
      else if FStar.IndefiniteDescription.strong_excluded_middle (L.memP (s, y) (nodes rr))
      then nodes_tgts rr s y
      else ()

let rec tgts_nodes (#r: Type0) (t: T.tree (B.box r & B.box r)) (y: B.box r)
  : Lemma (requires L.memP y (tgts t)) (ensures exists (s: B.box r). L.memP (s, y) (nodes t))
          (decreases t)
  = match t with
    | T.Branch l (s0, y0) rr ->
      if FStar.IndefiniteDescription.strong_excluded_middle (L.memP y (tgts l)) then tgts_nodes l y
      else if FStar.IndefiniteDescription.strong_excluded_middle (L.memP y (tgts rr)) then tgts_nodes rr y
      else assert (L.memP (s0, y) (nodes t))

/// Distinct targets: a target is paired with one source.
let rec nodes_unique (#r: Type0) (t: T.tree (B.box r & B.box r)) (s1 s2 y: B.box r)
  : Lemma (requires distinct (tgts t) /\ L.memP (s1, y) (nodes t) /\ L.memP (s2, y) (nodes t))
          (ensures s1 == s2) (decreases t)
  = match t with
    | T.Branch l (s0, y0) rr ->
      let inl s = L.memP (s, y) (nodes l) in
      let inr s = L.memP (s, y) (nodes rr) in
      FStar.Classical.move_requires (nodes_tgts l s1) y;
      FStar.Classical.move_requires (nodes_tgts l s2) y;
      FStar.Classical.move_requires (nodes_tgts rr s1) y;
      FStar.Classical.move_requires (nodes_tgts rr s2) y;
      if FStar.IndefiniteDescription.strong_excluded_middle (inl s1 /\ inl s2) then nodes_unique l s1 s2 y
      else if FStar.IndefiniteDescription.strong_excluded_middle (inr s1 /\ inr s2) then nodes_unique rr s1 s2 y
      else ()

let rec zip_size (#r: Type0) (left right: r -> B.box r) (h: heap r) (st: T.tree (B.box r & r))
    (y: B.box r)
  : Lemma (ensures L.length (tgts (zip left right h st y)) <= T.size st) (decreases st)
  = match st with
    | T.Leaf -> ()
    | T.Branch sl _ sr ->
      if B.is_null y then ()
      else match lookup h y with
        | None -> ()
        | Some ry ->
          zip_size left right h sl (left ry); zip_size left right h sr (right ry);
          L.append_length (tgts (zip left right h sl (left ry))) (tgts (zip left right h sr (right ry)))

let rec zip_ctree (#r: Type0) (left right: r -> B.box r) (h: heap r) (st: T.tree (B.box r & r))
    (y: B.box r)
  : Lemma (ensures boxes (ctree left right h st y) == tgts (zip left right h st y)) (decreases st)
  = match st with
    | T.Leaf -> ()
    | T.Branch sl _ sr ->
      if B.is_null y then ()
      else match lookup h y with
        | None -> ()
        | Some ry -> zip_ctree left right h sl (left ry); zip_ctree left right h sr (right ry)

let rec vmap_size (#a #v: Type0) (view: B.box a -> a -> v) (t: T.tree (B.box a & a))
  : Lemma (ensures T.size (vmap view t) == T.size t) (decreases t)
  = match t with
    | T.Leaf -> ()
    | T.Branch l _ rr -> vmap_size view l; vmap_size view rr

let rec tgts_mem (#r: Type0) (left right: r -> B.box r) (h: heap r) (st: T.tree (B.box r & r))
    (y z: B.box r)
  : Lemma (requires L.memP z (tgts (zip left right h st y))) (ensures mem h z) (decreases st)
  = match st with
    | T.Branch sl _ sr ->
      (match lookup h y with
       | Some ry ->
         if FStar.IndefiniteDescription.strong_excluded_middle (L.memP z (tgts (zip left right h sl (left ry))))
         then tgts_mem left right h sl (left ry) z
         else if FStar.IndefiniteDescription.strong_excluded_middle (L.memP z (tgts (zip left right h sr (right ry))))
         then tgts_mem left right h sr (right ry) z
         else ())

(* ------------------------------------------------------------------------------------ *)
(* Frames                                                                                *)

/// Every node of the zip is a box of the heap, and so is every non-null link it holds.
let zclosed (#r: Type0) (left right: r -> B.box r) (h: heap r) (t: T.tree (B.box r & B.box r))
  : prop =
  forall (n: B.box r & B.box r). L.memP n (nodes t) ==>
    mem h (snd n) /\
    (B.is_null (left (get h (snd n))) == false ==> mem h (left (get h (snd n)))) /\
    (B.is_null (right (get h (snd n))) == false ==> mem h (right (get h (snd n))))

/// A heap that holds every target as `h` did has the same zip.
let rec zip_frame (#r: Type0) (left right: r -> B.box r) (h h': heap r)
    (st: T.tree (B.box r & r)) (y: B.box r)
  : Lemma (requires (B.is_null y \/ T.Leaf? st \/ mem h y) /\
                    zclosed left right h (zip left right h st y) /\
                    (forall (z: B.box r). L.memP z (tgts (zip left right h st y)) ==> lookup h' z == lookup h z))
          (ensures zip left right h' st y == zip left right h st y)
          (decreases st)
  = match st with
    | T.Leaf -> ()
    | T.Branch sl (s, _) sr ->
      if B.is_null y then ()
      else begin
        let ry = get h y in
        let t = zip left right h st y in
        assert (L.memP (s, y) (nodes t));
        assert (L.memP y (tgts t));
        zip_frame left right h h' sl (left ry);
        zip_frame left right h h' sr (right ry)
      end

(* ------------------------------------------------------------------------------------ *)
(* Linking a child                                                                       *)

/// What a link step leaves of the zip at `y0`: where `y` is a target, the zip has gained
/// the node `(c, c')`, `c` the source child on side `d` of `y`'s source.
let linked (#r: Type0) (left right: r -> B.box r) (h0 h h': heap r) (st: T.tree (B.box r & r))
    (y0: B.box r) (d: bool) (s y c': B.box r) : prop =
  let t = zip left right h st y0 in
  let t' = zip left right h' st y0 in
  (L.memP y (tgts t) ==>
    mem h0 s /\
    (forall (n: B.box r & B.box r). L.memP n (nodes t') <==>
       L.memP n (nodes t) \/ n == (lnk left right d (get h0 s), c')) /\
    (forall (z: B.box r). L.memP z (tgts t') <==> L.memP z (tgts t) \/ z == c') /\
    distinct (tgts t') /\ L.length (tgts t') == L.length (tgts t) + 1) /\
  (~ (L.memP y (tgts t)) ==> t' == t)

/// One leaf node `cc` grown on an empty side of the root.
let grow (#r: Type0) (tl tr tl' tr': T.tree (B.box r & B.box r)) (k cc: B.box r & B.box r)
  : Lemma (requires ((tl == T.Leaf /\ tl' == T.Branch T.Leaf cc T.Leaf /\ tr' == tr) \/
                     (tr == T.Leaf /\ tr' == T.Branch T.Leaf cc T.Leaf /\ tl' == tl)) /\
                    distinct (tgts (T.Branch tl k tr)) /\ ~ (L.memP (snd cc) (tgts (T.Branch tl k tr))))
          (ensures (let t = T.Branch tl k tr in
                    let t' = T.Branch tl' k tr' in
                    (forall (n: B.box r & B.box r). L.memP n (nodes t') <==> L.memP n (nodes t) \/ n == cc) /\
                    (forall (z: B.box r). L.memP z (tgts t') <==> L.memP z (tgts t) \/ z == snd cc) /\
                    distinct (tgts t') /\ L.length (tgts t') == L.length (tgts t) + 1))
  = let (_, c') = cc in
    let (_, y) = k in
    assert (tgts (T.Branch T.Leaf cc T.Leaf) == [c']);
    assert (nodes (T.Branch T.Leaf cc T.Leaf) == [cc]);
    L.append_length (tgts tl) (tgts tr);
    L.append_length (tgts tl') (tgts tr');
    let a = L.append (tgts tl) (tgts tr) in
    let a' = L.append (tgts tl') (tgts tr') in
    assert (tgts (T.Branch tl k tr) == y :: a);
    assert (tgts (T.Branch tl' k tr') == y :: a');
    assert (nodes (T.Branch tl k tr) == k :: L.append (nodes tl) (nodes tr));
    assert (nodes (T.Branch tl' k tr') == k :: L.append (nodes tl') (nodes tr'));
    assert (distinct a /\ ~ (L.memP y a));
    assert (L.memP c' [c']);
    if FStar.IndefiniteDescription.strong_excluded_middle (tl == T.Leaf /\ tl' == T.Branch T.Leaf cc T.Leaf /\ tr' == tr)
    then begin
      assert (a == tgts tr);
      assert (a' == c' :: tgts tr);
      assert (L.append (nodes tl) (nodes tr) == nodes tr);
      assert (L.append (nodes tl') (nodes tr') == cc :: nodes tr)
    end else begin
      assert (tr == T.Leaf /\ tr' == T.Branch T.Leaf cc T.Leaf /\ tl' == tl);
      assert (tgts tr' == [c'] /\ nodes tr' == [cc]);
      assert (a' == L.append (tgts tl) [c']);
      assert (L.append (nodes tl') (nodes tr') == L.append (nodes tl) [cc]);
      L.append_l_nil (tgts tl);
      assert (a == tgts tl);
      L.append_l_nil (nodes tl);
      distinct_append (tgts tl) [c'];
      let auxz (z: B.box r) : Lemma (L.memP z a' <==> L.memP z a \/ z == c') =
        mem_append z (tgts tl) [c']; assert (L.memP z [c'] <==> z == c') in
      FStar.Classical.forall_intro auxz;
      let auxn (n: B.box r & B.box r)
        : Lemma (L.memP n (L.append (nodes tl') (nodes tr')) <==> L.memP n (L.append (nodes tl) (nodes tr)) \/ n == cc) =
        mem_append n (nodes tl) [cc]; assert (L.memP n [cc] <==> n == cc) in
      FStar.Classical.forall_intro auxn
    end

let rec zip_link (#r: Type0) (left right: r -> B.box r) (h0 h h': heap r)
    (st: T.tree (B.box r & r)) (x0 y0: B.box r) (d: bool) (s y c': B.box r)
  : Lemma (requires realizes left right h0 x0 st /\
                    (B.is_null y0 \/ T.Leaf? st \/ mem h y0) /\
                    zclosed left right h (zip left right h st y0) /\
                    distinct (tgts (zip left right h st y0)) /\
                    (forall (z: B.box r). mem h z /\ ~ (z == y) ==> lookup h' z == lookup h z) /\
                    ~ (mem h c') /\ B.is_null c' == false /\ mem h' c' /\
                    B.is_null (left (get h' c')) /\ B.is_null (right (get h' c')) /\
                    (L.memP y (tgts (zip left right h st y0)) ==>
                      L.memP (s, y) (nodes (zip left right h st y0)) /\
                      mem h y /\ mem h' y /\ mem h0 s /\
                      B.is_null (lnk left right d (get h y)) /\
                      lnk left right d (get h' y) == c' /\
                      lnk left right (not d) (get h' y) == lnk left right (not d) (get h y) /\
                      B.is_null (lnk left right d (get h0 s)) == false))
          (ensures linked left right h0 h h' st y0 d s y c')
          (decreases st)
  = let t = zip left right h st y0 in
    let frame_all () : Lemma (requires ~ (L.memP y (tgts t))) (ensures zip left right h' st y0 == t) =
      let aux (z: B.box r) : Lemma (L.memP z (tgts t) ==> lookup h' z == lookup h z) =
        if FStar.IndefiniteDescription.strong_excluded_middle (L.memP z (tgts t))
        then tgts_mem left right h st y0 z else () in
      FStar.Classical.forall_intro aux;
      zip_frame left right h h' st y0 in
    if FStar.IndefiniteDescription.strong_excluded_middle (L.memP y (tgts t)) then begin
      match st with
      | T.Branch sl (s0, rs) sr ->
        let ry = get h y0 in
        let tl = zip left right h sl (left ry) in
        let tr = zip left right h sr (right ry) in
        assert (t == T.Branch tl (s0, y0) tr);
        let frame_sub (sub: T.tree (B.box r & r)) (yy: B.box r)
          : Lemma (requires L.memP y0 (tgts t) /\
                            (B.is_null yy \/ T.Leaf? sub \/ mem h yy) /\
                            zclosed left right h (zip left right h sub yy) /\
                            (forall (z: B.box r). L.memP z (tgts (zip left right h sub yy)) ==> L.memP z (tgts t)) /\
                            ~ (L.memP y (tgts (zip left right h sub yy))))
                  (ensures zip left right h' sub yy == zip left right h sub yy)
          = let aux (z: B.box r) : Lemma (L.memP z (tgts (zip left right h sub yy)) ==> lookup h' z == lookup h z) =
              if FStar.IndefiniteDescription.strong_excluded_middle (L.memP z (tgts (zip left right h sub yy)))
              then tgts_mem left right h sub yy z else () in
            FStar.Classical.forall_intro aux;
            zip_frame left right h h' sub yy in
        if FStar.IndefiniteDescription.strong_excluded_middle (y0 == y) then begin
          nodes_unique t s s0 y;
          assert (s == s0);
          let c = lnk left right d rs in
          FStar.Classical.forall_intro (FStar.Classical.move_requires (tgts_mem left right h st y0));
          if d then begin
            let T.Branch cl (_, rc) cr = sl in
            assert (zip left right h' sl c' == T.Branch T.Leaf (c, c') T.Leaf);
            assert (tl == T.Leaf);
            frame_sub sr (right ry);
            assert (zip left right h' st y0 == T.Branch (T.Branch T.Leaf (c, c') T.Leaf) (s0, y0) tr);
            grow tl tr (T.Branch T.Leaf (c, c') T.Leaf) tr (s0, y0) (c, c')
          end else begin
            let T.Branch cl (_, rc) cr = sr in
            assert (zip left right h' sr c' == T.Branch T.Leaf (c, c') T.Leaf);
            assert (tr == T.Leaf);
            frame_sub sl (left ry);
            assert (zip left right h' st y0 == T.Branch tl (s0, y0) (T.Branch T.Leaf (c, c') T.Leaf));
            grow tl tr tl (T.Branch T.Leaf (c, c') T.Leaf) (s0, y0) (c, c')
          end
        end else begin
          assert (lookup h' y0 == lookup h y0);
          FStar.Classical.move_requires (nodes_tgts tl s) y;
          FStar.Classical.move_requires (nodes_tgts tr s) y;
          if FStar.IndefiniteDescription.strong_excluded_middle (L.memP y (tgts tl)) then begin
            zip_link left right h0 h h' sl (left rs) (left ry) d s y c';
            frame_sub sr (right ry);
            let tl' = zip left right h' sl (left ry) in
            assert (zip left right h' st y0 == T.Branch tl' (s0, y0) tr);
            FStar.Classical.forall_intro (FStar.Classical.move_requires (tgts_mem left right h st y0));
            L.append_length (tgts tl) (tgts tr);
            L.append_length (tgts tl') (tgts tr)
          end else begin
            zip_link left right h0 h h' sr (right rs) (right ry) d s y c';
            frame_sub sl (left ry);
            let tr' = zip left right h' sr (right ry) in
            assert (zip left right h' st y0 == T.Branch tl (s0, y0) tr');
            FStar.Classical.forall_intro (FStar.Classical.move_requires (tgts_mem left right h st y0));
            L.append_length (tgts tl) (tgts tr);
            L.append_length (tgts tl) (tgts tr')
          end
        end
    end
    else frame_all ()

(* ------------------------------------------------------------------------------------ *)
(* The stack                                                                             *)

/// The stack's pairs, top first.
let rec plist (#a: Type) (p: Seq.seq a) : Tot (list a) (decreases Seq.length p) =
  if Seq.length p = 0 then []
  else let n = Seq.length p - 1 in Seq.index p n :: plist (Seq.slice p 0 n)

let plist_snoc (#a: Type) (p: Seq.seq a) (x: a)
  : Lemma (ensures plist (Seq.snoc p x) == x :: plist p)
  = Seq.lemma_eq_intro (Seq.slice (Seq.snoc p x) 0 (Seq.length p)) p

let rec plist_length (#a: Type) (p: Seq.seq a)
  : Lemma (ensures L.length (plist p) == Seq.length p) (decreases Seq.length p)
  = if Seq.length p = 0 then () else plist_length (Seq.slice p 0 (Seq.length p - 1))

let plist_empty (#a: Type) (p: Seq.seq a)
  : Lemma (requires Seq.length p == 0) (ensures plist p == [])
  = ()

/// `TryPop`: the stack it leaves, with the pair it popped on top, is the stack it found.
let snoc_pop (#a: Type) (p: Seq.seq a) (n: nat)
  : Lemma (requires n + 1 == Seq.length p)
          (ensures Seq.snoc (Seq.slice p 0 n) (Seq.index p n) == p)
          [SMTPat (Seq.snoc (Seq.slice p 0 n) (Seq.index p n))]
  = Seq.lemma_eq_intro (Seq.snoc (Seq.slice p 0 n) (Seq.index p n)) p

let rec memP_map_snd (#a #b: Type) (l: list (a & b)) (z: b)
  : Lemma (ensures L.memP z (L.map snd l) <==> (exists (s: a). L.memP (s, z) l)) (decreases l)
  = match l with
    | [] -> ()
    | (s0, z0) :: t -> memP_map_snd t z

(* ------------------------------------------------------------------------------------ *)
(* The invariant                                                                         *)

/// `(s, y)` is on the stack.
let pend (#r: Type0) (p: Seq.seq (B.box r & B.box r)) (s y: B.box r) : prop =
  L.memP (s, y) (plist p)

/// A side of a node of the zip: the target links only where the source does, to a box of
/// the heap; a pending node's link is still null, unless it is `busy` (the pair being
/// worked on); a node that is not pending links wherever the source does.
let side_ok (#r: Type0) (left right: r -> B.box r) (h0 h: heap r)
    (p: Seq.seq (B.box r & B.box r)) (busy: B.box r) (d: bool) (s y: B.box r) : prop =
  mem h0 s /\ mem h y /\
  (let ls = lnk left right d (get h0 s) in
   let ly = lnk left right d (get h y) in
   (B.is_null ls ==> B.is_null ly) /\
   (B.is_null ly == false ==> mem h ly) /\
   (pend p s y ==> y == busy \/ B.is_null ly) /\
   (~ (pend p s y) ==> B.is_null ly ==> B.is_null ls))

/// A node of the zip: a well-formed source, a fresh target of the same view.
let node_ok (#r #v: Type0) (view: B.box r -> r -> v) (left right: r -> B.box r) (h0 h: heap r)
    (p: Seq.seq (B.box r & B.box r)) (busy: B.box r) (n: B.box r & B.box r) : prop =
  let s = fst n in
  let y = snd n in
  B.is_null s == false /\ wf left right h0 s /\ mem h0 s /\
  B.is_null y == false /\ mem h y /\ ~ (mem h0 y) /\
  view y (get h y) == view s (get h0 s) /\
  side_ok left right h0 h p busy true s y /\ side_ok left right h0 h p busy false s y

[@@"opaque_to_smt"]
let cloning_core (#r #v: Type0) (view: B.box r -> r -> v) (left right: r -> B.box r)
    (h0: heap r) (x: B.box r) (h: heap r) (root: B.box r) (p: Seq.seq (B.box r & B.box r))
    (busy: B.box r) : prop =
  unshared left right h0 x /\ B.is_null x == false /\
  (forall (z: B.box r). mem h0 z ==> mem h z /\ lookup h z == lookup h0 z) /\
  B.is_null root == false /\ mem h root /\
  (let t = zip left right h (ltree left right h0 x) root in
   (forall (n: B.box r & B.box r). L.memP n (nodes t) ==> node_ok view left right h0 h p busy n) /\
   distinct (tgts t) /\
   distinct (L.map snd (plist p)) /\
   (forall (n: B.box r & B.box r). L.memP n (plist p) ==> L.memP n (nodes t)))

/// How many targets the copy has.
let nz (#r: Type0) (left right: r -> B.box r) (h0: heap r) (x: B.box r) (h: heap r)
    (root: B.box r) : GTot nat =
  L.length (tgts (zip left right h (ltree left right h0 x) root))

/// R27.43. The copy of the tree at `x` in `h0`, at `root` in `h`, with the stack `p`.
let cloning (#r #v: Type0) (view: B.box r -> r -> v) (left right: r -> B.box r)
    (h0: heap r) (x: B.box r) (h: heap r) (root: B.box r) (p: Seq.seq (B.box r & B.box r))
    (busy: B.box r) : prop =
  cloning_core view left right h0 x h root p busy /\
  Seq.length p <= nz left right h0 x h root /\
  nz left right h0 x h root <= T.size (tree_of view left right h0 x)

/// The invariant at the head of the loop: no pair is being worked on.
let cloning_at (#r #v: Type0) (view: B.box r -> r -> v) (left right: r -> B.box r)
    (h0: heap r) (x: B.box r) (h: heap r) (root: B.box r) (p: Seq.seq (B.box r & B.box r)) : prop =
  cloning view left right h0 x h root p B.null

/// The loop's measure: two for each node not yet copied, one for each pair on the stack.
let measure (#r #v: Type0) (view: B.box r -> r -> v) (left right: r -> B.box r)
    (h0: heap r) (x: B.box r) (h: heap r) (root: B.box r) (p: Seq.seq (B.box r & B.box r))
  : GTot nat =
  let n = T.size (tree_of view left right h0 x) in
  let z = nz left right h0 x h root in
  if z <= n then 2 * (n - z) + Seq.length p else 0

let size_of (#r #v: Type0) (view: B.box r -> r -> v) (left right: r -> B.box r)
    (h0: heap r) (x: B.box r)
  : Lemma (ensures T.size (tree_of view left right h0 x) == T.size (ltree left right h0 x))
  = tree_of_vmap view left right h0 x; vmap_size view (ltree left right h0 x)

(* ------------------------------------------------------------------------------------ *)
(* The steps                                                                             *)

/// A view tree with no children is the view of a boxed tree with no children.
let vmap_root_only (#a #v: Type0) (view: B.box a -> a -> v) (t: T.tree (B.box a & a)) (k: v)
  : Lemma (requires vmap view t == T.Branch T.Leaf k T.Leaf)
          (ensures (match t with
                    | T.Branch T.Leaf (b, r) T.Leaf -> view b r == k
                    | _ -> False))
  = match t with
    | T.Branch l _ rr -> (match l with T.Leaf -> () | _ -> ()); (match rr with T.Leaf -> () | _ -> ())

/// A fresh copy of one node (`ShallowClone`): its children are null, and it has the view
/// of the node it copies.
let shallow (#r #v: Type0) (view: B.box r -> r -> v) (left right: r -> B.box r)
    (h h1: heap r) (c c': B.box r)
  : Lemma (requires mem h c /\ B.is_null c == false /\
                    unshared left right h1 c' /\ reshaped left right h h1 B.null c' /\
                    tree_of view left right h1 c' == T.root_only (tree_of view left right h c))
          (ensures B.is_null c' == false /\ mem h1 c' /\ ~ (mem h c') /\
                   B.is_null (left (get h1 c')) /\ B.is_null (right (get h1 c')) /\
                   view c' (get h1 c') == view c (get h c) /\
                   (forall (z: B.box r). mem h z ==> mem h1 z /\ lookup h1 z == lookup h z))
  = tree_of_mem view left right h c;
    tree_of_vmap view left right h1 c';
    let t = ltree left right h1 c' in
    vmap_root_only view t (view c (get h c));
    unshared_elim left right h1 c';
    let T.Branch _ (b, rb) _ = t in
    assert (b == c' /\ lookup h1 c' == Some rb);
    assert (L.memP c' (boxes t))

let init (#r #v: Type0) (view: B.box r -> r -> v) (left right: r -> B.box r)
    (h0: heap r) (x: B.box r) (h: heap r) (root: B.box r) (st: Seq.seq (B.box r & B.box r))
  : Lemma (requires unshared left right h0 x /\ B.is_null x == false /\
                    unshared left right h root /\ reshaped left right h0 h B.null root /\
                    tree_of view left right h root == T.root_only (tree_of view left right h0 x) /\
                    Seq.length st == 0)
          (ensures cloning_at view left right h0 x h root (Seq.snoc st (x, root)))
  = reveal_opaque (`%cloning_core) (cloning_core #r #v);
    unshared_mem left right h0 x;
    shallow view left right h0 h x root;
    unshared_step left right h0 x;
    let p = Seq.snoc st (x, root) in
    plist_snoc st (x, root);
    plist_empty st;
    let t = zip left right h (ltree left right h0 x) root in
    assert (t == T.Branch T.Leaf (x, root) T.Leaf);
    assert (nodes t == [(x, root)]);
    assert (tgts t == [root]);
    assert (plist p == [(x, root)]);
    assert (L.map snd (plist p) == [root]);
    assert (pend p x root);
    unshared_wf left right h0 x;
    assert (node_ok view left right h0 h p B.null (x, root));
    size_of view left right h0 x

/// The top pair of the stack, popped: what the body needs of it to copy its children.
let pop (#r #v: Type0) (view: B.box r -> r -> v) (left right: r -> B.box r)
    (h0: heap r) (x: B.box r) (h: heap r) (root: B.box r) (st: Seq.seq (B.box r & B.box r))
    (nx: B.box r & B.box r)
  : Lemma (requires cloning_at view left right h0 x h root (Seq.snoc st nx))
          (ensures (let s = fst nx in
                    let y = snd nx in
                    cloning view left right h0 x h root (Seq.snoc st nx) y /\
                    measure view left right h0 x h root (Seq.snoc st nx) ==
                      2 * (T.size (tree_of view left right h0 x) - nz left right h0 x h root) + Seq.length st + 1 /\
                    B.is_null s == false /\ mem h0 s /\ mem h s /\ lookup h s == lookup h0 s /\
                    B.is_null y == false /\ mem h y /\ ~ (mem h0 y) /\
                    B.is_null (left (get h y)) /\ B.is_null (right (get h y)) /\
                    (B.is_null (left (get h s)) == false ==> mem h0 (left (get h s)) /\ mem h (left (get h s))) /\
                    (B.is_null (right (get h s)) == false ==> mem h0 (right (get h s)) /\ mem h (right (get h s)))))
  = reveal_opaque (`%cloning_core) (cloning_core #r #v);
    let p = Seq.snoc st nx in
    let s = fst nx in
    let y = snd nx in
    plist_snoc st nx;
    let t = zip left right h (ltree left right h0 x) root in
    assert (L.memP nx (nodes t));
    assert (node_ok view left right h0 h p B.null nx);
    assert (pend p s y);
    wf_step #r #unit (fun _ _ -> ()) left right h0 s;
    let weaken (n: B.box r & B.box r)
      : Lemma (requires node_ok view left right h0 h p B.null n)
              (ensures node_ok view left right h0 h p y n) = () in
    FStar.Classical.forall_intro (FStar.Classical.move_requires weaken)

/// What `link` needs of the heap after a write to the target `y`: every other box is as it
/// was, `y`'s link on side `d` is `c'`, its other link and its view are as they were.
let written (#r #v: Type0) (view: B.box r -> r -> v) (left right: r -> B.box r) (d: bool)
    (h1 h2: heap r) (y c': B.box r) : prop =
  mem h1 y /\ mem h2 y /\
  (forall (z: B.box r). ~ (z == y) ==> lookup h2 z == lookup h1 z) /\
  lnk left right d (get h2 y) == c' /\
  lnk left right (not d) (get h2 y) == lnk left right (not d) (get h1 y) /\
  view y (get h2 y) == view y (get h1 y)

/// The child `c` on side `d` of the popped source, copied to `c'` and linked under the
/// popped target `y`: the pair `(c, c')` goes on the stack, under the popped pair.
let link (#r #v: Type0) (view: B.box r -> r -> v) (left right: r -> B.box r) (d: bool)
    (h0: heap r) (x: B.box r) (h h1 h2: heap r) (root: B.box r)
    (st: Seq.seq (B.box r & B.box r)) (nx: B.box r & B.box r) (c': B.box r)
  : Lemma (requires cloning view left right h0 x h root (Seq.snoc st nx) (snd nx) /\
                    mem h (fst nx) /\ mem h (snd nx) /\
                    B.is_null (lnk left right d (get h (snd nx))) /\
                    B.is_null (lnk left right d (get h (fst nx))) == false /\
                    unshared left right h1 c' /\ reshaped left right h h1 B.null c' /\
                    tree_of view left right h1 c' ==
                      T.root_only (tree_of view left right h (lnk left right d (get h (fst nx)))) /\
                    written view left right d h1 h2 (snd nx) c')
          (ensures (let s = fst nx in
                    let y = snd nx in
                    let c = lnk left right d (get h s) in
                    cloning view left right h0 x h2 root (Seq.snoc (Seq.snoc st (c, c')) nx) y /\
                    nz left right h0 x h2 root == nz left right h0 x h root + 1 /\
                    mem h2 s /\ lookup h2 s == lookup h s /\ mem h2 y /\
                    lnk left right d (get h2 y) == c' /\ B.is_null c' == false /\
                    lnk left right (not d) (get h2 y) == lnk left right (not d) (get h y) /\
                    (forall (z: B.box r). mem h z ==> mem h2 z)))
  = reveal_opaque (`%cloning_core) (cloning_core #r #v);
    let s = fst nx in
    let y = snd nx in
    let c = lnk left right d (get h s) in
    let p = Seq.snoc st nx in
    let p' = Seq.snoc (Seq.snoc st (c, c')) nx in
    plist_snoc st nx;
    plist_snoc st (c, c');
    plist_snoc (Seq.snoc st (c, c')) nx;
    let st0 = ltree left right h0 x in
    let t = zip left right h st0 root in
    let t2 = zip left right h2 st0 root in
    unshared_elim left right h0 x;
    assert (L.memP nx (nodes t));
    assert (node_ok view left right h0 h p y nx);
    wf_step #r #unit (fun _ _ -> ()) left right h0 s;
    assert (mem h0 c);
    shallow view left right h h1 c c';
    assert (L.memP nx (nodes t));
    assert (node_ok view left right h0 h p y nx);
    assert (get h s == get h0 s);
    assert (~ (c' == y));
    assert (get h2 c' == get h1 c');
    let frame (z: B.box r) : Lemma (mem h z /\ ~ (z == y) ==> mem h2 z /\ lookup h2 z == lookup h z) = () in
    FStar.Classical.forall_intro frame;
    assert (zclosed left right h t);
    nodes_tgts t s y;
    zip_link left right h0 h h2 st0 x root d s y c';
    assert (linked left right h0 h h2 st0 root d s y c');
    let ok (n: B.box r & B.box r)
      : Lemma (requires L.memP n (nodes t2))
              (ensures node_ok view left right h0 h2 p' y n)
      = if FStar.IndefiniteDescription.strong_excluded_middle (n == (c, c')) then begin
          wf_step #r #unit (fun _ _ -> ()) left right h0 s;
          assert (pend p' c c')
        end else begin
          assert (L.memP n (nodes t));
          assert (node_ok view left right h0 h p y n);
          let (s1, y1) = n in
          assert (~ (y1 == c'));
          if FStar.IndefiniteDescription.strong_excluded_middle (y1 == y) then begin
            nodes_unique t s s1 y;
            assert (pend p' s y)
          end else begin
            assert (pend p' s1 y1 <==> pend p s1 y1)
          end
        end in
    FStar.Classical.forall_intro (FStar.Classical.move_requires ok);
    memP_map_snd (plist p) c';
    let notc (s1: B.box r) : Lemma (~ (L.memP (s1, c') (plist p))) =
      if FStar.IndefiniteDescription.strong_excluded_middle (L.memP (s1, c') (plist p))
      then nodes_tgts t s1 c' else () in
    FStar.Classical.forall_intro notc;
    assert (L.map snd (plist p') == y :: c' :: L.map snd (plist st));
    assert (L.map snd (plist p) == y :: L.map snd (plist st));
    zip_size left right h2 st0 root;
    size_of view left right h0 x;
    plist_length p';
    plist_length p;
    assert (distinct (L.map snd (plist p')));
    assert (forall (n: B.box r & B.box r). L.memP n (plist p') ==> L.memP n (nodes t2));
    assert (distinct (tgts t2));
    assert (forall (z: B.box r). mem h0 z ==> mem h2 z /\ lookup h2 z == lookup h0 z);
    assert (cloning_core view left right h0 x h2 root p' y);
    assert (Seq.length p' <= nz left right h0 x h2 root);
    assert (nz left right h0 x h2 root <= T.size (tree_of view left right h0 x))

/// The popped pair is done: every side of the target that is still null is null in the source.
let done_ (#r #v: Type0) (view: B.box r -> r -> v) (left right: r -> B.box r)
    (h0: heap r) (x: B.box r) (h: heap r) (root: B.box r)
    (st: Seq.seq (B.box r & B.box r)) (nx: B.box r & B.box r)
  : Lemma (requires cloning view left right h0 x h root (Seq.snoc st nx) (snd nx) /\
                    mem h (fst nx) /\ mem h (snd nx) /\
                    (B.is_null (left (get h (snd nx))) ==> B.is_null (left (get h (fst nx)))) /\
                    (B.is_null (right (get h (snd nx))) ==> B.is_null (right (get h (fst nx)))))
          (ensures cloning_at view left right h0 x h root st /\
                   measure view left right h0 x h root st ==
                     2 * (T.size (tree_of view left right h0 x) - nz left right h0 x h root) + Seq.length st)
  = reveal_opaque (`%cloning_core) (cloning_core #r #v);
    let s = fst nx in
    let y = snd nx in
    let p = Seq.snoc st nx in
    plist_snoc st nx;
    let t = zip left right h (ltree left right h0 x) root in
    assert (L.memP nx (nodes t));
    assert (get h s == get h0 s);
    let ok (n: B.box r & B.box r)
      : Lemma (requires L.memP n (nodes t))
              (ensures node_ok view left right h0 h st B.null n)
      = assert (node_ok view left right h0 h p y n);
        let (s1, y1) = n in
        if FStar.IndefiniteDescription.strong_excluded_middle (y1 == y) then begin
          nodes_unique t s s1 y;
          memP_map_snd (plist st) y;
          assert (~ (pend st s y))
        end else
          assert (pend st s1 y1 <==> pend p s1 y1) in
    FStar.Classical.forall_intro (FStar.Classical.move_requires ok);
    plist_length st;
    plist_length p

/// With no pair pending, the zip is the whole source: the copy realizes the source's shape.
let rec full (#r #v: Type0) (view: B.box r -> r -> v) (left right: r -> B.box r)
    (h0 h: heap r) (st: T.tree (B.box r & r)) (xs y: B.box r)
  : Lemma (requires realizes left right h0 xs st /\
                    (B.is_null y <==> B.is_null xs) /\ (B.is_null y == false ==> mem h y) /\
                    (forall (n: B.box r & B.box r). L.memP n (nodes (zip left right h st y)) ==>
                       node_ok view left right h0 h Seq.empty B.null n))
          (ensures realizes left right h y (ctree left right h st y) /\
                   vmap view (ctree left right h st y) == vmap view st)
          (decreases st)
  = match st with
    | T.Leaf -> ()
    | T.Branch sl (s, rs) sr ->
      plist_empty #(B.box r & B.box r) Seq.empty;
      let t = zip left right h st y in
      assert (L.memP (s, y) (nodes t));
      assert (node_ok view left right h0 h Seq.empty B.null (s, y));
      let ry = get h y in
      assert (~ (pend #r Seq.empty s y));
      full view left right h0 h sl (left rs) (left ry);
      full view left right h0 h sr (right rs) (right ry)

/// The loop is over: the copy is an unshared tree of fresh boxes with the source's view.
let finish (#r #v: Type0) (view: B.box r -> r -> v) (left right: r -> B.box r)
    (h0: heap r) (x: B.box r) (h: heap r) (root: B.box r) (p: Seq.seq (B.box r & B.box r))
  : Lemma (requires cloning_at view left right h0 x h root p /\ Seq.length p == 0)
          (ensures unshared left right h root /\ reshaped left right h0 h B.null root /\
                   tree_of view left right h root == tree_of view left right h0 x)
  = reveal_opaque (`%cloning_core) (cloning_core #r #v);
    Seq.lemma_empty p;
    let st0 = ltree left right h0 x in
    let t = zip left right h st0 root in
    unshared_elim left right h0 x;
    full view left right h0 h st0 x root;
    let ct = ctree left right h st0 root in
    zip_ctree left right h st0 root;
    unshared_intro left right h root ct;
    tree_of_vmap view left right h root;
    tree_of_vmap view left right h0 x;
    let fresh (z: B.box r) : Lemma (L.memP z (boxes ct) ==> ~ (mem h0 z)) =
      if FStar.IndefiniteDescription.strong_excluded_middle (L.memP z (boxes ct))
      then tgts_nodes t z else () in
    FStar.Classical.forall_intro fresh
