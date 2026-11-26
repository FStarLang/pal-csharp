module SortedSetInductive.Fallback.Reference

module B = Pulse.Lib.Box
module E = Pulse.Lib.CSharp.Equality
module H = HashSetChain
module F = SortedSetInductive.Fallback
module Seq = FStar.Seq
module HC = Pulse.Lib.CSharp.HashChain
module R = Pulse.Lib.CSharp.Region
module Count = SortedSetCount

let mem (#r: Type0) (comparer: option (E.comparer (B.box r)))
    (nodes: Seq.seq (B.box r)) (node: B.box r)
  : Lemma
      (requires H.same_equality #(B.box r) #(E.reference_equality r) None comparer)
      (ensures H.mem #(B.box r) #(E.reference_equality r) comparer nodes node
               <==> F.node_mem nodes node)
  = H.mem_reference #r comparer nodes node;
    F.node_mem_exists nodes node

let rec insert_mem (#r: Type0) (nodes: Seq.seq (B.box r))
    (index: nat { index <= Seq.length nodes }) (node p: B.box r)
  : Lemma (ensures F.node_mem (HC.insert_at nodes index node) p ==
                   (R.eq_box p node || F.node_mem nodes p))
          (decreases Seq.length nodes)
  = if index = Seq.length nodes then begin
      HC.insert_at_end nodes node;
      Count.init_snoc nodes node
    end else begin
      let prefix = Count.init nodes in
      insert_mem prefix index node p;
      HC.insert_snoc prefix index node (Seq.last nodes);
      Count.init_snoc (HC.insert_at prefix index node) (Seq.last nodes)
    end

let added (#r: Type0) (before after: Seq.seq (B.box r)) (node: B.box r)
  : Lemma (requires H.added before after node)
          (ensures forall (p: B.box r). F.node_mem after p ==
                   (R.eq_box p node || F.node_mem before p))
  = let index = FStar.IndefiniteDescription.indefinite_description_ghost nat
        (fun index -> index <= Seq.length before /\ after == HC.insert_at before index node) in
    FStar.Classical.forall_intro (fun p -> insert_mem before index node p)

let unchanged (#r: Type0) (nodes: Seq.seq (B.box r)) (node: B.box r)
  : Lemma (requires F.node_mem nodes node)
          (ensures forall (p: B.box r). F.node_mem nodes p ==
                   (R.eq_box p node || F.node_mem nodes p))
  = ()
