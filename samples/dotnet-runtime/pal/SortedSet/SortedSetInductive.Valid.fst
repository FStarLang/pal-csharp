module SortedSetInductive.Valid

module O = SortedSetInductive.Ownership
module S = Class_SortedSet
module M = Struct_SortedSetModel
module N = Class_Node

// The genuine exported model refinement, instantiated with the actual fields.
// Useful while an operation keeps the receiver's raw cell open across a loop.
// Inline this exact refinement instead of spending SMT fuel on an extra alias.
unfold let state (#a: Type0) {| equality_a: Pulse.Lib.CSharp.EqualityModel.has_equality a |}
    (root: N.class_Node__opt a) (s: O.state a)
    (c: Pulse.Lib.CSharp.Order.comparer a) (count version: int) =
  S.class_SortedSet__model__pred
    { M.fld_Tree=O.values (O.active s); M.fld_Comparer=c;
      M.fld_Count=count; M.fld_Version=version; M.fld_Root=root; M.fld_Labels=O.active s;
      M.fld_Observation=SortedSetInductive.State.observe s }
