let int x = Z.to_string (FStar_Int32.v x)
let () =
  List.iter (fun x -> List.iter (fun y ->
    Printf.printf "%b %b %b\n"
      (Xor.func_Semantics_Xor_func_Semantics_Xor x y)
      (And.func_Semantics_And_func_Semantics_And x y)
      (Or.func_Semantics_Or_func_Semantics_Or x y)) [false; true]) [false; true];
  List.iter (fun x -> Printf.printf "%s %s\n"
    (int (EagerAnd.func_Semantics_EagerAnd_func_Semantics_EagerAnd x))
    (int (ShortAnd.func_Semantics_ShortAnd_func_Semantics_ShortAnd x))) [false; true];
  List.iter (fun x -> Printf.printf "%s\n"
    (Z.to_string (FStar_UInt8.v
      (Narrow.func_Semantics_Narrow_func_Semantics_Narrow (FStar_Int32.int_to_t (Z.of_int x))))))
    [-1; 0; 255; 256; 511];
  print_endline (int (Widen.func_Semantics_Widen_func_Semantics_Widen (FStar_UInt8.uint_to_t (Z.of_int 255))));
  print_endline (int (Named.func_Semantics_Named_func_Semantics_Named ()));
  print_endline (int (DebugErasure.func_Semantics_DebugErasure_func_Semantics_DebugErasure ()));
  print_endline (int (ArrayOps.func_Semantics_ArrayOps_func_Semantics_ArrayOps ()));
  print_endline (int (MakeAndSum.func_Shapes_MakeAndSum_func_Shapes_MakeAndSum ()));
  print_endline (int (GrowTile.func_Shapes_GrowTile_func_Shapes_GrowTile ()));
  print_endline (int (GrowAndMeasureSide.func_Shapes_GrowAndMeasureSide_func_Shapes_GrowAndMeasureSide ()))
