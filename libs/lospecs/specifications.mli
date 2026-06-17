(* ==================================================================== *)
val circuit_of_specification : Circuit.reg list -> Ast.adef -> Circuit.reg
val load_from_file : filename:string -> (string * Ast.adef) list
