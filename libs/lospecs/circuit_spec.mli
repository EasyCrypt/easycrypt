(* ==================================================================== *)
val circuit_of_specification : Aig.reg list -> Ast.adef -> Aig.reg
val load_from_file : filename:string -> (string * Ast.adef) list
