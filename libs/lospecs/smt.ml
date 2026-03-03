open Aig
open Bitwuzla_cxx

module type SMTInstance = sig
  type bvterm

  exception SMTError
 
  (* Expected params: sort, value *)
  val bvterm_of_int : int -> int -> bvterm

  (* Expected params: sort, name *)
  val bvterm_of_name : int -> string -> bvterm

  (* argument must be of size 1, assert it true *)
  (* Should affect internal state of SMT *)
  val assert' : bvterm -> unit

  (* Check satisfiability of current asserts *)
  val check_sat : unit -> bool 

  (* equality over bitvectors, res is a size 1 bitvector *)
  val bvterm_equal : bvterm -> bvterm -> bvterm

  (* bvterm concat, res sort is sum of sorts *)
  val bvterm_concat : bvterm -> bvterm -> bvterm

  (* bvand *)
  val bvnot : bvterm -> bvterm

  (* bvnot *)
  val bvand : bvterm -> bvterm -> bvterm

  val lognot : bvterm -> bvterm

  val bvtobool : bvterm -> bvterm

  val get_value : bvterm -> bvterm

  val pp_term : Format.formatter -> bvterm -> unit
end

module type SMTInterface = sig
  val circ_equiv : ?inps:(int * int) list -> reg -> reg -> node ->  bool

  val circ_sat : ?inps:(int * int) list -> node -> bool

  val circ_taut : ?inps:(int * int) list -> node -> bool
end

(* TODO Add model printing for circ_sat and circ_taut *)
(* Assumes circuit inputs have already been appropriately renamed *)
module MakeSMTInterface(SMT: SMTInstance) : SMTInterface = struct
  let circ_equiv ?(inps: (int * int) list option) (r1 : Aig.reg) (r2 : Aig.reg) (pcond : Aig.node) : bool =
    if not ((Array.length r1 > 0) && (Array.length r2 > 0)) then
      (Format.eprintf "Sizes differ in circ_equiv"; false)
    else
    let bvvars : SMT.bvterm Map.String.t ref = ref Map.String.empty in

    let rec bvterm_of_node : Aig.node -> SMT.bvterm =
      let cache = Hashtbl.create 0 in
  
      let rec doit (n : Aig.node) =
        let mn = 
          match Hashtbl.find_option cache (Int.abs n.id) with
          | None ->
            let mn = doit_r n.gate in
            Hashtbl.add cache (Int.abs n.id) mn;
            mn
          | Some mn -> 
            mn
        in 
          if 0 < n.id then mn else SMT.bvnot mn

      and doit_r (n : Aig.node_r) = 
        match n with
        | False -> SMT.bvterm_of_int 1 0 
        | Input v -> let name = ("BV_" ^ (fst v |> string_of_int) ^ "_" ^ (Printf.sprintf "%X" (snd v))) in
        begin 
          match Map.String.find_opt name !bvvars with
          | None ->
            bvvars := Map.String.add name (SMT.bvterm_of_name 1 name) !bvvars;
            Map.String.find name !bvvars 
          | Some t -> t
        end
        | And (n1, n2) -> SMT.bvand (doit n1) (doit n2)

      in fun n -> doit n
    in 
  
    let bvterm_of_reg (r: Aig.reg) : _ =
      Array.map bvterm_of_node r |> Array.reduce (fun acc b -> SMT.bvterm_concat b acc)
    in 

    let bvinpt1 = (bvterm_of_reg r1) in
    let bvinpt2 = (bvterm_of_reg r2) in
    let formula = SMT.bvterm_equal bvinpt1 bvinpt2 in
    let pcond = (bvterm_of_node pcond) in
    let inps = Option.bind inps (fun l -> 
      if List.is_empty l then None
      else Some l
    ) in

    let inps = Option.map (fun inps ->
      List.map (fun (id,sz) -> 
      List.init sz (fun i -> ("BV_" ^ (id |> string_of_int) ^ "_" ^ (Printf.sprintf "%X" (i))))) inps 
    ) inps in
    let inps = Option.map (fun inps ->
    List.map (List.map (fun name -> match Map.String.find_opt name !bvvars with
    | Some bv -> bv
    | None -> SMT.bvterm_of_name 1 name)) inps) inps
    in
    let bvinp = Option.map (fun inps -> 
      List.map (fun i -> List.reduce (SMT.bvterm_concat) i) inps) inps 
    in

    begin
      SMT.assert' @@ SMT.bvand pcond (SMT.bvnot formula);
      if SMT.check_sat () = false then true 
      else begin
        Format.eprintf "bvout1: %a@."  SMT.pp_term (SMT.get_value bvinpt1);
        Format.eprintf "bvout2: %a@."  SMT.pp_term (SMT.get_value bvinpt2);
        Format.eprintf "Terms in formula: ";
        List.iter (Format.eprintf "%s ") (List.of_enum @@ Map.String.keys !bvvars);
        Format.eprintf "@\n";
        Option.may (fun bvinp ->
        List.iteri (fun i bv -> 
        Format.eprintf "input[%d]: %a@." i SMT.pp_term (SMT.get_value bv)        
        ) bvinp) bvinp;
        false
      end
    end


  (* TODO: better encoding of smt terms ? *)
  let circ_sat ?(inps: (int * int) list option) (n : Aig.node) : bool =
    let bvvars : SMT.bvterm Map.String.t ref = ref Map.String.empty in

    begin match inps with
    | None -> ()
    | Some inps -> List.iter (fun (id, sz) -> 
      List.iter (fun i -> 
        let name = ("BV_" ^ (string_of_int id) ^ "_" ^ (Printf.sprintf "%05X" i)) in
        bvvars := Map.String.add name (SMT.bvterm_of_name 1 name) !bvvars) 
        (List.init sz identity)) inps
    end;

    let rec bvterm_of_node : Aig.node -> SMT.bvterm =
      let cache = Hashtbl.create 0 in
  
      let rec doit (n : Aig.node) =
        let mn = 
          match Hashtbl.find_option cache (Int.abs n.id) with
          | None ->
            let mn = doit_r n.gate in
            Hashtbl.add cache (Int.abs n.id) mn;
            mn
          | Some mn -> 
            mn
        in 
          if 0 < n.id then mn else SMT.bvnot mn

      and doit_r (n : Aig.node_r) = 
        match n with
        | False -> SMT.bvterm_of_int 1 0 
        | Input v -> let name = ("BV_" ^ (fst v |> string_of_int) ^ "_" ^ (Printf.sprintf "%05X" (snd v))) in
        begin 
          match Map.String.find_opt name !bvvars with
          | None ->
            bvvars := Map.String.add name (SMT.bvterm_of_name 1 name) !bvvars;
            Map.String.find name !bvvars 
          | Some t -> t
        end
        | And (n1, n2) -> SMT.bvand (doit n1) (doit n2)

      in fun n -> doit n
    in 
  
    let form = SMT.bvtobool @@ bvterm_of_node n in 

    let inps = Option.bind inps (fun l -> 
      if List.is_empty l then None
      else Some l
    ) in

    let inps = Option.map (fun inps ->
      List.map (fun (id,sz) -> 
      List.init sz (fun i -> ("BV_" ^ (id |> string_of_int) ^ "_" ^ (Printf.sprintf "%05X" (i))))) inps 
    ) inps in
    let inps = Option.map (fun inps ->
    List.map (List.map (fun name -> match Map.String.find_opt name !bvvars with
    | Some bv -> bv
    | None -> SMT.bvterm_of_name 1 name)) inps) inps
    in
    let bvinp = Option.map (fun inps -> 
      List.map (fun i -> List.reduce (SMT.bvterm_concat) i) inps) inps 
    in

    begin
      SMT.assert' @@ form;
      if SMT.check_sat () = true then 
      begin
        Format.eprintf "Input BVVars: ";
        let () = Enum.iter (Format.eprintf "%s, ") (Map.String.keys !bvvars) in
        Format.eprintf "@.";
        Option.may (fun bvinp -> List.iteri (fun i bv -> 
            Format.eprintf "input[%d]: %a@." i SMT.pp_term (SMT.get_value bv)        
        ) bvinp) bvinp;
        true 
      end
      else false
    end
  
  let circ_taut ?inps (n: Aig.node) : bool =
    not @@ circ_sat ?inps (Aig.neg n)

end


let makeBWZinstance () : (module SMTInstance) = 
  let options = Options.default () in
  Options.set options Produce_models true;
  let bitwuzla = Solver.create options in
  
  (module struct
  type bvterm = Term.t 

  exception SMTError
  
  let bvterm_of_int (sort: int) (v: int) : bvterm =
    mk_bv_value_int (mk_bv_sort sort) v
  
  let bvtobool (bv: bvterm) : bvterm = 
    mk_term2 Kind.Equal bv (mk_bv_one (mk_bv_sort 1))

  let bvterm_of_name (sort: int) (name: string) : bvterm =
    mk_const ~symbol:name (mk_bv_sort sort)

  let assert' (f: bvterm) : unit =
    Solver.assert_formula bitwuzla f

  let check_sat () : bool =
    match Solver.check_sat bitwuzla with
    | Sat -> true
    | Unsat -> false
    | Unknown -> raise SMTError

  let bvterm_equal (bv1: bvterm) (bv2: bvterm) : bvterm =
    mk_term2 Kind.Equal bv1 bv2

  let bvterm_concat (bv1: bvterm) (bv2: bvterm) : bvterm =
    mk_term2 Kind.Bv_concat bv1 bv2

  let bvnot (bv: bvterm) : bvterm =
    mk_term1 Kind.Bv_not bv

  let bvand (bv1: bvterm) (bv2: bvterm) : bvterm =
    mk_term2 Kind.Bv_and bv1 bv2

  let lognot (bv: bvterm) : bvterm =
    mk_term1 Kind.Not bv

  let get_value (bv: bvterm) : bvterm =
    Solver.get_value bitwuzla bv

  let pp_term (fmt: Format.formatter) (bv: bvterm) : unit =
    Term.pp fmt bv

  end : SMTInstance)


let makeBWZinterface () : (module SMTInterface) =
  (module MakeSMTInterface ((val makeBWZinstance () : SMTInstance)))



