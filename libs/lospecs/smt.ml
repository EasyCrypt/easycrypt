(* ==================================================================== *)
open Aig
open Bitwuzla_cxx

(* ==================================================================== *)
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
  val get_value : bvterm -> bvterm
  val pp_term : Format.formatter -> bvterm -> unit
end

(* ==================================================================== *)
module type SMTInterface = sig
  val circ_equiv : ?inps:(int * int) list -> reg -> reg -> node -> bool
  val circ_sat : ?inps:(int * int) list -> node -> bool
  val circ_taut : ?inps:(int * int) list -> node -> bool
end

(* ==================================================================== *)
(* TODO Add model printing for circ_sat and circ_taut *)
(* Assumes circuit inputs have already been appropriately renamed *)
module MakeSMTInterface (SMT : SMTInstance) : SMTInterface = struct
  (* SMT variable name for bit [bit] of circuit input [id]. *)
  let name_of_var (id : int) (bit : int) : string =
    Printf.sprintf "BV_%d_%05X" id bit

  (* Per-instance translation state, shared across every query on this
     instance. AIG ids are globally hash-consed and stable, and the terms
     below live in this instance's solver, so both maps can persist:
     - the node table memoizes node translation, keyed on the positive id;
     - the variable table holds the size-1 input variables, by name, and
       is read back for model extraction.
     Every input variable is built through a single [bvterm_of_name 1]
     point, so callers never construct names by hand. *)
  module Cache : sig
    type t

    val create : unit -> t

    (* Memoized node translation. *)
    val find_node : t -> int -> SMT.bvterm option
    val add_node : t -> int -> SMT.bvterm -> unit

    (* Size-1 input variable named [name], allocated and memoized on the
       first request. *)
    val var : t -> string -> SMT.bvterm

    (* Same, but a name unseen so far yields a fresh (non-memoized)
       variable — used when reading back a model. *)
    val var_opt : t -> string -> SMT.bvterm

    (* Names of all the variables allocated so far. *)
    val var_names : t -> string list
  end = struct
    type t = {
      nodes : (int, SMT.bvterm) Hashtbl.t;
      mutable vars : SMT.bvterm Map.String.t;
    }

    let create () : t = {nodes = Hashtbl.create 0; vars = Map.String.empty}

    let find_node (c : t) (id : int) : SMT.bvterm option =
      Hashtbl.find_option c.nodes id

    let add_node (c : t) (id : int) (bv : SMT.bvterm) : unit =
      Hashtbl.add c.nodes id bv

    let var (c : t) (name : string) : SMT.bvterm =
      match Map.String.find_opt name c.vars with
      | Some bv -> bv
      | None ->
        let bv = SMT.bvterm_of_name 1 name in
        c.vars <- Map.String.add name bv c.vars;
        bv

    let var_opt (c : t) (name : string) : SMT.bvterm =
      match Map.String.find_opt name c.vars with
      | Some bv -> bv
      | None -> SMT.bvterm_of_name 1 name

    let var_names (c : t) : string list = List.of_enum (Map.String.keys c.vars)
  end

  (* Translate an AIG node to an SMT bitvector term, using [cache] both to
     memoize nodes and to allocate the size-1 input variables. *)
  let bvterm_of_node (cache : Cache.t) : Aig.node -> SMT.bvterm =
    let rec doit (n : Aig.node) =
      let mn =
        match Cache.find_node cache (Int.abs n.id) with
        | None ->
          let mn = doit_r n.gate in
          Cache.add_node cache (Int.abs n.id) mn;
          mn
        | Some mn -> mn
      in
      if 0 < n.id then mn else SMT.bvnot mn
    and doit_r (n : Aig.node_r) =
      match n with
      | False -> SMT.bvterm_of_int 1 0
      | Input v -> Cache.var cache (name_of_var (fst v) (snd v))
      | And (n1, n2) -> SMT.bvand (doit n1) (doit n2)
    in
    doit

  let circ_equiv
      ?(inps : (int * int) list option)
      (r1 : Aig.reg)
      (r2 : Aig.reg)
      (pcond : Aig.node) : bool =
    assert (Array.length r1 = Array.length r2);
    assert (Array.length r1 > 0);
    assert (Array.length r2 > 0);

    let cache = Cache.create () in
    let bvterm_of_node = bvterm_of_node cache in

    let bvterm_of_reg (r : Aig.reg) : _ =
      Array.map bvterm_of_node r
      |> Array.reduce (fun acc b -> SMT.bvterm_concat b acc)
    in

    let bvinpt1 = bvterm_of_reg r1 in
    let bvinpt2 = bvterm_of_reg r2 in
    let formula = SMT.bvterm_equal bvinpt1 bvinpt2 in
    let pcond = bvterm_of_node pcond in
    let inps =
      Option.bind inps (fun l -> if List.is_empty l then None else Some l)
    in

    let inps =
      Option.map
        (fun inps ->
          List.map
            (fun (id, sz) -> List.init sz (fun i -> name_of_var id i))
            inps)
        inps
    in
    let inps =
      Option.map
        (fun inps -> List.map (List.map (Cache.var_opt cache)) inps)
        inps
    in
    let bvinp =
      Option.map
        (fun inps -> List.map (fun i -> List.reduce SMT.bvterm_concat i) inps)
        inps
    in

    begin
      SMT.assert' @@ SMT.bvand pcond (SMT.bvnot formula);
      if SMT.check_sat () = false then true
      else begin
        Format.eprintf "bvout1: %a@." SMT.pp_term (SMT.get_value bvinpt1);
        Format.eprintf "bvout2: %a@." SMT.pp_term (SMT.get_value bvinpt2);
        Format.eprintf "Terms in formula: ";
        List.iter (Format.eprintf "%s ") (Cache.var_names cache);
        Format.eprintf "@\n";
        Option.may
          (fun bvinp ->
            List.iteri
              (fun i bv ->
                Format.eprintf "input[%d]: %a@." i SMT.pp_term
                  (SMT.get_value bv))
              bvinp)
          bvinp;
        false
      end
    end

  (* TODO: better encoding of smt terms ? *)
  let circ_sat ?(inps : (int * int) list option) (n : Aig.node) : bool =
    let cache = Cache.create () in
    let bvterm_of_node = bvterm_of_node cache in

    begin
      match inps with
      | None -> ()
      | Some inps ->
        List.iter
          (fun (id, sz) ->
            List.iter
              (fun i -> ignore (Cache.var cache (name_of_var id i)))
              (List.init sz identity))
          inps
    end;

    let form = bvterm_of_node n in
    let form = SMT.(bvterm_equal form @@ bvterm_of_int 1 1) in

    let inps =
      Option.bind inps (fun l -> if List.is_empty l then None else Some l)
    in

    let inps =
      Option.map
        (fun inps ->
          List.map
            (fun (id, sz) -> List.init sz (fun i -> name_of_var id i))
            inps)
        inps
    in
    let inps =
      Option.map
        (fun inps -> List.map (List.map (Cache.var_opt cache)) inps)
        inps
    in
    let bvinp =
      Option.map
        (fun inps -> List.map (fun i -> List.reduce SMT.bvterm_concat i) inps)
        inps
    in

    begin
      SMT.assert' @@ form;
      if SMT.check_sat () = true then begin
        Format.eprintf "Input BVVars: ";
        List.iter (Format.eprintf "%s, ") (Cache.var_names cache);
        Format.eprintf "@.";
        Option.may
          (fun bvinp ->
            List.iteri
              (fun i bv ->
                Format.eprintf "input[%d]: %a@." i SMT.pp_term
                  (SMT.get_value bv))
              bvinp)
          bvinp;
        true
      end
      else false
    end

  let circ_taut ?inps (n : Aig.node) : bool = not (circ_sat ?inps (Aig.neg n))
end

(* ==================================================================== *)
let makeBWZinstance () : (module SMTInstance) =
  let options = Options.default () in
  Options.set options Produce_models true;

  let bitwuzla = Solver.create options in

  (module struct
    type bvterm = Term.t

    exception SMTError

    let bvterm_of_int (sort : int) (v : int) : bvterm =
      mk_bv_value_int (mk_bv_sort sort) v

    let bvterm_of_name (sort : int) (name : string) : bvterm =
      mk_const (mk_bv_sort sort) ~symbol:name

    let assert' (f : bvterm) : unit = Solver.assert_formula bitwuzla f

    let check_sat () : bool =
      match Solver.check_sat bitwuzla with
      | Sat -> true
      | Unsat -> false
      | Unknown -> raise SMTError

    let bvterm_equal (bv1 : bvterm) (bv2 : bvterm) : bvterm =
      mk_term2 Kind.Equal bv1 bv2

    let bvterm_concat (bv1 : bvterm) (bv2 : bvterm) : bvterm =
      mk_term2 Kind.Bv_concat bv1 bv2

    let bvnot (bv : bvterm) : bvterm = mk_term1 Kind.Bv_not bv

    let bvand (bv1 : bvterm) (bv2 : bvterm) : bvterm =
      mk_term2 Kind.Bv_and bv1 bv2

    let get_value (bv : bvterm) : bvterm = Solver.get_value bitwuzla bv
    let pp_term (fmt : Format.formatter) (bv : bvterm) : unit = Term.pp fmt bv
  end : SMTInstance)

let makeBWZinterface () : (module SMTInterface) =
  (module MakeSMTInterface ((val makeBWZinstance () : SMTInstance)))
