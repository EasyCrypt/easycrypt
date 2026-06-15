(* ==================================================================== *)
open Aig
open Bitwuzla_cxx

(* ==================================================================== *)
module type SMTInstance = sig
  type bvterm

  (* A solver instance: holds the assertion stack and, after a satisfiable
     check, the model. The stateful operations below act on one. *)
  type solver

  exception SMTError

  (* Create a fresh solver (empty assertion stack). *)
  val create_solver : unit -> solver

  (* Expected params: sort, value *)
  val bvterm_of_int : int -> int -> bvterm

  (* Expected params: sort, name *)
  val bvterm_of_name : int -> string -> bvterm

  (* argument must be of size 1, assert it true *)
  (* Affects the solver's assertion stack *)
  val assert' : solver -> bvterm -> unit

  (* Check satisfiability of the solver's current asserts *)
  val check_sat : solver -> bool

  (* equality over bitvectors, res is a size 1 bitvector *)
  val bvterm_equal : bvterm -> bvterm -> bvterm

  (* bvterm concat, res sort is sum of sorts *)
  val bvterm_concat : bvterm -> bvterm -> bvterm

  (* bvnot *)
  val bvnot : bvterm -> bvterm

  (* bvand *)
  val bvand : bvterm -> bvterm -> bvterm

  (* Boolean negation; argument and result are of Boolean sort
     (as produced by [bvterm_equal]). *)
  val bool_not : bvterm -> bvterm

  (* Boolean conjunction; both arguments and the result are of Boolean sort. *)
  val bool_and : bvterm -> bvterm -> bvterm
  val get_value : solver -> bvterm -> bvterm
  val pp_term : Format.formatter -> bvterm -> unit
end

(* ==================================================================== *)
(* A solving context bundles everything one query needs: the backend
   solver together with the per-query memoization tables. It is created
   per query (one solver per query gives assertion isolation) and carried
   explicitly. The queries return the decision; [model] reads the model
   back from the same context, one value per input, and is only meaningful
   after a satisfiable query, before the context's solver is re-used. *)
module type SMTInterface = sig
  type ctx

  val create : unit -> ctx
  val equiv : ctx -> reg -> reg -> node -> bool
  val sat : ctx -> node -> bool
  val valid : ctx -> node -> bool
  val model : ctx -> (int * string) list
end

(* ==================================================================== *)
(* Assumes circuit inputs have already been appropriately renamed *)
module MakeSMTInterface (SMT : SMTInstance) : SMTInterface = struct
  (* SMT variable name for bit [bit] of circuit input [id]. *)
  let name_of_var (id : int) (bit : int) : string =
    Printf.sprintf "BV_%d_%05X" id bit

  (* The explicit per-query state. AIG ids are globally hash-consed and
     stable, and the terms below live in [solver], so the two memo tables
     are valid for the whole life of the context:
     - [nodes] memoizes node translation, keyed on the positive node id;
     - [vars] maps an input bit (id, bit) to its size-1 bitvector, so each
       input bit is built exactly once. *)
  type ctx = {
    solver : SMT.solver;
    nodes : (int, SMT.bvterm) Hashtbl.t;
    vars : (int * int, SMT.bvterm) Hashtbl.t;
  }

  let create () : ctx =
    {
      solver = SMT.create_solver ();
      nodes = Hashtbl.create 0;
      vars = Hashtbl.create 0;
    }

  (* Size-1 variable for bit [bit] of input [id], allocated and memoized
     on the first request. *)
  let var (ctx : ctx) (id : int) (bit : int) : SMT.bvterm =
    match Hashtbl.find_option ctx.vars (id, bit) with
    | Some bv -> bv
    | None ->
      let bv = SMT.bvterm_of_name 1 (name_of_var id bit) in
      Hashtbl.add ctx.vars (id, bit) bv;
      bv

  (* Read back the solver's current model, one value per input. We report
     exactly the input bits the query materialized — the contents of
     [ctx.vars] — so the values are always those of variables the solver
     actually constrained (reading externally-supplied ids could name
     variables absent from the formula, whose model value is an arbitrary
     default). Bits are grouped by input id and concatenated, lowest bit
     last (bit 0 most significant, as in the register encoding). Only
     meaningful right after a satisfiable query, and reads the live solver,
     so it must run before the context's solver is re-used. *)
  let model (ctx : ctx) : (int * string) list =
    Hashtbl.enum ctx.vars |> List.of_enum
    (* group the (id, bit) -> term entries by input id *)
    |> List.group (fun ((id1, _), _) ((id2, _), _) -> Int.compare id1 id2)
    |> List.map (fun bits ->
           let id = fst (fst (List.hd bits)) in
           let bv =
             bits
             |> List.sort (fun ((_, b1), _) ((_, b2), _) -> Int.compare b1 b2)
             |> List.map snd
             |> List.reduce SMT.bvterm_concat
           in
           id, Format.asprintf "%a" SMT.pp_term (SMT.get_value ctx.solver bv))

  (* Translate an AIG node to an SMT bitvector term, memoizing nodes and
     allocating the size-1 input variables in [ctx]. *)
  let bvterm_of_node (ctx : ctx) : Aig.node -> SMT.bvterm =
    let rec doit (n : Aig.node) =
      let mn =
        match Hashtbl.find_option ctx.nodes (Int.abs n.id) with
        | None ->
          let mn = doit_r n.gate in
          Hashtbl.add ctx.nodes (Int.abs n.id) mn;
          mn
        | Some mn -> mn
      in
      if 0 < n.id then mn else SMT.bvnot mn
    and doit_r (n : Aig.node_r) =
      match n with
      | False -> SMT.bvterm_of_int 1 0
      | Input v -> var ctx (fst v) (snd v)
      | And (n1, n2) -> SMT.bvand (doit n1) (doit n2)
    in
    fun (n : Aig.node) -> doit n

  let equiv (ctx : ctx) (r1 : Aig.reg) (r2 : Aig.reg) (pcond : Aig.node) : bool
      =
    assert (Array.length r1 = Array.length r2);
    assert (Array.length r1 > 0);
    assert (Array.length r2 > 0);

    let bvterm_of_node = bvterm_of_node ctx in

    let bvterm_of_reg (r : Aig.reg) : _ =
      Array.map bvterm_of_node r
      |> Array.reduce (fun acc b -> SMT.bvterm_concat b acc)
    in

    let bvinpt1 = bvterm_of_reg r1 in
    let bvinpt2 = bvterm_of_reg r2 in
    let formula = SMT.bvterm_equal bvinpt1 bvinpt2 in
    let pcond = bvterm_of_node pcond in

    (* [pcond] is a 1-bit BV; lift it to Boolean by comparing with #b1.
       [formula] is already Boolean (built via [bvterm_equal]). We look for
       a counter-model: an assignment under which [pcond] holds and the
       registers differ, i.e. [pcond_bool /\ not formula]. *)
    let pcond_bool = SMT.bvterm_equal pcond (SMT.bvterm_of_int 1 1) in
    SMT.assert' ctx.solver (SMT.bool_and pcond_bool (SMT.bool_not formula));
    not (SMT.check_sat ctx.solver)

  let sat (ctx : ctx) (n : Aig.node) : bool =
    let form = bvterm_of_node ctx n in
    let form = SMT.(bvterm_equal form (bvterm_of_int 1 1)) in
    SMT.assert' ctx.solver form;
    SMT.check_sat ctx.solver

  let valid (ctx : ctx) (n : Aig.node) : bool = not (sat ctx (Aig.neg n))
end

(* ==================================================================== *)
(* The Bitwuzla backend. The solver is an explicit value (no longer hidden
   in a closure), so it can be owned by a solving context. *)
module BWZInstance : SMTInstance = struct
  type bvterm = Term.t
  type solver = Solver.t

  exception SMTError

  let create_solver () : solver =
    let options = Options.default () in
    Options.set options Produce_models true;
    Solver.create options

  let bvterm_of_int (sort : int) (v : int) : bvterm =
    mk_bv_value_int (mk_bv_sort sort) v

  let bvterm_of_name (sort : int) (name : string) : bvterm =
    mk_const (mk_bv_sort sort) ~symbol:name

  let assert' (s : solver) (f : bvterm) : unit = Solver.assert_formula s f

  let check_sat (s : solver) : bool =
    match Solver.check_sat s with
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

  let bool_not (bv : bvterm) : bvterm = mk_term1 Kind.Not bv

  let bool_and (bv1 : bvterm) (bv2 : bvterm) : bvterm =
    mk_term2 Kind.And bv1 bv2

  let get_value (s : solver) (bv : bvterm) : bvterm = Solver.get_value s bv
  let pp_term (fmt : Format.formatter) (bv : bvterm) : unit = Term.pp fmt bv
end

module BWZ = MakeSMTInterface (BWZInstance)
