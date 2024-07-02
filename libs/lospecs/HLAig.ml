type node = Aig.node
type reg = Aig.reg

type input = string * int
type tdeps = (int, int Set.t) Map.t
type tdblock = (int * tdeps)

module Hashtbl = Batteries.Hashtbl

module Env : sig
  type env

  val id : env -> string -> env * int
  val get : env -> string -> int
  val get_opt : env -> string -> int option
  val get_reverse : env -> int -> string 
  val get_reverse_opt : env -> int -> string option
  val input_of_var : env -> Aig.var -> input
  val var_of_input : env -> input -> Aig.var
  val empty: env
  val namer_of_env : env -> (int -> string)

end = struct
  type env = {
    forward : (string, int) Map.t;
    reverse : (int, string) Map.t;
  }

  let fresh = 
    let counter = ref 0 in
    fun () -> incr counter; !counter 

  let empty = {
      forward = Map.empty;
      reverse = Map.empty;
    }

  let id (env: env) (s: string) =
    match Map.find_opt s env.forward with
    | None ->
      let id = fresh () in
      ({ env with
      forward = Map.add s id env.forward;
      reverse = Map.add id s env.reverse;
      }, id)
    | Some i -> (env, i)

  let get (env: env) (s: string) = 
    match Map.find_opt s env.forward with
    | Some i -> i
    | None -> Format.eprintf "Variable %s not in map@." s; assert false

  let get_opt (env: env) (s: string) = 
    Map.find_opt s env.forward

  let get_reverse (env: env) (i: int) = 
    Map.find i env.reverse

  let get_reverse_opt (env: env) (i: int) = 
    Map.find_opt i env.reverse

  let input_of_var (env: env) ((v, i): Aig.var) =
    (get_reverse env v,i)

  let var_of_input (env: env) ((s, i): input) =
    (get env s, i)

  let namer_of_env (env: env) : int -> string =
    fun i -> get_reverse env i
end

type env = Env.env

(* -------------------------------------------------------------------- *)
let input (env: env) ((s,i) : input) =
  let (env, v) = 
    match Env.get_opt env s with
    | Some v -> (env, v)
    | None -> Env.id env s
  in (env, Aig.input (v, i))

let reg (env: env) ~(size : int) ~(name : string) : env * reg =
  let (env, id) = Env.id env name in
  (env, Circuit.reg ~size:size ~name:id)

(* Checks that variable v does not appear in the circuit  *)
let check_sub (env: env) (v: string) (circ: reg) : bool =
  let rec doit (c: node) : bool = 
    match c.gate with
    | False -> true
    | And (n1, n2) -> (doit n1) && (doit n2)
    | Input (c, i) -> (Env.get_reverse env c) <> v
  in
  List.for_all doit circ

(* ------------------------------------------------------------------------------- *)
(* FIXME: CHECK THIS *)
let rec inputs_of_node : _ -> Aig.var Set.t =
  let cache : (int, Aig.var Set.t) Hashtbl.t = Hashtbl.create 0 in
  
  let rec doit (n : Aig.node) : Aig.var Set.t =
    match Hashtbl.find_option cache (Int.abs n.id) with
    | None ->
      let mn = doit_r n.gate in
      Hashtbl.add cache (Int.abs n.id) mn;
      mn
    | Some mn -> 
      mn

  and doit_r (n : Aig.node_r) = 
    match n with
    | False -> Set.empty
    | Input v -> Set.singleton v
    | And (n1, n2) -> Set.union (doit n1) (doit n2)

  in fun n -> doit n

(* ------------------------------------------------------------------------------- *)
let inputs_of_reg (r : Aig.reg) : Aig.var Set.t =
  List.fold_left (fun acc x -> Set.union acc (inputs_of_node x)) Set.empty r

(* -------------------------------------------------------------------- *)
(* ?? *)
let aenv_of_regs (env: env) (rs : bytes list) = 
  fun inp -> 
  Aig.env_of_regs rs @@ Env.var_of_input env inp

(* ==================================================================== *)
(* check this one *)
let map (env: env) (aenv : input -> node option) : node -> node =
  let _env = fun var ->
    aenv @@ Env.input_of_var env var
  in Aig.map _env 

let rename_input (env: env) (source: string) (target: string) (offset: int) : node -> env * node =
  let cache : (int, node) Hashtbl.t = Hashtbl.create 0 in

  let rec doit (env: env) (n : node) : env * node =
    let env, mn =
      match Hashtbl.find_option cache (abs n.id) with
      | None ->
        let env, mn = doit_r env n.gate in
        Hashtbl.add cache (abs n.id) mn;
        env, mn
      | Some mn ->
        env, mn
    in
      env, if 0 < n.id then mn else Aig.neg mn

  and doit_r (env: env) (n : Aig.node_r) =
    match n with
    | False ->
      (env, Aig.false_)
    | Input ((v, i) as orig) -> begin
      match Env.get_reverse_opt env v with
      | Some n when n = source -> 
        input env (target, i+offset)
      | _ -> (env, Aig.input orig)
      end
    | And (n1, n2) -> 
      let env, n1 = doit env n1 in
      let env, n2 = doit env n2 in
      env, Aig.and_ n1 n2

  in fun (n : node) -> doit env n

let rename_input_s (env: env) (source: string) (target: string) (offset: int): reg -> env * reg =
  fun r -> List.fold_left_map (fun env node -> rename_input env source target offset node) env r

(* -------------------------------------------------------------------- *)
let maps (env:env) (aenv : input -> node option) : reg -> reg =
  fun r -> List.map (map env aenv) r  

(* ==================================================================== *)
let equivs (env: env) (inputs : (input * input) list) (c1 : reg) (c2 : reg) : bool =
  let inputs = List.map (fun (a,b) -> (Env.var_of_input env a, Env.var_of_input env b)) inputs in
  Aig.equivs inputs c1 c2

(* ==================================================================== *)
let eval (env: env) (aenv : input -> bool) =
  let aenv = fun var ->
  aenv @@ Env.input_of_var env var
  in Aig.eval aenv 
   
(* -------------------------------------------------------------------- *)
let evals (env: env) (aenv : input -> bool) = 
  let aenv = fun var ->
  aenv @@ Env.input_of_var env var
  in Aig.evals aenv 

let rec dep : _ -> tdeps = 
  let cache : (int, tdeps) Hashtbl.t = Hashtbl.create 0 in

  let rec doit (n: Aig.node) : tdeps = 
    match Hashtbl.find_option cache (Int.abs n.id) with
    | None -> let mn = doit_r n.gate in
      Hashtbl.add cache (Int.abs n.id) mn;
      mn 
    | Some mn -> 
      mn

  and doit_r (n: Aig.node_r) =
    match n with
    | False -> Map.empty
    | Input (v, i) -> Map.add v (Set.add i (Set.empty)) Map.empty
    | And (n1, n2) -> Map.union_stdlib (fun k s1 s2 -> Some (Set.union s1 s2)) (doit n1) (doit n2)

  in fun n -> doit n

let deps (n: reg) : tdeps array = 
  List.map dep n |> Array.of_list

let block_deps (d: tdeps array) : tdblock list =
  let drop_while_count (f: 'a -> bool) (l: 'a list) : int * ('a list) =
    let rec doit (n: int) (l: 'a list) = 
      match l with
      | [] -> (n, [])
      | a::l' -> if f a then doit (n+1) l' else (n, l)
    in
    let n, tl = doit 0 l in
    (n, tl)
  in
  let rec decompose (l: tdeps list) : tdblock list =
    match l with
    | [] -> []
    | h::_ -> let n, l' = 
      (drop_while_count (fun a -> Map.equal (Set.equal) h a) l) in
      (n, h)::(decompose l')
  in
  decompose (Array.to_list d)

let merge_deps (d1: tdeps) (d2: tdeps) : tdeps = 
    Map.union_stdlib (fun _ a b -> Option.some (Set.union a b)) d1 d2

let split_deps (n: int) (d: tdeps array) : tdblock list =
  assert (Array.length d mod n = 0);
  let combine (d: tdeps list) : tdeps =
    List.reduce merge_deps d
  in
  let rec aggregate (d: tdeps array) : tdblock list =
    (n, combine (Array.head d n |> Array.to_list))::(aggregate (Array.tail d n))
  in
  aggregate d

(* maybe optimize this? *)
let tdblock_of_tdeps (d: tdeps list) : tdblock =
  (List.length d, List.reduce merge_deps d)

(* 
  Take a list of blocks and drop all but the first block if the 
  sizes are the same and the dependecy amounts are the same
*)
let compare_dep_size (a: tdeps) (b: tdeps) : bool =
  (Map.fold (fun s acc -> acc + (Set.cardinal s)) a 0) =
  (Map.fold (fun s acc -> acc + (Set.cardinal s)) b 0)   

let compare_tdblocks ((na, da): tdblock) ((nb, db): tdblock) : bool =
  (na = nb) && compare_dep_size da db

let collapse_blocks (d: tdblock list) : tdblock option = 
  match d with
  | [] -> None
  | h::t -> 
    List.fold_left 
    (fun a b -> 
      match a with
      | None -> None
      | Some a -> if compare_tdblocks a b 
                  then Some a else None) 
    (Some h) t

(* -------------------------------------------------------------------- *)
let rec pp_node ?(namer=string_of_int) (env: env) (fmt : Format.formatter) (n : node) =
  match n with
  | { gate = False; id } when 0 < id ->
    Format.fprintf fmt "⊥"

  | { gate = False; } ->
    Format.fprintf fmt "⊤"

  | { gate = Input (v, i); id; } ->
    let s = namer v in
    Format.fprintf fmt "%s%s#%0.4x"
      (if 0 < id then "" else "¬") s i

  | { gate = And (n1, n2); id; } when 0 < id ->
    Format.fprintf fmt "(%a) ∧ (%a)" (pp_node env) n1 (pp_node env) n2

  | { gate = And (n1, n2); } ->
    Format.fprintf fmt "¬((%a) ∧ (%a))" (pp_node env) n1 (pp_node env) n2

let pp_dep ?(namer = string_of_int) (fmt : Format.formatter) (d: tdeps) : unit =
  let print_set fmt s = Set.iter (Format.fprintf fmt "%d ") s in
  Map.iter (fun id ints -> Format.fprintf fmt "%s: %a@." (namer id) print_set ints) d

let pp_deps ?(namer = string_of_int) (fmt: Format.formatter) (ds: tdeps list) : unit = 
  List.iteri (fun i d -> Format.fprintf fmt "Output #%d:@.%a@." i (pp_dep ~namer) d) ds

let pp_bdep ?(start_index = 0) ?(oname="") ?(namer=string_of_int) (fmt: Format.formatter) ((n, d): tdblock) : unit =
  Format.fprintf fmt "[%d-%d]%s:@." start_index (start_index+n-1) oname;
  pp_dep ~namer fmt d

let pp_bdeps ?(oname="") ?(namer=string_of_int) (fmt: Format.formatter) (bs: tdblock list) : unit =
  List.fold_left (fun acc (n,d) -> (pp_bdep ~start_index:acc ~oname ~namer fmt (n,d)); acc + n) 0 bs |> ignore

(* -------------------------------------------------------------------- *)
let zpad (n: int) (r: Aig.reg)  = 
  if List.length r < n then
    List.append r (List.init (n - (List.length r)) (fun _ -> Aig.false_))
  else r

let single_var_equiv_precheck (env: env) (r1: reg) (r2: reg) : bool =
  let (r1, r2) = if List.compare_lengths r1 r2 < 0 then
    (zpad (List.length r2) r1, r2) else
    (r1, zpad (List.length r1) r2)
  in

  let d1 = deps r1 |> Array.to_list |> tdblock_of_tdeps in 
  let d2 = deps r2 |> Array.to_list |> tdblock_of_tdeps in
  if not (compare_tdblocks d1 d2) 
  then false
  else true 
  (* FIXME: find some better way of doing this *)


let circ_equiv_bitwuzla (r1 : Aig.reg) (r2 : Aig.reg) (pcond : Aig.node) : bool =
  let module B = Bitwuzla.Once () in
  let open B in
  let bvvars : B.bv B.term Map.String.t ref = ref Map.String.empty in
  (* assert (single_var_equiv_precheck env r1 r2); *)
  Format.eprintf "%a@." (fun fmt -> pp_deps fmt) (deps r1 |> Array.to_list);
  Format.eprintf "%a@." (fun fmt -> pp_deps fmt) (deps r2 |> Array.to_list);
  (* let inp1 = inputs_of_reg r1 |> Set.to_list in *)
  (* let inp2 = inputs_of_reg r2 |> Set.to_list in *)
  (* let inps = List.combine (List.take (List.length inp2) inp1) (List.take (List.length inp1) inp2) in *)
  (* let inps = Map.of_seq (List.to_seq inps) in *)
  (* let env_ (v : Aig.var) = Option.map Aig.input (Map.find_opt v inps) in *)
  (* let r1 = (Aig.maps env_ r1) in *)

  let rec bvterm_of_node : Aig.node -> _ =
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
        if 0 < n.id then mn else Term.Bv.lognot mn

    and doit_r (n : Aig.node_r) = 
      match n with
      | False -> Term.Bv.zero (Sort.bv 1) 
      | Input v -> let name = ("BV_" ^ (fst v |> string_of_int) ^ "_" ^ (Printf.sprintf "%X" (snd v))) in
      begin 
        match Map.String.find_opt name !bvvars with
        | None ->
          bvvars := Map.String.add name (Term.const (Sort.bv 1) name) !bvvars;
          Map.String.find name !bvvars 
        | Some t -> t
      end
      | And (n1, n2) -> Term.Bv.logand (doit n1) (doit n2)

    in fun n -> doit n
  in 
  
  let bvterm_of_reg (r: Aig.reg) : _ =
    (* DEBUG PRINT *)
    Format.eprintf "Reg has %d nodes@." (List.length r);
    List.map bvterm_of_node r |> Array.of_list |> Array.rev |> Term.Bv.concat
  in 

  let bvinpt1 = (bvterm_of_reg r1) in
  let bvinpt2 = (bvterm_of_reg r2) in
  let formula = Term.equal bvinpt1 bvinpt2 in
  let pcond = (bvterm_of_node pcond) in
 
  (* FIXME: Mega hardcoding for shift test *)
  (* let () = Format.eprintf "bvvars has %d entries@." (List.length @@ List.of_enum @@ Map.String.keys !bvvars) in *)
  (* let inputs = Array.init bwidth (fun i -> *)
    (* ("BV_" ^ (bvar) ^ "_" ^ (Printf.sprintf "%X" (i+bstart)))) in *)
  (* let inputs = Array.rev inputs in *) 
  (* DEBUG PRINT: *)
  (* let () = Array.iter (fun v -> Format.eprintf "key: %s@." v) inputs in *)
  (* let () = Format.eprintf "BVVARS: "; Enum.iter (Format.eprintf "%s@.") @@ Map.String.keys !bvvars; *)
  (* Format.eprintf "@." *)
  (* in *)
  (* let lsB, msB = Array.head inputs 8, Array.tail inputs 8 in *)
  (* let inp_bv = Term.Bv.concat (Array.map (fun v -> Map.String.find v !bvvars) inputs) in *)

  begin
    (* if bound > 0 then *)
      (* let precond = Term.Bv.ult inp_bv (Term.Bv.of_int (Sort.bv (Array.length inputs)) bound) *) 
      (* in assert' @@ Term.Bv.logand precond (Term.Bv.lognot formula); *)
    (* else *) 
      (* assert' @@ Term.Bv.lognot formula; *)
    assert' @@ Term.Bv.logand pcond (Term.Bv.lognot formula);
    let result = check_sat () in
    if result = Unsat then true 
    else begin
      Format.eprintf "fc: %a@."     Term.pp (get_value bvinpt1 :> B.bv B.term);
      Format.eprintf "block: %a@."  Term.pp (get_value bvinpt2 :> B.bv B.term);
      (* Format.eprintf "inp: %a@."    Term.pp (get_value inp_bv :> B.bv B.term); *)
      false
    end
  end


(* ------------------------------------------------------------------------------- *)
(* Assuming dependence on only one variable for now *)
let circ_equiv (env: env) (r1 : Aig.reg) (r2 : Aig.reg) : bool = 
  (* Format.eprintf "CIRC_EQUIV: @."; *)
  assert (single_var_equiv_precheck env r1 r2);
  (* Format.eprintf "%a@." (pp_deps) (deps env r1 |> Array.to_list); *)
  (* Format.eprintf "%a@." (pp_deps) (deps env r2 |> Array.to_list); *)
  let inp1 = inputs_of_reg r1 |> Set.to_list in
  let inp2 = inputs_of_reg r2 |> Set.to_list in
  let inps = List.combine (List.take (List.length inp2) inp1) (List.take (List.length inp1) inp2) in
  Aig.equivs inps r1 r2

(* let bruteforce (r : Aig.reg) (vars : Aig.var list) : unit = *) 
  (* let rec doit (acc : bool list) (n : int) : unit = *)
    (* match n with *)
    (* | 0 -> let eval = ((List.combine vars acc) |> List.to_seq |> Map.of_seq) in *)
           (* let eval = C.eval (fun x -> Map.find x eval) in *) 
           (* List.map eval r |> C.uint_of_bools |> Format.eprintf "@.@.ERROR: -> %d: %d@." (C.uint_of_bools acc) *) 
    (* | n -> doit (false::acc) (n-1); doit (true::acc) (n-1) *)

  (* in doit [] (List.length vars) *)

(* let bools_of_int (n : int) ~(size: int) : bool list = *)
  (* List.init size (fun i -> ((n lsr i) land 1) <> 0) *) 

(* let bruteforce_equiv (r1 : Aig..reg) (r2 : Aig.reg) (range: int) : bool = *) 
  
  (* let (r1, r2) = if List.compare_lengths r1 r2 < 0 then *)
    (* (zpad (List.length r2) r1, r2) else *)
    (* (r1, zpad (List.length r1) r2) *)
  (* in *)

  (* let. eval (r : Aig.reg) (n: int) : int = *)
    (* let inp = inputs_of_reg r |> Set.to_list in *)
    (* let vals = bools_of_int n ~size:(List.length inp) in *)
    (* let env = List.combine inp vals |> List.to_seq |> Map.of_seq in *)
    (* (*let eval = C.eval (fun x -> Map.find x env) in *)
    (* List.map eval r *) *)
    (* let res = C.evals (fun x -> Map.find x env) r |> C.uint_of_bools in *)
    (* res *)
  (* in *)
  (* Enum.(--^) 0 range *) 
    (* |> Enum.map (fun i -> *) 
        (* let res1 = (eval r1 i) in *)
        (* let res2 = (eval r2 i) in *)
        (* if res1 = res2 then true *) 
        (* else (Format.eprintf "i: %d | r1: %d | r2: %d@." i res1 res2; false)) |> Enum.fold (&&) true *)

