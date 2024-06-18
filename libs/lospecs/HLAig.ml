type node = Aig.node
type reg = Aig.reg

type input = string * int
type tdeps = int Set.t Map.String.t
type tbdeps = int Set.t Map.String.t list

module Env : sig
  type env
  
  val id : env -> string -> env * int
  val get : env -> string -> int
  val get_opt : env -> string -> int option
  val get_reverse : env -> int -> string 
  val get_reverse_opt : env -> int -> string option
  val input_of_var : env -> Aig.var -> input
  val var_of_input : env -> input -> Aig.var

end = struct
  type env = {
    forward : (string, int) Map.t;
    reverse : (int, string) Map.t;
  }

  let fresh = 
    let counter = ref 0 in
    fun () -> incr counter; !counter 

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
end

type env = Env.env

(* -------------------------------------------------------------------- *)
(* let rec pp_node (fmt : Format.formatter) (n : node) : unit *)

(* let rec pp_deps (fmt : Format.formatter) (d: deps) : unit *)

(* let rec pp_block_deps (fmt: Format.formatter) (b: bdeps) : unit *)

(* -------------------------------------------------------------------- *)
let input (env: env) ((s,i) : input) =
  let (env, v) = 
    match Env.get_opt env s with
    | Some v -> (env, v)
    | None -> Env.id env s
  in (env, Aig.input (v, i))

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

(* -------------------------------------------------------------------- *)
let maps (env:env) (aenv : input -> node option) : reg -> reg =
  List.map (map env aenv)  

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

let dep (n: node) : (string, int Set.t) Map.t = 
  assert false

let deps (n: reg) : ((string, int Set.t) Map.t) array = 
  assert false

let block_deps (d: ((string, int Set.t) Map.t) array) : (string, int Set.t) Map.t list =
  assert false

(* ==================================================================== *)
let reg (env: env) ~(size : int) ~(name : string) : env * reg =
  let (env, id) = Env.id env name in
  (env, Circuit.reg ~size:size ~name:id)
  

(* -------------------------------------------------------------------- *)
let rec pp_node (env: env) (fmt : Format.formatter) (n : node) =
  match n with
  | { gate = False; id } when 0 < id ->
    Format.fprintf fmt "⊥"

  | { gate = False; } ->
    Format.fprintf fmt "⊤"

  | { gate = Input var; id; } ->
    let (s, i) = Env.input_of_var env var in
    Format.fprintf fmt "%s%s#%0.4x"
      (if 0 < id then "" else "¬") s i

  | { gate = And (n1, n2); id; } when 0 < id ->
    Format.fprintf fmt "(%a) ∧ (%a)" (pp_node env) n1 (pp_node env) n2

  | { gate = And (n1, n2); } ->
    Format.fprintf fmt "¬((%a) ∧ (%a))" (pp_node env) n1 (pp_node env) n2

