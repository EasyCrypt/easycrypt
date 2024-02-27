(* -------------------------------------------------------------------- *)
open EcUtils
open EcBigInt
open EcSymbols
open EcPath
open EcParsetree
open EcEnv
open EcTypes
open EcModules

(* -------------------------------------------------------------------- *)
module Map = Batteries.Map
module Hashtbl = Batteries.Hashtbl
module Set = Batteries.Set

(* -------------------------------------------------------------------- *)
module C = struct
  include Lospecs.Aig
  include Lospecs.Circuit
  include Lospecs.Circuit_avx2.FromSpec ()
  include Lospecs.Circuit_spec
end

(* -------------------------------------------------------------------- *)
module IdentMap = Lospecs.Ast.IdentMap
module Ident = Lospecs.Ast.Ident

type ident = Ident.ident
type deps = ((int * int) * int C.VarRange.t) list

(* -------------------------------------------------------------------- *)
module CircEnv : sig
  type env

  val empty : env
  val lookup : env -> symbol -> ident option
  val lookup_id : env -> int -> ident option
  val push : env -> symbol -> env * ident
  val bind : env -> ident -> C.reg -> env
  val get : env -> ident -> C.reg option
  val bind_s : env -> symbol -> C.reg -> env
  val get_s : env -> symbol -> C.reg option
end = struct
  type env = { vars : (symbol, ident) Map.t;
               bindings : C.reg IdentMap.t;
               ids : (int, ident) Map.t }

(* -------------------------------------------------------------------- *)
  let empty : env = { vars = Map.empty;
                      bindings = IdentMap.empty;
                      ids = Map.empty }

(* -------------------------------------------------------------------- *)
  let lookup (env : env) (x: symbol) = Map.find_opt x env.vars

(* -------------------------------------------------------------------- *)
  let lookup_id (env: env) (i: int) = Map.find_opt i env.ids

(* -------------------------------------------------------------------- *)
  let push (env : env) (x : symbol) =
    let idx = Ident.create x in
    let env = { vars = Map.add x idx env.vars ;
                bindings = env.bindings;
                ids  = Map.add (Ident.id idx) idx env.ids } in
    (env, idx)

(* -------------------------------------------------------------------- *)
  let push_ident (env: env) (idx: ident) : env =
    let (name, id) = (Ident.name idx, Ident.id idx) in
    let env = { vars = Map.add name idx env.vars ;
                bindings = env.bindings;
                ids  = Map.add id idx env.ids } in
    env

(* -------------------------------------------------------------------- *)
  let bind (env: env) (x : ident) (r : C.reg) =
    let env =
      match Map.find_opt (Ident.name x) env.vars with
              | Some _ -> env
              | None -> push_ident env x
    in let env = {
      vars = env.vars;
      ids  = env.ids;
      bindings = IdentMap.add x r env.bindings; }
    in env

(* -------------------------------------------------------------------- *)
  let get (env: env) (x: ident) =
    IdentMap.find_opt x env.bindings

(* -------------------------------------------------------------------- *)
  let bind_s (env: env) (x : symbol) (r : C.reg) =
    match lookup env x with
    | Some idx -> bind env idx r
    | None -> bind env (Ident.create x) r

(* -------------------------------------------------------------------- *)
  let get_s (env: env) (x : symbol) =
    match lookup env x with
    | Some idx -> get env idx
    | None -> None
end

(* -------------------------------------------------------------------- *)
type width = int

type bprgm =
  bstmt list

and bstmt =
  vsymbol * brhs

and vsymbol =
  symbol * width

and brhs =
  | Const of width * zint
  | Copy  of vsymbol
  | Op    of symbol * bargs

and barg =
  | Const of width * zint
  | Var   of vsymbol

and bargs = barg list

type cp_env = CircEnv.env

(* -------------------------------------------------------------------- *)
let pp_barg (fmt : Format.formatter) (b : barg) =
  match b with
  | Const (w, i) ->
     Format.fprintf fmt "%a@%d" EcBigInt.pp_print i w

  | Var (x, w) ->
     Format.fprintf fmt "%s@%d" x w

(* -------------------------------------------------------------------- *)
let pp_brhs (fmt : Format.formatter) (rhs : brhs) =
  match rhs with
  | Const (w, i) ->
     Format.fprintf fmt "%a@%d" EcBigInt.pp_print i w

  | Copy (x, w) ->
     Format.fprintf fmt "%s@%d" x w

  | Op (op, args) ->
     Format.fprintf fmt "%s%a"
       op
       (Format.pp_print_list
          (fun fmt a -> Format.fprintf fmt "@ %a" pp_barg a))
       args

(* -------------------------------------------------------------------- *)
let pp_bstmt (fmt : Format.formatter) (((x, w), rhs) : bstmt) =
  Format.fprintf fmt "%s@%d = %a" x w pp_brhs rhs

(* -------------------------------------------------------------------- *)
let pp_bprgm (fmt : Format.formatter) (bprgm : bprgm) =
  List.iter (Format.fprintf fmt "%a;@." pp_bstmt) bprgm

(* -------------------------------------------------------------------- *)
let register_of_barg (env : cp_env) (arg : barg) : C.reg =
  match arg with
  | Const (w, i) ->
    C.of_bigint ~size:w (EcBigInt.to_zt i)

  | Var (x, i) ->
    Option.get (CircEnv.get_s env x)

(* -------------------------------------------------------------------- *)
let registers_of_bargs (env : cp_env) (args : bargs) : C.reg list =
  List.map (register_of_barg env) args

(* -------------------------------------------------------------------- *)
let circuit_of_bstmt (env : cp_env) (((v, s), rhs) : bstmt) : cp_env * C.reg =
  let (env, idx) = CircEnv.push env v in

  let r =
    match rhs with
    | Const (w, i) ->
      C.of_bigint ~size:w (EcBigInt.to_zt i)

    | Copy (x, w) -> Option.get (CircEnv.get_s env x)

    | Op (op, args) ->
      args |> registers_of_bargs env |> (C.func_from_spec op)
  in

  let env = CircEnv.bind env idx r in

  (env, r)

(* -------------------------------------------------------------------- *)
let circuit_from_bprgm (env: cp_env) (prg : bprgm) =
  List.fold_left_map circuit_of_bstmt env prg

(* -------------------------------------------------------------------- *)
let print_deps ~name (env : cp_env) (r : C.reg)  =
  let deps = C.deps r in

  List.iter (fun ((lo, hi), deps) ->
    let vs =
         Enum.(--) lo hi
      |> Enum.fold (fun vs i ->
           let name = Format.sprintf "%s_%03d" name (i / 256) in
           C.VarRange.push vs (name, i mod 256)
         ) C.VarRange.empty in

    Format.eprintf "%a: %a@."
      (C.VarRange.pp Format.pp_print_string) vs
      (C.VarRange.pp
         (fun fmt i ->
            let name = Ident.name (Option.get (CircEnv.lookup_id env i)) in
            Format.fprintf fmt "%s" name))
      deps
  ) deps

(* -------------------------------------------------------------------- *)
let print_deps_ric (env : cp_env) (r : string) =
  let circ = Option.get (CircEnv.get_s env r) in
  print_deps env circ ~name:r

(* -------------------------------------------------------------------- *)
let circ_dep_split (r : C.reg) : C.reg list =
  let deps = C.deps r in

  List.fold_left_map (fun acc ((lo, hi), _) ->
    swap (List.split_nth (hi - lo + 1) acc)
  ) r deps |> snd

let compare_deps (d1: deps) (d2: deps) : bool =
  List.for_all2 (fun ((lo1, hi1), deps1) ((lo2, hi2), deps2) ->
    (hi1 - lo1 == hi2 - lo2) && 
    (List.for_all2 (fun (_, l1) (_, l2) -> 
      List.for_all2 
        (fun (a1, b1) (a2, b2) -> b1 - a1 == b2 - a2) 
        l1 
        l2) 
      (C.VarRange.contents deps1)
      (C.VarRange.contents deps1)))
    d1
    d2

let rec inputs_of_node (n : C.node) : C.var Set.t =
  let cache : (int, C.var Set.t) Hashtbl.t = Hashtbl.create 0 in
  
  let rec doit (n : C.node) : C.var Set.t =
    match Hashtbl.find_option cache (Int.abs n.id) with
    | None -> let mn = doit_r n.gate in
      Hashtbl.add cache (Int.abs n.id) mn;
      mn
    | Some mn -> 
      mn

  and doit_r (n : C.node_r) = 
    match n with
    | False -> Set.empty
    | Input v -> Set.singleton v
    | And (n1, n2) -> Set.union (doit n1) (doit n2)

  in doit n

let inputs_of_reg (r : C.reg) : C.var Set.t =
  List.fold_left (fun acc x -> Set.union acc (inputs_of_node x)) Set.empty r

let circ_equiv (r1 : C.reg) (r2 : C.reg) : bool = 
  if List.compare_lengths r1 r2 <> 0 then false 
  else 
    let d1 = C.deps r1 in 
    let d2 = C.deps r2 in
    if not (compare_deps d1 d2) then false
    else 
      let inps = List.combine (inputs_of_reg r1 |> Set.to_list) (inputs_of_reg r2 |> Set.to_list) in
      C.equivs inps r1 r2


(* -------------------------------------------------------------------- *)
exception BDepError

(* -------------------------------------------------------------------- *)
let decode_op (p : path) : symbol =
  match EcPath.toqsymbol p with
  | ["Top"; "JWord"; "W16u16"], ("VPSUB_16u16"       as op)
  | ["Top"; "JWord"; "W16u16"], ("VPSRA_16u16"       as op)
  | ["Top"; "JWord"; "W16u16"], ("VPADD_16u16"       as op)
  | ["Top"; "JWord"; "W16u16"], ("VPBROADCAST_16u16" as op)
  | ["Top"; "JWord"; "W16u16"], ("VPMULH_16u16"      as op)

     -> op

  | ["Top"; "JModel_x86"], ("VPMULHRS_16u16" as op)
  | ["Top"; "JModel_x86"], ("VPACKUS_16u16"  as op)
  | ["Top"; "JModel_x86"], ("VPMADDUBSW_256" as op)
  | ["Top"; "JModel_x86"], ("VPERMD"         as op)

     -> op

  | ["Top"; "JWord"; "W256"], "andw" -> "AND_u256"

  | _ ->
     Format.eprintf "%s@." (EcPath.tostring p);
     raise BDepError

(* -------------------------------------------------------------------- *)
let bdep (env : env) (p : pgamepath) : unit =
  let proc = EcTyping.trans_gamepath env p in
  let proc = EcEnv.Fun.by_xpath proc env in
  let pdef = match proc.f_def with FBdef def -> def | _ -> assert false in

  let trans_int (p : path) : width =
    match EcPath.toqsymbol p with
    | (["Top"; "JWord"; "W256"], "of_int") -> 256
    | (["Top"; "JWord"; "W128"], "of_int") -> 128
    | (["Top"; "JWord"; "W64" ], "of_int") ->  64
    | (["Top"; "JWord"; "W32" ], "of_int") ->  32
    | (["Top"; "JWord"; "W16" ], "of_int") ->  16
    | (["Top"; "JWord"; "W8"  ], "of_int") ->   8
    | _ -> raise BDepError in

  let trans_wtype (ty : ty) : width =
    match (EcEnv.Ty.hnorm ty env).ty_node with
    | Tconstr (p, []) -> begin
        match EcPath.toqsymbol p with
        | (["Top"; "JWord"; "W256"], "t") -> 256
        | (["Top"; "JWord"; "W128"], "t") -> 128
        | (["Top"; "JWord"; "W64" ], "t") ->  64
        | (["Top"; "JWord"; "W32" ], "t") ->  32
        | (["Top"; "JWord"; "W16" ], "t") ->  16
        | (["Top"; "JWord"; "W8"  ], "t") ->   8
        | _ -> raise BDepError
      end

    | _ ->
       raise BDepError in

  let trans_arg (e : expr) : barg =
    match e.e_node with
    | Evar (PVloc y) ->
       Var (y, trans_wtype e.e_ty)

    | Eapp ({ e_node = Eop (p, []) }, [{ e_node = Eint i }]) ->
      Const (trans_int p, i)

    | _ ->
       let ppe = EcPrinting.PPEnv.ofenv env in
       Format.eprintf "%a@." (EcPrinting.pp_expr ppe) e;
       raise BDepError

  in

  let rec trans_ret (e : expr) : barg list =
    match e.e_node with
    | Evar (PVloc y) ->
        [Var (y, trans_wtype e.e_ty)]
    | Etuple es ->
        List.fold_left (fun acc x -> List.append (trans_ret x) acc) [] es
    | _ -> failwith "Not valid return type"

  in

  let trans_instr (i : instr) : bstmt =
    match i.i_node with
    | Sasgn (LvVar (PVloc x, xty), e) ->
       let rhs =
         match e.e_node with
         | Evar (PVloc y) ->
            Copy (y, trans_wtype e.e_ty)

         | Eapp ({ e_node = Eop (p, []) }, [{ e_node = Eint i }]) ->
            Const (trans_int p, i)

         | Eapp ({ e_node = Eop (p, []) }, args) ->
            Op (decode_op p, List.map trans_arg args)

         | _ ->
            raise BDepError

       in ((x, trans_wtype xty), rhs)

    | _ -> raise BDepError in

  let trans_arg_ (x : ovariable) =
   (oget ~exn:BDepError x.ov_name, trans_wtype x.ov_type) in

  let trans_local (x : variable) =
    (x.v_name, trans_wtype x.v_type) in

  let arguments = List.map trans_arg_ proc.f_sig.fs_anames in
  let ret_vars = Option.map trans_ret pdef.f_ret |> Option.map List.rev in
  let _locals = List.map trans_local pdef.f_locals in

  let body : bprgm = List.map trans_instr pdef.f_body.s_node in

  if not (List.is_unique (List.fst body)) then
    raise BDepError;

  let cenv = List.fold_left 
    (fun env (s,w) -> 
      let (env, idn) = CircEnv.push env s in
      CircEnv.bind  env idn (C.reg ~size:w ~name:(Ident.id idn)))
    CircEnv.empty arguments in
  let (cenv, circs) = circuit_from_bprgm cenv body in

  (*
   * TODO
   *  1: generator the circuit C from the program `body`
   *  2: compute the dependencies and infer sub-circuits C1...Cn
   *  3: check equivalence between the different boolean functions C1...Cn
   *  4: generate a circuit Pr encoding the pre-condition (partial)
   *  5: generate a circuit Po encoding the post-condition
   *  6: check that (Pri /\ Ci) => Poi by computation
   *)

  Format.eprintf "%a@." pp_bprgm body;

  (*
  print_deps_ric cenv "rp_0_0";
  print_deps_ric cenv "rp_1_0";
  print_deps_ric cenv "rp_2_0";
  print_deps_ric cenv "rp_3_0";*)

  let process (r: symbol) : unit = 
    let rs = Option.get (CircEnv.get_s cenv r) in
    let rs = circ_dep_split rs in
    let () = assert (circ_equiv (List.hd rs) (List.hd (List.tl rs))) in
    let () = assert (List.for_all (circ_equiv (List.hd rs)) (List.tl rs)) in 
    List.iteri (fun i r_ -> print_deps ~name:(r ^ (string_of_int (i*(List.length r_)))) cenv r_) rs

  in match ret_vars with
  | None -> ()
  | Some vs ->
      List.iter process (List.map (fun x -> match x with | Var (v,_) -> v | _ -> failwith "Wrong") vs)
