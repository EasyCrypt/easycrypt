(* -------------------------------------------------------------------- *)
open EcUtils
open EcBigInt
open EcSymbols
open EcPath
open EcParsetree
open EcEnv
open EcTypes
open EcModules
open Batteries

module C = struct
  include Lospecs.Aig
  include Lospecs.Circuit
  include Lospecs.Circuit_avx2.FromSpec ()
  include Lospecs.Circuit_spec
end

module IdentMap = Lospecs.Ast.IdentMap
module Ident = Lospecs.Ast.Ident

type ident = Ident.ident

module CircEnv : sig
  type env

  val empty : env
  val lookup : env -> symbol -> ident option
  val push : env -> symbol -> env * ident
  val bind : env -> ident -> C.reg -> env
  val get : env -> ident -> C.reg option
  val bind_s : env -> symbol -> C.reg -> env
  val get_s : env -> symbol -> C.reg option
end = struct
  type env = { vars : (symbol, ident) Map.t;
               bindings : C.reg IdentMap.t }
  
  let empty : env = { vars = Map.empty;
                      bindings = IdentMap.empty }
  let lookup (env : env) (x: symbol) = Map.find_opt x env.vars

  let push (env : env) (x : symbol) =
    let idx = Ident.create x in
    let env = { vars = Map.add x idx env.vars ; bindings = env.bindings } in
    (env, idx)

  let bind (env: env) (x : ident) (r : C.reg) =
    let env = { 
      vars = (match Map.find_opt (Ident.name x) env.vars with
              | Some _ -> env.vars
              | None -> Map.add (Ident.name x) x env.vars);
      bindings = IdentMap.add x r env.bindings} in
    env

  let get (env: env) (x: ident) = 
    IdentMap.find_opt x env.bindings

  let bind_s (env: env) (x : symbol) (r : C.reg) =
    match lookup env x with
    | Some idx -> bind env idx r
    | None -> bind env (Ident.create x) r

  let get_s (env: env) (x : symbol) =
    match lookup env x with
    | Some idx -> get env idx
    | None -> failwith ("No variable named " ^ x)
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
  | Op    of symbol * barg list

and barg =
  | Const of width * zint
  | Var   of vsymbol

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


let circuit_from_bstmt (env: cp_env) (((x, w), rhs) : bstmt) : cp_env * C.reg =
  let (env, idx) = CircEnv.push env x
  in let r = 
    (match rhs with
    | Const (w, i)     -> C.of_bigint ~size:w (EcBigInt.to_zt i)
    | Copy  (x, i)     -> C.reg ~size:i ~name:(Ident.id idx)
    | Op    (op, args) -> C.circuit_of_spec (args |> (parse_circ_args (env, idm)) |> Array.of_list) (List.assoc op C.specs))
  in let env = CircEnv.bind idx r env
  in (env, r)

and parse_circ_args (env: cp_env) (args: barg list) : C.reg list =
  List.map 
  (fun arg -> 
    match arg with
    | Const (w, i) -> C.of_bigint ~size:w i
    | Var (x, i) -> 
      (match CircEnv.get_s env x with
      | None -> failwith ("No var named " ^ x)
      | Some r -> r))
  args

let circuit_from_bprgm (prg: bprgm) = 
  List.fold_left_map circuit_from_bstmt (Env.empty, IdentMap.empty) prg
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

  let trans_arg (x : ovariable) =
    (oget ~exn:BDepError x.ov_name, trans_wtype x.ov_type) in

  let trans_local (x : variable) =
    (x.v_name, trans_wtype x.v_type) in

  let _locals =
    (List.map trans_arg proc.f_sig.fs_anames) @
    (List.map trans_local pdef.f_locals) in

  let body : bprgm = List.map trans_instr pdef.f_body.s_node in

  if not (List.is_unique (List.fst body)) then
    raise BDepError;

  (*
   * TODO
   *  1: generator the circuit C from the program `body`
   *  2: compute the dependencies and infer sub-circuits C1...Cn
   *  3: check equivalence between the different boolean functions C1...Cn
   *  4: generate a circuit Pr encoding the pre-condition (partial)
   *  5: generate a circuit Po encoding the post-condition
   *  6: check that (Pri /\ Ci) => Poi by computation
   *)

  Format.eprintf "%a" pp_bprgm body
