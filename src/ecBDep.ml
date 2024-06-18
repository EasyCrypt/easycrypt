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

module HL = struct
  include Lospecs.HLAig
end

(* -------------------------------------------------------------------- *)
module IdentMap = Lospecs.Ast.IdentMap
module Ident = Lospecs.Ast.Ident

type ident = Ident.ident
type deps = ((int * int) * int C.VarRange.t) list

(* -------------------------------------------------------------------- *)
module CircEnv : sig
  type env

  val empty     : env
  val lookup    : env -> symbol -> ident option
  val lookup_id : env -> int    -> ident option
  val push      : env -> symbol -> env * ident
  val bind      : env -> ident  -> C.reg -> env
  val get       : env -> ident  -> C.reg option
  val bind_s    : env -> symbol -> C.reg -> env
  val get_s     : env -> symbol -> C.reg option
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
let zpad (n: int) (r: C.reg)  = 
  if List.length r < n then
    List.append r (List.init (n - (List.length r)) (fun _ -> C.false_))
  else r


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

    | Op (op, args) -> try 
            begin
            match op with
            | "OPP_8" -> C.opp (args |> registers_of_bargs env |> List.hd) (* FIXME: Needs to be in spec *)
            | _ ->
              args |> registers_of_bargs env |> (C.func_from_spec op)
            end
    with Not_found -> Format.eprintf "op %s not found@." op; assert false
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


(* FIXME: TEMPORARY DEV FUNCTION, TO BE DELETED *)
let print_deps_alt ~name (r : C.reg)  =
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
            Format.fprintf fmt "%d" i))
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
    (hi1 - lo1 = hi2 - lo2) && 
    (List.for_all2 (fun (_, l1) (_, l2) -> 
      List.for_all2 
        (fun (a1, b1) (a2, b2) -> b1 - a1 = b2 - a2) 
        l1 
        l2) 
      (C.VarRange.contents deps1)
      (C.VarRange.contents deps1)))
    d1
    d2

(* ------------------------------------------------------------------------------- *)
let rec inputs_of_node : _ -> C.var Set.t =
  let cache : (int, C.var Set.t) Hashtbl.t = Hashtbl.create 0 in
  
  let rec doit (n : C.node) : C.var Set.t =
    match Hashtbl.find_option cache (Int.abs n.id) with
    | None ->
      let mn = doit_r n.gate in
      Hashtbl.add cache (Int.abs n.id) mn;
      mn
    | Some mn -> 
      mn

  and doit_r (n : C.node_r) = 
    match n with
    | False -> Set.empty
    | Input v -> Set.singleton v
    | And (n1, n2) -> Set.union (doit n1) (doit n2)

  in fun n -> doit n

(* ------------------------------------------------------------------------------- *)
let inputs_of_reg (r : C.reg) : C.var Set.t =
  List.fold_left (fun acc x -> Set.union acc (inputs_of_node x)) Set.empty r

(* ------------------------------------------------------------------------------- *)
(* this needs cleanup and refactoring 
  Make the translation to SMT more conscious of semantics
  and of definitions on the upper level (variable and such)
*)
let circ_equiv_bitwuzla (hlenv: HL.env) (inps: (C.var * C.var) list) (r1 : C.reg) (r2 : C.reg) (bound : int) : bool =
  let module B = Bitwuzla.Once () in
  let open B in
  let bvvars : B.bv B.term Map.String.t ref = ref Map.String.empty in
  let inps = Map.of_seq (List.to_seq inps) in
  let env_ (v : C.var) = Option.map C.input (Map.find_opt v inps) in
  let r1 = C.maps env_ r1 in

  let rec bvterm_of_node : C.node -> _ =
    let cache = Hashtbl.create 0 in
  
    let rec doit (n : C.node) =
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

    and doit_r (n : C.node_r) = 
      match n with
      | False -> Term.Bv.zero (Sort.bv 1) 
      | Input v -> let name = ("BV_" ^ (HL.Env.get_reverse hlenv (fst v)) ^ "_" ^ (Printf.sprintf "%X" (snd v))) in
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
  
  let bvterm_of_reg (r: C.reg) : _ =
    (* DEBUG PRINT *)
    Format.eprintf "Reg has %d nodes@." (List.length r);
    List.map bvterm_of_node r |> Array.of_list |> Array.rev |> Term.Bv.concat
  in 
  let bvinpt1 = (bvterm_of_reg r1) in
  let bvinpt2 = (bvterm_of_reg r2) in
  let formula = Term.equal bvinpt1 bvinpt2 
  in 
 
  (* FIXME: Mega hardcoding for shift test *)
  let () = Format.eprintf "bvvars has %d entries@." (List.length @@ List.of_enum @@ Map.String.keys !bvvars) in
  let inputs = Map.String.keys !bvvars |> List.of_enum |> Array.of_list in 
  let inputs = Array.rev inputs in 
  (* DEBUG PRINT: *)
  let () = Array.iter (fun v -> Format.eprintf "key: %s@." v) inputs in 
  (*let lsB, msB = Array.take 8 inputs, Array.drop 8 inputs in*)
  let inp_bv = Term.Bv.concat (Array.map (fun v -> Map.String.find v !bvvars) inputs)  
  in

  begin
          if bound > 0 then
             let precond = Term.Bv.ult inp_bv (Term.Bv.of_int (Sort.bv (Array.length inputs)) bound) 
             in assert' @@ Term.Bv.logand precond (Term.Bv.lognot formula);
          else 
             assert' @@ Term.Bv.lognot formula;
    let result = check_sat () in
    if result = Unsat then
    true else
      begin
        Format.eprintf "fc: %a@."     Term.pp (get_value bvinpt1 :> B.bv B.term);
        Format.eprintf "block: %a@."  Term.pp (get_value bvinpt2 :> B.bv B.term);
        Format.eprintf "inp: %a@."    Term.pp (get_value inp_bv :> B.bv B.term);
        false
      end
  end


(* ------------------------------------------------------------------------------- *)
let circ_equiv (hlenv: HL.env) (r1 : C.reg) (r2 : C.reg) ~(bitwuzla: int) : bool = 
  let (r1, r2) = if List.compare_lengths r1 r2 < 0 then
    (zpad (List.length r2) r1, r2) else
    (r1, zpad (List.length r1) r2)
  in

  let d1 = C.deps r1 in 
  let d2 = C.deps r2 in
  if not (compare_deps d1 d2) then false

  else  
    let inp1 = (inputs_of_reg r1 |> Set.to_list) in
    let inp2 = (inputs_of_reg r2 |> Set.to_list) in
    let inps = List.combine (List.take (List.length inp2) inp1) (List.take (List.length inp1) inp2) in
    if bitwuzla >= 0 then 
      let () = Format.eprintf "inp1: @."; List.iter (fun (a,b) -> Format.eprintf "%s.(%d)@." (HL.Env.get_reverse hlenv a) b) inp1 in
      let () = Format.eprintf "inp2: "; List.iter (fun (a,b) -> Format.eprintf "%s.(%d)@." (HL.Env.get_reverse hlenv a) b) inp2 in
      circ_equiv_bitwuzla hlenv inps r1 r2 bitwuzla
    else C.equivs inps r1 r2

let bruteforce (r : C.reg) (vars : C.var list) : unit = 
  let rec doit (acc : bool list) (n : int) : unit =
    match n with
    | 0 -> let eval = ((List.combine vars acc) |> List.to_seq |> Map.of_seq) in
           let eval = C.eval (fun x -> Map.find x eval) in 
           List.map eval r |> C.uint_of_bools |> Format.eprintf "@.@.ERROR: -> %d: %d@." (C.uint_of_bools acc) 
    | n -> doit (false::acc) (n-1); doit (true::acc) (n-1)

  in doit [] (List.length vars)

let bools_of_int (n : int) ~(size: int) : bool list =
  List.init size (fun i -> ((n lsr i) land 1) <> 0) 

let bruteforce_equiv (r1 : C.reg) (r2 : C.reg) (range: int) : bool = 
  
  let (r1, r2) = if List.compare_lengths r1 r2 < 0 then
    (zpad (List.length r2) r1, r2) else
    (r1, zpad (List.length r1) r2)
  in

  let eval (r : C.reg) (n: int) : int =
    let inp = inputs_of_reg r |> Set.to_list in
    let vals = bools_of_int n ~size:(List.length inp) in
    let env = List.combine inp vals |> List.to_seq |> Map.of_seq in
    (*let eval = C.eval (fun x -> Map.find x env) in
    List.map eval r *)
    let res = C.evals (fun x -> Map.find x env) r |> C.uint_of_bools in
    res
  in
  Enum.(--^) 0 range 
    |> Enum.map (fun i -> 
        let res1 = (eval r1 i) in
        let res2 = (eval r2 i) in
        if res1 = res2 then true 
        else (Format.eprintf "i: %d | r1: %d | r2: %d@." i res1 res2; false)) |> Enum.fold (&&) true

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
  | ["Top"; "JWord"; "W4u64" ], ("VPSLL_4u64"      as op)
  | ["Top"; "JWord"; "W4u64" ], ("VPSRL_4u64"      as op)
  | ["Top"; "JWord"; "W2u128"], ("truncateu128"    as op)

     -> op

  | ["Top"; "JModel_x86"], ("VPMULHRS_16u16" as op)
  | ["Top"; "JModel_x86"], ("VPACKUS_16u16"  as op)
  | ["Top"; "JModel_x86"], ("VPMADDUBSW_256" as op)
  | ["Top"; "JModel_x86"], ("VPERMD"         as op)
  | ["Top"; "JModel_x86"], ("VPSLLDQ_256"    as op)
  | ["Top"; "JModel_x86"], ("VPSRLDQ_128"    as op)
  | ["Top"; "JModel_x86"], ("concat_2u128"   as op)
  | ["Top"; "JModel_x86"], ("VEXTRACTI128"  as op)

     -> op

  | ["Top"; "JWord"; "W256"], "andw" -> "AND_u256"
  | ["Top"; "JWord"; "W256"], "+^"   -> "VPXOR_256"
  | ["Top"; "JWord"; "W128"], "+^"   -> "VPXOR_128"
  | ["Top"; "JWord"; "W8"], "[-]"    -> "OPP_8"
  | ["Top"; "JWord"; "W8"], "+"      -> "ADD_8"

  | _ ->
     Format.eprintf "%s@." (EcPath.tostring p);
     raise BDepError



let rec circuit_of_form (hlenv: HL.env) (env: env) (f : EcAst.form) : HL.env * C.reg =
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
        | (["Top"; "Pervasive"], "int") -> 256
(*      DEBUG PRINT V
        | (qs, q) -> List.iter (Format.eprintf "%s ") qs; Format.eprintf "@. %s@." q; raise BDepError*)
        | _ -> raise BDepError
      end

    | _ ->
       raise BDepError in

  let trans_jops (pth: qsymbol) : C.reg list -> C.reg =
    (* TODO: Check if we need regs to be of correct size or not (semi-done) *)
    match pth with
    | (["Top"; "JWord"; "W32"], "to_uint") 
    | (["Top"; "JWord"; "W16"], "to_uint") 
    | (["Top"; "JWord"; "W8"], "to_uint")  -> 
        fun rs -> begin
          match rs with
          | [r] -> zpad 256 r
          | _   -> raise BDepError (* check error type here *)
        end
    | (["Top"; "JWord"; "W32"], "of_int") -> 
        fun rs -> begin
          match rs with
          | [r] -> r |> List.take 32 |> zpad 32
          | _   -> raise BDepError
        end
    | (["Top"; "JWord"; "W16"], "of_int") -> 
        fun rs -> begin
          match rs with
          | [r] -> r |> List.take 16 |> zpad 16
          | _   -> raise BDepError
        end
    | (["Top"; "JWord"; "W8"], "of_int") -> 
        fun rs -> begin
          match rs with
          | [r] -> r |> List.take 8 |> zpad 8
          | _   -> raise BDepError
        end
    | (["Top"; "JWord"; "W32"], "*") 
    | (["Top"; "JWord"; "W16"], "*") -> 
        fun rs -> begin
          match rs with
          | [a; b] -> C.umull a b 
          | _      -> raise BDepError
        end
    | (["Top"; "JWord"; "W32"], "+") 
    | (["Top"; "JWord"; "W16"], "+") -> 
        fun rs -> begin 
          match rs with
          | [a; b] -> C.add a b |> snd
          | _      -> raise BDepError
        end
(*    | (["Top"; "JWord"; "W32"], "[-]") -> This should be subtraction, need to change path FIXME
        fun rs -> begin
          match rs with
          | [a; b] -> C.sub_dropc a b
          | _      -> raise BDepError
        end *)
    | (["Top"; "JWord"; "W256"], "`<<`") 
    | (["Top"; "JWord"; "W32"], "`<<`") 
    | (["Top"; "JWord"; "W16"], "`<<`") -> 
        fun rs -> begin
          match rs with
          | [a; b] -> C.shift ~side:`L ~sign:`L a b 
          | _ -> raise BDepError
        end
    | (["Top"; "JWord"; "W32"], "`>>`")     (*  assuming logical shift right for words   *)
    | (["Top"; "JWord"; "W16"], "`>>`") ->  (* TODO: need to check if this is correct or *)  
        fun rs -> begin                     (* if we need to apply a mask                *) 
          match rs with
          | [a; b] -> C.shift ~side:`R ~sign:`L a b 
          | _      -> raise BDepError
        end
    | (["Top"; "JWord"; "W32"], "`&`") 
    | (["Top"; "JWord"; "W32"], "andw")  
    | (["Top"; "JWord"; "W16"], "`&`") 
    | (["Top"; "JWord"; "W16"], "andw") -> 
        fun rs -> begin
          match rs with
          | [a; b] -> C.land_ a b 
          | _      -> raise BDepError
        end
    | _ -> List.iter (Format.eprintf "%s ") (fst pth);
        Format.eprintf "%s@.Not implemented yet@." (snd pth);
        raise BDepError
  in

  match f.f_node with
  (* hardcoding size for now FIXME *)
  | Fint z -> hlenv, C.of_bigint ~size:256 (EcAst.BI.to_zt z)
  | Fif (c_f, t_f, f_f) -> 
      let hlenv, c_c = circuit_of_form hlenv env c_f in
      let hlenv, t_c = circuit_of_form hlenv env t_f in
      let hlenv, f_c = circuit_of_form hlenv env f_f in
      let () = assert (List.length c_c = 1) in
      let c_c = List.hd c_c in
      hlenv, C.mux2_reg f_c t_c c_c
  (* hardcoding size for now FIXME *)
  | Flocal idn -> 
      HL.reg hlenv ~size:(trans_wtype f.f_ty) ~name:idn.id_symb 
      (* TODO: Check name after *)
  | Fop (pth, _) -> 
    let (pth, pth2) = EcPath.toqsymbol pth in
    let () = List.iter (Format.eprintf "%s ") pth in
    let () = Format.eprintf "@.%s@.------------@." pth2 in
    failwith "No unary yet"

  | Fapp _ -> 
    let (f, fs) = EcCoreFol.destr_app f in
    let hlenv, fs_c = List.fold_left_map (fun hlenv -> circuit_of_form hlenv env) hlenv fs in
    begin match f.f_node with
      | Fop (pth, _) ->
          hlenv, trans_jops (EcPath.toqsymbol pth) fs_c
      | _ -> failwith "Cant apply to non op"
    end 
  | Fquant (_, binds, f) -> 
      (* maybe add bindings to some env here? *)
      circuit_of_form hlenv env f (* FIXME *) 
  | Fproj (f, i) ->
      begin match f.f_node with
      | Ftuple tp ->
        circuit_of_form hlenv env (tp |> List.drop (i-1) |> List.hd)
      | _ -> circuit_of_form hlenv env f 
      (* FIXME^: for testing, to allow easycrypt to ignore flags on Jasmin operators *) 
      end
  | _ -> failwith "Not yet implemented"
    
(* -------------------------------------------------------------------- *)
let bdep (env : env) (p : pgamepath) (f: psymbol) (n : int) (m : int) (vs : string list) (b_bound: int) : unit =
  let proc = EcTyping.trans_gamepath env p in
  let proc = EcEnv.Fun.by_xpath proc env in
  let pdef = match proc.f_def with FBdef def -> def | _ -> assert false in
  let f = EcEnv.Op.lookup ([], f.pl_desc) env |> snd in
  let f = match f.op_kind with
  | OB_oper (Some (OP_Plain (f, _))) -> f
  | _ -> failwith "Invalid operator type" in
  let hlenv, fc = circuit_of_form HL.Env.empty env f in
  (* let () = Format.eprintf "%a" (HL.pp_node hlenv) (List.hd fc) in *)
  (* DEBUG PRINTS FOR OP CIRCUIT *)
  let () = Format.eprintf "len %d @." (List.length fc) in
  let () = inputs_of_reg fc |> Set.to_list |> List.iter (fun x -> Format.eprintf "%d %d@." (fst x) (snd x)) in
  print_deps_alt ~name:"test_out" fc;
 
  (* refactor this maybe? *)
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
        | (["Top"; "Pervasive"], "int") -> 256
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

         | _ -> let () = Format.eprintf "Sasgn error" in
            raise BDepError

       in ((x, trans_wtype xty), rhs)

    | _ -> let () = Format.eprintf "instr_error" in
                raise BDepError in

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

  let (cenv, hlenv) = List.fold_left 
    (fun (env, hlenv) (s,w) -> 
      let (env, idn) = CircEnv.push env s in
      let (hlenv, r) = (HL.reg hlenv ~size:w ~name:(Ident.name idn)) in 
      CircEnv.bind env idn r, hlenv)
    (CircEnv.empty, hlenv) arguments in
  let (cenv, circs) = circuit_from_bprgm cenv body in

(* PRINT PROC PROGRAM BODY *)
  Format.eprintf "%a@." pp_bprgm body; 

(* COMPRESS CIRCUIT FROM SPEC LANGUAGE 
  let comp_circ = C.func_from_spec "COMPRESS" [C.reg ~size:16 ~name:0] in *)
  begin 
    let circ = List.map (fun v -> Option.get (CircEnv.get_s cenv v)) vs |> List.flatten in
    if (n = m) &&  (n = 0) then
      let () = assert (circ_equiv hlenv fc circ ~bitwuzla:b_bound) in
      Format.eprintf "Success@."
    else
      let () = assert (List.length circ <> 0) in
      let () = assert ((List.length circ) mod m = 0) in
      let rec part (l : 'a list) (n : int) : 'a list list = (* assumes above assertion for correctness *)
        match l with
        | [] -> []
        | v -> (List.take n l)::(part (List.drop n l) n) in
      let circs = part circ m in
      (* DEBUG PRINT DEPS FOR PARTITIONED CIRCUITS: *)
      (* let () = *) 
      (* List.iteri (fun i c -> *)
        (* Format.eprintf "@.%d: " i; *)
        (* print_deps ~name:"TEST_" cenv c) circs *)
      (* in *) 
      (* TODO: refactor this? V*)
        let () = assert (List.for_all (fun c ->
        let d = C.deps c in
        List.for_all (fun (_, deps) -> 
          List.for_all (fun (_, l) ->
            List.for_all (fun (a,b) ->
            b - a + 1 = n) l)
          (C.VarRange.contents deps)
        ) d) 
      circs) in
      let () = assert (List.for_all (circ_equiv hlenv (List.hd circs) ~bitwuzla:(-1)) (List.tl circs)) in 
      let () = assert (circ_equiv hlenv fc (List.hd circs) ~bitwuzla:b_bound) in
      Format.eprintf "Success@."
  end 



  (*
   * old_TODO
   *  1: generator the circuit C from the program `body` -> Done
   *  2: compute the dependencies and infer sub-circuits C1...Cn -> Done
   *  3: check equivalence between the different boolean functions C1...Cn -> Done
   *  4: generate a circuit Pr encoding the pre-condition (partial) -> ?
   *  5: generate a circuit Po encoding the post-condition -> ?
   *  6: check that (Pri /\ Ci) => Poi by computation -> ?
   *)

  (* Actual plan:

    Take {rp_0, rp_1, rp_2, rp_3} e.g, flatten it as one bit array
    partition into array of m-bit words 
    these can be computed each from m-bit input words
    by operator f

    Args to bdep: {rp_0, ..., rp_3} as a list
                  n -> input words size
                  m -> output word size
                  f : `W n => `W m -> operator

    Args -> Semi done -> Need to check type still

  1) Circuit from procedure -> done
  2) Flatten array of the variables we want -> Done
  3) Join by each m bits -> Done
  4) Check that each block depends on (exactly) n bits -> Done
  5) Check that circuits are equivalent for each pair of blocks -> Done
  6) Generate circuit for operator -> Done
  7) Check it is equivalent to first block -> Done (bruteforce and SMT)

  *)


