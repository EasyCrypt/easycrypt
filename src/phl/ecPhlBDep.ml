(* -------------------------------------------------------------------- *)
open EcUtils
open EcBigInt
open EcSymbols
open EcPath
open EcParsetree
open EcEnv
open EcTypes
open EcModules
open EcCoreGoal
open EcAst
open EcCoreFol

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
(* Should be merged with usual EcEnv TODO *)
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
  | Op    of path * bargs
  | Nop

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
     Format.fprintf fmt "%a%a"
       EcPrinting.pp_path op
       (Format.pp_print_list
          (fun fmt a -> Format.fprintf fmt "@ %a" pp_barg a))
       args
  | Nop -> ()

(* -------------------------------------------------------------------- *)
let pp_bstmt (fmt : Format.formatter) (((x, w), rhs) : bstmt) =
  Format.fprintf fmt "%s@%d = %a" x w pp_brhs rhs

(* -------------------------------------------------------------------- *)
let pp_bprgm (fmt : Format.formatter) (bprgm : bprgm) =
  List.iter (Format.fprintf fmt "%a;@." pp_bstmt) bprgm

let trans_wtype (env: env) (ty : ty) : width =
  match EcEnv.Circ.lookup_bitstring_size env ty with
  | Some w -> w 
  | None -> Format.eprintf "No size binding for type: %a@."
    (EcPrinting.pp_type (EcPrinting.PPEnv.ofenv env)) ty;
    assert false

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
(* ?? *)
let circ_dep_split (r : C.reg) : C.reg list =
  let deps = C.deps r in

  List.fold_left_map (fun acc ((lo, hi), _) ->
    swap (List.split_nth (hi - lo + 1) acc)
  ) r deps |> snd

(* ------------------------------------------------------------------------------- *)
(* Needs better integration with EC  *)
(* -------------------------------------------------------------------- *)
exception BDepError

(* -------------------------------------------------------------------- *)
let circuit_of_path (env: env) (p : path) : C.reg list -> C.reg  =
  (* | "OPP_8" -> C.opp (args |> registers_of_bargs env |> List.hd) (* FIXME: Needs to be in spec *) *)
  match EcEnv.Circ.lookup_circuit_path env p with
  | Some op -> C.func_from_spec op
  | None -> Format.eprintf "No operator for path: %s@."
    (let a,b = EcPath.toqsymbol p in List.fold_right (fun a b -> a ^ "." ^ b) a b);
    assert false 


(* -------------------------------------------------------------------- *)
let circuit_of_bstmt (env : env) (cenv: cp_env) (((v, s), rhs) : bstmt) : cp_env * C.reg =
  let (cenv, idx) = CircEnv.push cenv v in

  let r =
    match rhs with
    | Const (w, i) ->
      C.of_bigint ~size:w (EcBigInt.to_zt i)

    | Copy (x, w) -> Option.get (CircEnv.get_s cenv x)

    | Op (op, args) -> begin try 
      args |> registers_of_bargs cenv |> circuit_of_path env op 
      with Not_found -> Format.eprintf "op %a not found@." EcPrinting.pp_path op; assert false
      end

    | Nop -> failwith "Nop should have been discarded already"
  in

  let cenv = CircEnv.bind cenv idx r in

  (cenv, r)

(* -------------------------------------------------------------------- *)
let circuit_from_bprgm (env: env) (cenv: cp_env) (prg : bprgm) =
  List.fold_left_map (circuit_of_bstmt env) cenv prg


let rec circuit_of_form (hlenv: HL.env) (env: env) (f : EcAst.form) : HL.env * C.reg =
  let unary (p: path) : C.reg =
  match (EcPath.toqsymbol p) with
  | ["Top"; "Pervasive"], "true" -> [C.true_]
  | q -> Format.eprintf "Non registered unary operator: %s@." (EcSymbols.string_of_qsymbol q); assert false
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
      HL.reg hlenv ~size:(trans_wtype env f.f_ty) ~name:idn.id_symb 
      (* TODO: Check name after *)
  | Fop (pth, _) ->  
    (hlenv, unary pth)

  | Fapp _ -> 
    let (f, fs) = EcCoreFol.destr_app f in
    begin match f.f_node with
      | Fop (pth, _) ->
        begin match (EcPath.toqsymbol pth) with
        | _, "bits" -> begin match fs with
          | a::{f_node=Fint k;_}::{f_node=Fint i; _}::[] -> 
            let k = BI.to_int k in
            let i = BI.to_int i in
            let hlenv, a = circuit_of_form hlenv env a in
            hlenv, a |> List.drop k |> List.take i
          | _ -> failwith "Bits should be called with (word -> int -> int)"
        end
        | _ ->
          let hlenv, fs_c = List.fold_left_map 
            (fun hlenv -> circuit_of_form hlenv env) hlenv fs 
          in hlenv, circuit_of_path env pth fs_c
        end
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
let bdep (env : env) (proc: stmt) (f: psymbol) (invs: variable list) (n : int) (outvs : variable list) (m : int) (pcond: psymbol) : unit =
  let f = EcEnv.Op.lookup ([], f.pl_desc) env |> snd in
  let f = match f.op_kind with
  | OB_oper (Some (OP_Plain (f, _))) -> f
  | _ -> failwith "Invalid operator type" in
  let hlenv, fc = circuit_of_form HL.Env.empty env f in
  (* let fc = List.take 4 fc in (* FIXME: this needs to be removed *) *)
  (* let () = Format.eprintf "%a" (HL.pp_node hlenv) (List.hd fc) in *)
  (* DEBUG PRINTS FOR OP CIRCUIT *)
  let () = Format.eprintf "len %d @." (List.length fc) in
  let () = HL.inputs_of_reg fc |> Set.to_list |> List.iter (fun x -> Format.eprintf "%d %d@." (fst x) (snd x)) in
  let () = Format.eprintf "%a@." HL.pp_deps (HL.deps hlenv fc |> Array.to_list) in

  
  let condition = EcEnv.Op.lookup ([], pcond.pl_desc) env |> snd in
  let condition = match condition.op_kind with
  | OB_oper (Some (OP_Plain (condition, _))) -> condition
  | _ -> failwith "Invalid operator type" in
  let hlenv, condition = circuit_of_form hlenv env condition in
  let () = Format.eprintf "Condition output size: %d@." (List.length condition) in
  let condition = List.hd condition in 
 
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

  let trans_arg (e : expr) : barg =
    match e.e_node with
    | Evar (PVloc y) ->
       Var (y, trans_wtype env e.e_ty)

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
        [Var (y, trans_wtype env e.e_ty)]
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
            Copy (y, trans_wtype env e.e_ty)

         | Eapp ({ e_node = Eop (p, []) }, [{ e_node = Eint i }]) ->
            Const (trans_int p, i)

         | Eapp ({ e_node = Eop (p, []) }, args) ->
            Op (p, List.map trans_arg args)

         | Eop (pth, _) ->
            match (EcPath.toqsymbol pth) with
            | ["Top"; "Pervasive"], "witness" ->
            Format.eprintf "Don't forget to add the safety check (o )(o )@.";
            Nop
            | _ -> let () = Format.eprintf "Sasgn error on : %a@." 
            (EcPrinting.pp_expr (EcPrinting.PPEnv.ofenv env)) e in
            raise BDepError

         | _ -> let () = Format.eprintf "Sasgn error on : %a@." 
            (EcPrinting.pp_expr (EcPrinting.PPEnv.ofenv env)) e in
            raise BDepError

       in ((x, trans_wtype env xty), rhs)

    | _ -> let () = Format.eprintf "instr_error" in
                raise BDepError in

  let arg_of_variable (v : variable) =
   (v.v_name, trans_wtype env v.v_type) in

  let trans_local (x : variable) =
    (x.v_name, trans_wtype env x.v_type) in

  let is_op (b: bstmt) : bool = 
  match b with
  | (_, Nop) -> false
  | _ -> true
  in
  let body : bprgm = List.map trans_instr proc.s_node |> List.filter is_op in

  if not (List.is_unique (List.fst body)) then
    raise BDepError; 

  let arguments = "" in

  let (cenv, hlenv) = List.fold_left 
    (fun (cenv, hlenv) (s,w) -> 
      let (cenv, idn) = CircEnv.push cenv s in
      let (hlenv, r) = (HL.reg hlenv ~size:w ~name:(Ident.name idn)) in 
      CircEnv.bind cenv idn r, hlenv)
    (CircEnv.empty, hlenv) (List.map arg_of_variable invs) in
  let (cenv, circs) = circuit_from_bprgm env cenv body in

(* PRINT PROC PROGRAM BODY *)
  Format.eprintf "%a@." pp_bprgm body; 

(* COMPRESS CIRCUIT FROM SPEC LANGUAGE 
  let comp_circ = C.func_from_spec "COMPRESS" [C.reg ~size:16 ~name:0] in *)
  begin 
    let circ = List.map (fun v -> Option.get (CircEnv.get_s cenv v)) (List.map (fun v -> v.v_name) outvs) |> List.flatten in
    if (n = m) &&  (n = 0) then
      let () = assert (HL.circ_equiv hlenv fc circ) in
      Format.eprintf "Success@."
    else
      let () = assert (List.length circ <> 0) in
      let () = assert ((List.length circ) mod m = 0) in
      let rec part (l : 'a list) (n : int) : 'a list list = (* assumes above assertion for correctness *)
        match l with
        | [] -> []
        | v -> (List.take n l)::(part (List.drop n l) n) in
      let circs = part circ m in
      begin
        Format.eprintf "Proc circuit block sizes: ";
        List.iter (fun a -> Format.eprintf "%d " @@ List.length a) circs;
        Format.eprintf "@.Op circ size: %d@." (List.length fc)
      end;
      (* ADD CHECK THAT CIRCUIT HAS THE CORRECT DEPENDENCY NUMBERS *)
      let () = assert (List.for_all (HL.circ_equiv hlenv (List.hd circs)) (List.tl circs)) in 
      let () = List.iteri (fun i r -> Format.eprintf "Op[%d] deps: %a@." i HL.pp_dep (HL.dep hlenv r)) fc in
      let () = Format.eprintf "Cond deps: %a@." HL.pp_dep (HL.dep hlenv condition)  in
      let () = assert (HL.circ_equiv_bitwuzla hlenv (List.hd circs) fc condition) in
      Format.eprintf "Success@."
  end 


let bdep_xpath (env : env) (p : xpath) (f: psymbol) (n : int) (m : int) (vs : string list) (pcond: psymbol) : unit =
  let trans_arg_ (x : ovariable) =
   (oget ~exn:BDepError x.ov_name, trans_wtype env x.ov_type) 
  in
  let rec trans_ret (e : expr) : barg list =
    match e.e_node with
    | Evar (PVloc y) ->
        [Var (y, trans_wtype env e.e_ty)]
    | Etuple es ->
        List.fold_left (fun acc x -> List.append (trans_ret x) acc) [] es
    | _ -> failwith "Not valid return type"
  in
  let trans_local (x : variable) =
    (x.v_name, trans_wtype env x.v_type) 
  in

  let proc = EcEnv.Fun.by_xpath p env in
  let pdef = match proc.f_def with FBdef def -> def | _ -> assert false in
  let arguments = List.map 
    (fun {ov_name=name; ov_type=ty} -> {v_name= Option.get name; v_type= ty}) 
    (* FIXME: Add better handling for possible error when converting from ovar to var *)
    proc.f_sig.fs_anames 
  in
  let vs = List.map (fun v -> {v_name=v; v_type=tint}) vs in (* FIXME: add actual typing for vs *)
  let _ret_vars = Option.map trans_ret pdef.f_ret |> Option.map List.rev in 
  let _locals = List.map trans_local pdef.f_locals in
  bdep env pdef.f_body f arguments n vs m pcond

(* ----------------------------------------------------------------------- *)
(* FIXME: standardize this, maybe move to common EC lib *)
let op_is_arr_get (p: path) : bool =
  match (EcPath.toqsymbol p) with
  | ["Top"; thr; _], "_.[_]" when String.starts_with thr "Array" -> true
  | _ -> false
  
let op_is_arr_set (p: path) : bool =
  match (EcPath.toqsymbol p) with
  | ["Top"; thr; _], "_.[_<-_]" when String.starts_with thr "Array"  -> true
  | _ -> false

let destruct_array_get (env: env) (f: form) : form * form =
  match f.f_node with 
  | Fapp ({f_node=Fop (p, ty)}, [arr;{f_ty=t_int} as i]) when op_is_arr_get p ->
    arr, i
  | _ -> raise (DestrError "Not an array get")

let destruct_array_set (env: env) (f: form) : form * BI.zint * form =
  match f.f_node with 
  | Fapp ({f_node=Fop (p, ty)}, [arr;{f_node=Fint i; f_ty=t_int}; v]) when op_is_arr_set p ->
    arr, i, v
  | _ -> raise (DestrError "Not an array set (with fixed index)")
  
let destruct_nested_array_set (env: env) (f: form) : form * (BI.zint * form) list = 
  let rec doit acc f =
    try
      let arr, i, v = destruct_array_set env f in
      doit ((i, v)::acc) arr
    with
      | DestrError _ -> f, acc
  in
  let arr, i, v = destruct_array_set env f in
  doit [(i,v)] arr

type init_variant =
| INIT
| MAP

let destruct_array_init (f: form) : form = 
  let p = function
  | _, "init" -> true
  | _ -> false in
  let p pth = p (EcPath.toqsymbol pth) in
  destr_app1 ~name:"init" p f


let destruct_arr_chnk_init (f: form) : form * form * form * init_variant =
  let fn = destruct_array_init f in
  match fn.f_node with
  | Fquant _ -> let binds, fb = destr_lambda fn in
    begin
    match fb.f_node with
    (* map variant *)    
    | Fapp (f, [{f_node=Fapp (chnk, [arr;_i])}]) -> (f, chnk, arr, MAP) 
    (* init variant *)
    | Fapp (f, [{f_node=Fapp (chnk, [arr;_i])}; {f_ty=tint}]) -> (f, chnk, arr, INIT)
    | _ -> failwith "Unsupported form of init body"
    end
  | _ -> failwith "Only lambda init supported"

let chunk_access (env: env) (f: path) (idx: zint) : zint Set.t =
  let o = EcEnv.Op.by_path f env in
  let fb = match o.op_kind with
  | OB_oper (Some (OP_Plain (f, _))) -> f
  | _ -> failwith "Unknown op type"
  in
  let i, fb = match fb.f_node with
  | Fquant (_, [arr; (i, i_ty)], f) -> 
    (i, f)
  | _ -> failwith "Wrong form for chunk"
  in
  let subst = EcSubst.add_flocal EcSubst.empty i (f_int idx) in
  let eval_form = 
    fun f -> (EcReduction.simplify EcReduction.full_red (EcEnv.LDecl.init env []) 
    (EcSubst.subst_form subst f)
    |> destr_int
  ) in
  match fb.f_node with
  | Ftuple fs -> List.fold_left (fun acc i -> 
    let i = (destruct_array_get env i |> snd) in
    let i = eval_form i in
    Set.add i acc) Set.empty fs
  | Fapp _ -> let i = fb in (* FIXME: write better code here *)
    let i = (destruct_array_get env i |> snd) in
    let i = eval_form i in
    Set.singleton i
  | _ -> failwith "Chunk should return tuple"

let const_index_accesses_from_form (env: env) (f: form) : zint Set.t =
  let rec doit (f: form) =
  begin
    let res = try
      let arr, i = destruct_array_get env f in
      let i = destr_int i in
      Set.singleton i
    with 
    | DestrError e when e = "destr_int" ->
      failwith "Non-constant array access"
    | DestrError e -> 
      (* Improve this later *)
      match f.f_node with
      | Fint _ -> Set.empty
      | Fop _ -> Set.empty
      | Fproj (f, _) -> doit f
      | Ftuple args 
      | Fapp (_, args) -> List.fold_left (Set.union) Set.empty (List.map doit args)
      | Fif (cond, ft, ff) -> let ca = doit cond in
        let ta = doit ft in
        let tf = doit ff in
        if (Set.equal ta tf) then Set.union ca ta 
        else begin match (EcReduction.simplify EcReduction.full_red (LDecl.init env []) cond).f_node with
        | Fop (p, _) when p = EcCoreLib.CI_Bool.p_true -> Set.union ca ta
        | Fop (p, _) when p = EcCoreLib.CI_Bool.p_false -> Set.union ca tf
        | _ -> failwith "Non-closed if condition with different array accesses in branches"
        end      
      | _ -> Format.eprintf "%a@." (EcPrinting.pp_form (EcPrinting.PPEnv.ofenv env)) f; 
        failwith "Uncaught case for const idx array access"
    in res
  end 
  in doit f

(* ----------------------------------------------------------------------- *)
let auto_init (env: env) (f: form) =
  let arr_f, init_f = destr_eq f in
  let arr, asgns = try
    destruct_nested_array_set env arr_f
    with
    | DestrError _ -> Format.eprintf "arr: %a@." (EcPrinting.pp_form (EcPrinting.PPEnv.ofenv env)) arr_f;
      raise (DestrError "Not an array on left side") (* FIXME: improve error handling *)
  in 
  let f, chnk, arr, init_var = destruct_arr_chnk_init init_f in
  assert (List.is_unique ~eq:BI.equal (List.fst asgns));
  let chnk, _tys = destr_op chnk in
  (* TODO: Replace above by sort (order-preserving) + unique pass ?*)
  List.iter (fun (i, f) -> 
    let chunk = chunk_access env chnk i in
    let arr = const_index_accesses_from_form env f in
    if not (Set.subset arr chunk) then
    begin
     Format.eprintf "arr accesses: @.";
     Set.iter (Format.eprintf "%s ") (Set.map BI.to_string arr);
     Format.eprintf "chunk accesses: @.";
     Set.iter (Format.eprintf "%s ") (Set.map BI.to_string chunk);
     Format.eprintf "@."
    end;
     assert(Set.subset arr chunk)) asgns;
  let rs_b = destruct_array_init init_f in
  match destr_lambda rs_b with
  | ([(i, i_ty)], rs_f) -> 
  let eval_rs (idx: zint) = 
    let subst = EcSubst.add_flocal (EcSubst.empty) i (f_int idx) in
    EcSubst.subst_form subst rs_f
  in
  List.map (fun (idx, f) -> f_eq f (eval_rs idx)) asgns |> List.fold_left (fun a b -> EcTypesafeFol.f_app_safe env (EcEnv.Op.lookup_path ([], "/\\") env) [a;b]) (f_true)
  | _ -> assert false
  
  
  
  (* Right side checks TODO *)
  (* Array safety checks TODO *)
  
    
let t_bdep (outvs: variable list) (n: int) (inpvs: variable list) (m: int) (op: psymbol) (pcond: psymbol) (tc : tcenv1)=
  (* Run bdep and check that is works FIXME *)
  let () = match (FApi.tc1_goal tc).f_node with
  | FhoareF sH -> bdep_xpath (FApi.tc1_env tc) sH.hf_f op n m (List.map (fun v-> v.v_name) outvs) pcond
  | FhoareS sF -> bdep (FApi.tc1_env tc) sF.hs_s op inpvs n outvs m pcond
  | FcHoareF _ -> assert false
  | FcHoareS _ -> assert false 
  | FbdHoareF _ -> assert false
  | FbdHoareS _ -> assert false 
  | FeHoareF _ -> assert false
  | FeHoareS _ -> assert false 
  | _ -> assert false
  in
  FApi.close (!@ tc) VBdep
  
let process_bdep 
  ((inpvs, n): string list * int) 
  ((outvs, m): string list * int) 
  (op: psymbol) 
  (pcond: psymbol) 
  (tc: tcenv1) 
=

  let env = FApi.tc1_env tc in
  let f_app_safe = EcTypesafeFol.f_app_safe in

  if true then
  begin
  if true then
  let smt = EcBitvector.bitvector_to_smtlib env (FApi.tc1_goal tc) in
  Format.eprintf "%s@." smt; assert false
  else
  let pt = auto_init env (FApi.tc1_goal tc) in
  FApi.t_last (fun tc -> FApi.close (!@ tc) VBdep) (EcLowGoal.t_cut pt tc) 
  end
  else


  (* DEBUG SECTION *)
  let pp_type (fmt: Format.formatter) (ty: ty) = Format.fprintf fmt "%a" (EcPrinting.pp_type (EcPrinting.PPEnv.ofenv env)) ty in
  
  let get_var (v: symbol) (m: memenv) : variable =
    match EcMemory.lookup_me v m with
    | Some (v, None, _) -> v
    | _ -> assert false
  in
  let pop, oop = EcEnv.Op.lookup ([], op.pl_desc) env in
  let ppcond, opcond = EcEnv.Op.lookup ([], pcond.pl_desc) env in
  let inpbty, outbty = tfrom_tfun2 oop.op_ty in
  
  (* TODO: add a typesafe interface to build formulas and refactor this *)
  let w2bits (ty: ty) (arg: form) : form = 
    let tb = match EcEnv.Circ.lookup_bitstring env ty with
    | Some {to_bits=tb; _} -> tb
    | _ -> Format.eprintf "No w2bits for type %a@." (EcPrinting.pp_type (EcPrinting.PPEnv.ofenv env)) ty; assert false
    in EcTypesafeFol.f_app_safe env tb [arg]
    (* in let tbp, tbo = EcEnv.Op.lookup (EcPath.toqsymbol tb) env in *)
    (* f_op tb [] tbo.op_ty *) 
  in
  let bits2w (ty: ty) (arg: form) : form = 
    let fb = match EcEnv.Circ.lookup_bitstring env ty with
    | Some {from_bits=fb; _} -> fb
    | _ -> Format.eprintf "No bits2w for type %a@." (EcPrinting.pp_type (EcPrinting.PPEnv.ofenv env)) ty; assert false
    in EcTypesafeFol.f_app_safe env fb [arg]
    (* in let fbp, fbo = EcEnv.Op.lookup (EcPath.toqsymbol fb) env in *)
    (* f_op fb [] fbo.op_ty *) 
  in
  let w2bits_op (ty: ty) : form = 
    let tb = match EcEnv.Circ.lookup_bitstring env ty with
    | Some {to_bits=tb; _} -> tb
    | _ -> Format.eprintf "No bits2w for type %a@." (EcPrinting.pp_type (EcPrinting.PPEnv.ofenv env)) ty; assert false
    in let tbp, tbo = EcEnv.Op.lookup (EcPath.toqsymbol tb) env in
    f_op tb [] tbo.op_ty 
  in
  let bits2w_op (ty: ty) : form = 
    let fb = match EcEnv.Circ.lookup_bitstring env ty with
    | Some {from_bits=fb; _} -> fb
    | _ -> Format.eprintf "No bits2w for type %a@." (EcPrinting.pp_type (EcPrinting.PPEnv.ofenv env)) ty; assert false
    in let fbp, fbo = EcEnv.Op.lookup (EcPath.toqsymbol fb) env in
    f_op fb [] fbo.op_ty 
  in

  let hr = EcLowPhlGoal.tc1_as_hoareS tc in

  (* ------------------------------------------------------------------ *)
  let outvs = List.map (fun v -> get_var v hr.hs_m) outvs in
  let poutvs = List.map (fun v -> EcFol.f_pvar (pv_loc v.v_name) v.v_type (fst hr.hs_m)) outvs in
  let poutvs = List.map (w2bits (List.hd poutvs).f_ty) poutvs in
  let poutvs = List.rev poutvs in
  let poutvs = List.fold_right (fun v1 v2 -> f_app_safe env EcCoreLib.CI_List.p_cons [v1; v2]) poutvs (fop_empty (List.hd poutvs).f_ty)  in
  let poutvs = f_app_safe env EcCoreLib.CI_List.p_flatten [poutvs] in
  let poutvs = f_app_safe env (EcCoreLib.CI_List.p_chunk) [f_int (BI.of_int m); poutvs] in

  
  let inpvs = List.map (fun v -> get_var v hr.hs_m) inpvs in
  let pinpvs = List.map (fun v -> EcFol.f_pvar (pv_loc v.v_name) v.v_type (fst hr.hs_m)) inpvs in
  let pinpvs = List.map (w2bits (List.hd pinpvs).f_ty) pinpvs in
  let pinpvs = List.rev pinpvs in
  let pinpvs = List.fold_right (fun v1 v2 -> f_app_safe env EcCoreLib.CI_List.p_cons [v1; v2]) (List.rev pinpvs) (fop_empty (List.hd pinpvs).f_ty) in
  let pinpvs = f_app_safe env EcCoreLib.CI_List.p_flatten [pinpvs] in
  let () = Format.eprintf "Type after flatten %a@." pp_type pinpvs.f_ty in
  let pinpvs = f_app_safe env EcCoreLib.CI_List.p_chunk [f_int (BI.of_int n); pinpvs] in
  let () = Format.eprintf "Type after chunk %a@." pp_type pinpvs.f_ty in
  let b2w = (bits2w_op inpbty) in
  let () = Format.eprintf "Type of b2w %a@." pp_type b2w.f_ty in
  let pinpvs =  EcTypesafeFol.f_app_safe env EcCoreLib.CI_List.p_map [b2w; pinpvs] in
  let () = Format.eprintf "Type after first map %a@." pp_type pinpvs.f_ty in
  let pinpvs_post = EcTypesafeFol.f_app_safe env EcCoreLib.CI_List.p_map [(f_op pop [] oop.op_ty); pinpvs] in
  (* A REFACTOR EVERYTHING HERE A *)
  (* ------------------------------------------------------------------ *)
  let post = f_eq pinpvs_post poutvs in
  let pre = EcTypesafeFol.f_app_safe env EcCoreLib.CI_List.p_all [(f_op ppcond [] opcond.op_ty); pinpvs] in

  (* let env, hyps, concl = FApi.tc1_eflat tc in *)
  let tc = EcPhlConseq.t_conseq pre post tc in
  FApi.t_last (t_bdep outvs n inpvs m op pcond) tc 
