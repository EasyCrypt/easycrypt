(*~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~*)
open EcUtil
open Ast
open AstLogic

(* -------------------------------------------------------------------- *)
module TyVarsMap : sig
  type t

  val create  : ?frozen:bool -> ?bindings:((string * tvar) list) -> unit -> t
  val frozen  : t -> bool
  val freeze  : t -> bool -> unit
  val bind    : t -> pos -> string -> tvar
  val iter    : t -> (string -> tvar -> unit) -> unit
  val collect : t -> (string -> tvar -> 'a) -> 'a list
  val tvars   : t -> tvar list
  val all     : t -> (string -> tvar -> bool) -> bool
end = struct
  type t = {
    mutable tmap_map    : tvar StringMap.t;
    mutable tmap_frozen : bool;
  }

  let frozen (map : t) =
    map.tmap_frozen

  let freeze (map : t) (flag : bool) =
    map.tmap_frozen <- flag

  let create ?(frozen = false) ?(bindings = []) () : t =
    let bindings =
      List.fold_left
        (fun map (x, tvar) -> StringMap.add x tvar map)
        StringMap.empty
        bindings
    in
      { tmap_map    = bindings;
        tmap_frozen = frozen; }

  let bind (map : t) (pos : pos) (x : string) =
    try  StringMap.find x map.tmap_map
    with Not_found ->
      if map.tmap_frozen then
        pos_error pos "unknown type variable %s" x;
      let tvar = EcTerm.mk_tvar x pos in
        tvar.tv_def <- Closed;
        map.tmap_map <- StringMap.add x tvar map.tmap_map;
        tvar

  let iter (map : t) (f : string -> tvar -> unit) =
    StringMap.iter f map.tmap_map

  let collect (map : t) (f : string -> tvar -> 'a) =
    StringMap.fold
      (fun x tvar bds -> (f x tvar) :: bds) map.tmap_map []

  let tvars (map : t) =
    collect map (fun _ tvar -> tvar)

  exception AllFailure

  let all (map : t) (test : string -> tvar -> bool) =
    let realtest x tvar =
      if not (test x tvar) then raise AllFailure
    in
      try  iter map realtest; true
      with AllFailure -> false
end

(* -------------------------------------------------------------------- *)
type scope
type environment

(*~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~*)
(** {2 Expressions } *)

(* let mk_tvar pos = EcTerm.mk_tvar "'a" pos *)

(** Catch OpNotFound and
    * @raise PosError with appropriate message.
    * *)
let catch_op_not_found pos = function
  | Global.OpNotFound (opname, type_list) ->
    pos_error pos "couldn't find op %s (%a)"
      opname (pp_list ~sep:", " PpAst.pp_type_exp) type_list
  | e -> raise e

let get_op pos opname type_list =
  try Global.find_op pos opname type_list
  with e -> catch_op_not_found pos e

let mk_binop pos opname (e1, t1) (e2, t2) =
  let (op, type_res) = get_op pos opname [t1; t2] in
  (Eapp (op, [e1; e2]), type_res)

let mk_binop pos opname e1 e2 =
  if opname = "<>" then
    try
      let e,t = mk_binop pos "=" e1 e2 in
      Eapp(Global.bool_not, [e]), t
    with _ -> mk_binop pos opname e1 e2
  else mk_binop pos opname e1 e2
      



let mk_cnst _pos = function
  | Ebool b -> (Ecnst (Ebool b), Tbool)
  | Eint i -> (Ecnst (Eint i), Tint)
  | Ecst () -> bug "[Typing] mk_cnst"


let mk_const name =
  let c = Global.find_cst name in
  let poly, t = 
    if c.c_poly = [] then [], c.c_type 
    else 
      let poly = 
        List.map (fun tv -> EcTerm.mk_tvar tv.tv_name tv.tv_pos) c.c_poly in
      let subst = List.map2 (fun tv v-> tv, Tvar v) c.c_poly poly in
      poly, EcTerm.subst_tvar subst c.c_type in
  Ecnst (Ecst (c,poly)), t

let raise_mk_const (pos, s) =
  try mk_const s
  with _ -> pos_error pos "the ident %s is not a constant" s


let raise_cnst_var_exp venv (pos, s) =
  try
    let v = Global.find_var venv s in
    Ebase v, v.v_type
  with _ -> try mk_const s
    with _ -> 
      pos_error pos "the ident %s is not a constant or a variable" s

let raise_cnst_lvar_exp lvenv (pos, s) =
  try let v = Global.find_lvar lvenv s in
      Ebase v, Fol.lv_type v
  with _ -> try mk_const s
    with _ -> 
      pos_error pos "the ident %s is not a constant nor a program variable" s


let raise_cnst_var2lvar_exp venv side (pos, s) =
  try mk_const s
  with _ ->
    try let v = Global.find_var venv s in
        Ebase (Fol.lvar_of_var v side), v.v_type
    with _ ->
      pos_error pos "the ident %s is not a constant or a variable" s

let mk_var venv n ((pos, _) as x) = match n with
  | 0 ->
    begin match venv with
      | None -> raise_mk_const x
      | Some venv -> raise_cnst_var_exp venv x
    end
  | 1 | 2 -> pos_error pos "relational position not allowed here"
  | _ -> bug "relational position should have been checked before"

let mk_lvar (lvenv, venv12) n ((pos, _) as x) = match n with
  | 0 -> raise_cnst_lvar_exp lvenv x
  | 1 | 2 ->
    begin match venv12 with
      | None -> pos_error pos "relational position not allowed here"
      | Some (venv1, venv2) ->
        try raise_cnst_lvar_exp lvenv x
        with _ ->
          let side, env =
            if n = 1 then Fol.FVleft, venv1 else Fol.FVright, venv2
          in raise_cnst_var2lvar_exp env side x
    end
  | _ -> bug "relational position should have been checked before"

let mk_no_var _ _n x = raise_mk_const x

let mk_no_random _f pos _r =
  pos_error pos "random expression not allowed here"

let rec mk_g_exp env add_var mk_pr mk_var random (pos, e) =
  let aux = mk_g_exp env add_var mk_pr mk_var random in
  match e with
    | Ecnst c -> mk_cnst pos c
    | Ebase (AstYacc.Eident s) -> mk_var env 0 (pos, s)
    | Ebase (AstYacc.Ebinop (opname, e1, e2)) ->
        mk_binop pos opname (aux e1) (aux e2)
    | Ebase (AstYacc.Eat (e, i)) ->
        if 1 <= i && i <= 2 then
          let mk_var_at env n x = 
            if n = 0 then mk_var env i x else mk_var env n x in
          mk_g_exp env add_var mk_pr mk_var_at random e
        else pos_error pos "relational position should be 1 or 2"
    | Ebase (AstYacc.Epr (qfn, e)) -> mk_pr pos qfn e
    | Ebase (AstYacc.Elist l) -> 
        List.fold_right 
          (fun pe l -> mk_binop (fst pe) (get_tk_name TK_CONS) (aux pe) l) 
          l (raise_mk_const (pos, "[]"))
    | Elet (xs,e1,e2) ->
        let e1',t1 = aux e1 in
        let env, vars = 
          match xs with
          | [] -> 
              bug 
                "EcTyping.mk_exp : found a let expression without binding variable"
          | [x] ->
              let env, v = add_var env x t1 in
              env,[v]
          | _ ->
              let lt =
                try EcTerm.get_tuple t1 
                with Not_found ->
                  pos_error (fst e1) "a tuple with %i arguments is expected"
                    (List.length xs) in
              if List.length lt <> List.length xs then
                pos_error pos "a pattern with %i arguments is expected"
                  (List.length lt);
              let env, vars = 
                List.fold_left2
                  (fun (env,vars) x t ->
                    let env, v = add_var env x t in
                    env, v::vars) (env, []) xs lt in
              env, List.rev vars 
        in
        let e2',t2 = mk_g_exp env add_var mk_pr mk_var random e2 in
        Elet(vars, e1', e2'), t2
    | Ebase (AstYacc.Eforall _) ->
        pos_error pos "quantificators not allowed in expression"
    | Ebase(AstYacc.Eexists _) ->
        pos_error pos "existantial not allowed in expression"
    | Ebase(AstYacc.Eeqvar _) ->
        pos_error pos "equality of a set of variables not allowed in expression"
    | Ernd r -> random aux pos r
    | Epair l ->
      let le, lt = List.split (List.map aux l) in
      (Epair le, Ttuple lt)
    | Eapp (opname, args) ->
      begin
        let args', arg_types = List.split (List.map aux args) in
        try
          let _ = Global.find_op ~prob:true pos opname arg_types in
          random aux pos (Rapp(opname,args))
        with Global.OpNotFound _ ->
          begin
            let (op, type_res) = Global.find_op pos opname arg_types in
            (* can raise Global.OpNotFound _ : catched to process call *)
            (Eapp (op, args'), type_res)
          end
      end
    | Eif (c, e1, e2) ->
      let b, tb = aux c in
      let msg =
        "guards in conditional expression must be of type 'bool'"
      in Unification.raise_unify_type tb Tbool (fst c) msg;
      let e1, t1 = aux e1 in
      let e2, t2 = aux e2 in
      let msg =
        "both branches in the conditional expression must have the same type"
      in Unification.raise_unify_type t1 t2 pos msg;
      (Eif (b, e1, e2), t1)

let rec mk_random mk_rec pos r =
  let r, r_type =
    match r with
      | Rinter (ev1, ev2) ->
        let msg = "non-integer bounds in random interval" in
        let e1, t1 = mk_rec ev1 in
        let e2, t2 = mk_rec ev2 in
        Unification.raise_unify_type t1 Tint (fst ev1) msg;
        Unification.raise_unify_type t2 Tint (fst ev2) msg;
        Rinter (e1, e2), Tint
      | Rbool -> Rbool, Tbool
      | Rbitstr e ->
        let msg = "bitstring length must be an int" in
        let c, t = mk_rec e in
        Unification.raise_unify_type t Tint (fst e) msg;
        Rbitstr c, Tbitstring c
      | Rexcepted (r1, e) ->
          let msg = "type mismatch in random expression" in
          begin
            match mk_random mk_rec pos r1 with
            | (Ernd r2, t) ->
                if not (EcTerm.is_uniform r2) then
                  pos_error pos "the distribution %a should be uniform" 
                    PpAst.pp_random r2;
                let l, tl = mk_rec e in
                let lty = Global.find_type "list" pos in
                let lty = Tnamed { lty with t_poly = [t] } in
                Unification.raise_unify_type tl lty (fst e) msg;
                Rexcepted (r2, l), EcTerm.type_of_random r2
            | _ -> assert false
          end 
      | Rapp (opname,args) ->
        let args, arg_types = List.split (List.map mk_rec args) in
        let (op, type_res) = Global.find_op ~prob:true pos opname arg_types in
        Rapp ( op, args), type_res
  in (Ernd r, r_type)

let mk_no_pr pos _ _ =
  pos_error pos "probabilistic expression not allowed here"

let add_var env (pos,x) t = 
  let env = match env with Some e -> e | None -> Global.empty_venv () in
  let env, v = Global.add_var env pos x t in
  Some env, v

let mk_cst_exp ((pos, _) as pe) =
  try mk_g_exp None add_var  mk_no_pr mk_var mk_no_random pe
  with ex -> catch_op_not_found pos ex

let mk_var_exp venv ((pos, _) as pe) =
  try mk_g_exp (Some venv) add_var mk_no_pr mk_var mk_no_random pe
  with ex -> catch_op_not_found pos ex

let mk_rnd_exp_maybe_call venv pe =
  mk_g_exp (Some venv) add_var mk_no_pr mk_var mk_random pe

let mk_rnd_exp venv ((pos, _) as pe) =
  try mk_rnd_exp_maybe_call venv pe
  with ex -> catch_op_not_found pos ex

let add_lvar (lvenv, lvenvs) (_,x) t =
  let lvenv,lv = Global.add_lvar lvenv x t in
  (lvenv, lvenvs), lv

let mk_lvar_exp lvenv ((pos, _) as pe)  =
  try mk_g_exp (lvenv, None) add_lvar mk_no_pr mk_lvar mk_no_random pe
  with ex -> catch_op_not_found pos ex

let mk_var2_exp lvenv venv1 venv2 ((pos, _) as pe)  =
  try 
    mk_g_exp (lvenv,(Some(venv1,venv2))) add_lvar 
      mk_no_pr mk_lvar mk_no_random pe
  with ex -> catch_op_not_found pos ex

let mk_cst_def poly t ((pos, _) as def) =
  assert (List.for_all (fun tv -> tv.tv_def = Closed) poly);
  let def, tdef = mk_cst_exp def in
  let msg = "constant definition must be of the same type than the constant" in
  Unification.raise_unify_type t tdef pos msg;
  def

(*~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~*)
(** {2 Types} *)

let rec g_mk_type_exp (tvars : TyVarsMap.t option) (pos : pos) texp =
  match texp with
    | AstYacc.Tbase name -> 
        begin 
          try Global.find_primitive_type name 
          with Not_found ->
            let tn = Global.find_type name pos in
            let nargs = List.length tn.t_poly in
            if nargs = 0 then Tnamed tn
            else
              pos_error pos "the type %s except %i argument%s"
                name nargs (if nargs = 1 then "" else "s")
        end
    | AstYacc.Tvar id -> begin
        match tvars with
          | None -> bug "EcTyping.g_mk_type_exp: no poly allowed"
          | Some tvars -> Tvar (TyVarsMap.bind tvars pos id)
      end
    | AstYacc.Tbitstring e ->
        let c, t = mk_cst_exp e in
        let int_msg = "bitstring size must be of type 'int'" in
        Unification.raise_unify_type t Tint (fst e) int_msg;
        Global.add_bitstring c;
        Tbitstring c
    | AstYacc.Tpair l -> 
      ignore (EcWhy3.add_tuple (List.length l));
      Ttuple (List.map (g_mk_type_exp tvars pos) l)
    | AstYacc.Tapp (args,name) ->
        let tn = Global.find_type name pos in
        let nargs = List.length args in
        if nargs = 0 then bug "EcTyping.g_mk_type_exp : nargs = 0";
        let expected = List.length tn.t_poly in
        if nargs = expected then
          let args = List.map (g_mk_type_exp tvars pos) args in
          let subst = List.map2 (fun tv t ->
            match tv with
            | Tvar v -> (v,t)
            | _ -> 
                bug "EcTyping.g_mk_type_exp: t_poly without Tvar") tn.t_poly args 
          in
          let body = 
            match tn.t_def with
            | None -> None
            | Some t -> Some (EcTerm.subst_tvar subst t) in
          Tnamed { tn with t_poly = args; t_def = body }
        else 
          pos_error pos
            "the type %s except %i argument%s, here it is applied to %i argument%s"
            name expected (if expected <= 1  then "" else "s")
            nargs (if nargs <= 1 then "" else "s")

let rec check_unicity pos args =
  match args with
  | [] -> ()
  | a::l -> 
      if List.mem a l then 
        pos_error pos "the polymorphic arguments should be disjoint : %s" a;
      check_unicity pos l
  
let mk_type_def pos args name def =
  check_unicity pos args;
  let tvars = List.map (fun x -> (x, EcTerm.mk_tvar x pos)) args in
  let def = 
    match def with
    | None -> None
    | Some texp ->
      let tvarsmap =
        TyVarsMap.create ~frozen:true ~bindings:tvars ()
      in
        Some (g_mk_type_exp (Some tvarsmap) pos texp)
  in
    EcTerm.mk_tdef
      name pos
      (List.map (fun (_, tvar) -> Tvar tvar) tvars)
      def

(* -------------------------------------------------------------------- *)
let mk_poly_type_exp pos typ =
  let tvars = TyVarsMap.create () in
  let t = g_mk_type_exp (Some tvars) pos typ in
    (TyVarsMap.tvars tvars, t)

let check_poly_list =
  let test (_, t) =
    match t with Tvar t when t.tv_def = Closed -> true | _ -> false in
  List.for_all test 

let mk_op_sig pos (t_params,t_res) =
  let tvars = TyVarsMap.create () in
  let t_params = List.map (g_mk_type_exp (Some tvars) pos) t_params in
  let t_res = g_mk_type_exp (Some tvars) pos t_res in
  assert (TyVarsMap.all tvars (fun _ tv -> tv.tv_def = Closed));
  t_params, t_res

let add_local venv v_pos name t =
  let venv, v = Global.add_var venv v_pos name t in
  debug db_add_loc "[typing] add local: %a" PpAst.pp_var_decl_d v;
  venv, v

let mk_op_def _pos params body =
  let tvars = TyVarsMap.create () in
  let mk_type_exp = g_mk_type_exp (Some tvars) in
  let do_param (venv, params) ((pos, name), t) =
    let venv, v = add_local venv pos name (mk_type_exp pos t) in
    venv, v::params
  in
  let venv, rparams =
    List.fold_left do_param (Global.empty_venv (), []) params in
  let body, t_res = mk_var_exp venv body in
  let params = List.rev rparams in
  let op_sig = List.map (fun v -> v.v_type) params, t_res in
  assert (TyVarsMap.all tvars (fun _ tv -> tv.tv_def = Closed));
  op_sig, (params, body)

let mk_pop_def (_pos:EcUtil.pos) (params:AstYacc.param_list) ((param:AstYacc.p_var),t) body =
  let tvars = TyVarsMap.create () in
  let mk_type_exp = g_mk_type_exp (Some tvars) in
  let do_param (venv, params) ((pos, name), t) =
    let venv, v = add_local venv pos name (mk_type_exp pos t) in
    venv, v::params
  in
  let venv, rparams =
    List.fold_left do_param (Global.empty_venv (), []) params in
  let venv, param = match do_param (venv,[]) (param,t) with 
    | venv, [param] -> venv, param 
    | _ -> assert false in 
  let body, t_res = mk_var_exp venv body in
  assert (TyVarsMap.all tvars (fun _ tv -> tv.tv_def = Closed));
  let params = List.rev rparams in
  let msg = "Expression must have type real" in
  Unification.raise_unify_type t_res Ast.Treal EcUtil.dummy_pos msg;
  let params = param :: params in
  let op_sig = List.map (fun v -> v.v_type) params, t_res in
  op_sig, (params, body)

let mk_type_exp = 
  g_mk_type_exp None

(*~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~*)
(** {2 Instructions} *)

let mk_asgn_rval venv (lval, lval_type) ((pos, e) as rval) =
  let msg = "assigned expression must have the same type as the variable" in
  try
    let e, t = mk_rnd_exp_maybe_call venv rval in
    Unification.raise_unify_type lval_type t pos msg;
    Sasgn (lval, e)
  with Global.OpNotFound (opname, type_list) as ex ->
    let fct, args =
      match e with
        | Eapp (name, args) ->
          let fct =
            try Global.find_fct name
            with Not_found ->
              pos_error pos "couldn't find op or function %s (%a)"
                opname (pp_list ~sep:", " PpAst.pp_type_exp) type_list in
          let msg = "wrong type in call argument" in
          let check_arg arg t_param =
            let e, t = mk_rnd_exp venv arg in
            Unification.raise_unify_type t t_param.v_type (fst arg) msg;
            e in
          if List.length args <> List.length fct.f_param then
            pos_error pos "bad number of arguments";
          let args = List.map2 check_arg args fct.f_param in
          fct, args
        | _ -> catch_op_not_found pos ex in
    Unification.raise_unify_type lval_type fct.f_res.v_type pos msg;
    Scall (lval, fct, args)

let find_var venv (pos,v) =
  try Global.find_var venv v 
  with _ -> pos_error pos "unknow variable %s" v
    
let mk_lval venv l =
  match l with
  | Ltuple lv ->
      let lv, t =
        match lv with
        | [] -> [], Tunit
        | [v] -> let v = find_var venv v in [v], v.v_type
        | l -> 
            let lv = List.map (find_var venv) l in
            let lt = List.map (fun v -> v.v_type) lv in
            lv, Ttuple lt
      in Ltuple lv, t
  | Lupd (v, pe) ->
      let pos = fst v in
      let v = find_var venv v in
      let tk, tv =
        let l = 
          try EcTerm.get_named_type "map" v.v_type 
          with Not_found ->
            pos_error pos "variable %s should be a map" v.v_name in
        match l with
        | [tk;tv] -> tk, tv
        | _ -> assert false in
      let e, te = mk_rnd_exp venv pe in
      Unification.raise_unify_type te tk (fst pe) "invalid index in map access";
      Lupd (v, e), tv
 
let rec mk_instr venv ((pos, i):AstYacc.p_instr) =
  match i with
    | Sasgn (lv, rv) ->
      let lv = mk_lval venv lv in
      mk_asgn_rval venv lv rv
    | Scall (lv, name, args) ->
      let lv = mk_lval venv lv in
      let rv = (pos, Eapp (snd name, args)) in
      mk_asgn_rval venv lv rv
    | Sif (c, bt, bf) ->
      let b, t = mk_var_exp venv c in
      let msg = "If condition is expected to have 'bool' type" in
      Unification.raise_unify_type t Tbool (fst c) msg;
      let bt = mk_stmt venv bt in
      let bf = mk_stmt venv bf in
      Sif (b, bt, bf)
    | Swhile (c, body) ->
      let b, t = mk_var_exp venv c in
      let msg = "While guard is expected to have 'bool' type" in
      Unification.raise_unify_type t Tbool (fst c) msg;
      let body = mk_stmt venv body in
      Swhile (b, body)
    | Sassert c ->
      let b, t = mk_var_exp venv c in
      let msg = "assert condition is expected to have 'bool' type" in
      Unification.raise_unify_type t Tbool (fst c) msg;
      Sassert b

and mk_stmt venv stmt = List.map (mk_instr venv) stmt

(*~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~*)
(** {2 Functions} *)


let rec mk_local_init v (init, t) =
  let msg = "initialisation must have the same type than the variable" in
  Unification.raise_unify_type v.v_type t v.v_pos msg;
  Sasgn (Ltuple[v], init)

let mk_locals venv pos decls =
  let do_locals (venv, vars, inits) (names, t , init_opt) =
    let t = mk_type_exp pos t in
    let init = match init_opt with
      | None -> None
      | Some init -> Some (mk_rnd_exp venv init)
    in
    let add_v (venv, vars, inits) (v_pos, name) =
      let venv, v = add_local venv v_pos name t in
      let inits = match init with None -> inits
        | Some init -> (mk_local_init v init)::inits
      in (venv, v::vars, inits)
    in List.fold_left add_v (venv, vars, inits) names
  in
  let (venv, locals, inits) = List.fold_left do_locals (venv, [], []) decls in
  venv, List.rev locals, List.rev inits

let mk_res venv pos res_opt t_res =
  let msg = "returned expression doesn't have the same type "^
    "than the function declaration" in
  match res_opt with
  | None -> 
      Unification.raise_unify_type (Tunit) t_res pos msg;
      None
  | Some ((pos,_) as e) ->
      let res, tres = mk_var_exp venv e in
      Unification.raise_unify_type tres t_res pos msg;
      Some res


let mk_fct_body venv pos t_res (decls, stmts, ret) = 
  let venv, locals, inits = mk_locals venv pos decls in
  let stmts = mk_stmt venv stmts in
  FctDef { f_local = locals;
           f_def = inits@stmts;
           f_return = mk_res venv pos ret t_res
         }

let mk_fct_decl_v venv pos ((fpos, name), params, t_res) =
  let do_param (venv, params) ((pos, name), t) =
    let venv, v = add_local venv pos name (mk_type_exp pos t) in
    venv, v::params
  in
  let venv, params = List.fold_left do_param (venv, []) params in
  let t_res = mk_type_exp pos t_res in
  venv, fpos, name, List.rev params, t_res

let mk_fct_decl game pos fun_decl =
  let venv = Global.game_venv game in
  let venv, fpos, name, params, t_res =  mk_fct_decl_v venv pos fun_decl in
  venv, fpos, name, params, t_res

let mk_fct game pos f_decl f_body =
  let venv, fpos, name, params, t_res = mk_fct_decl game pos f_decl in
  let body = mk_fct_body venv pos t_res f_body in
  fpos, name, params, t_res, body

let mk_ifct ((pos, name), params, rty) =
  if not (EcUtil.uniq (List.map (fun x -> snd (fst x)) params)) then
    pos_error pos "duplicate names in function parameters" ;
  let rty    = mk_type_exp pos rty in
  let params = List.map (fun ((_, x), ty) -> (x, mk_type_exp pos ty)) params in
    { if_pos    = pos   ;
      if_name   = name  ;
      if_params = params;
      if_type   = rty   ; }

let mk_adv_decl pos (fun_decl, odecl) =
  let venv = Global.empty_venv () in
  let _venv, fpos, name, params, t_res = mk_fct_decl_v venv pos fun_decl in
  let mk_odecl (t_params, t_res) =
    let t_res = mk_type_exp pos t_res in
    let t_params = List.map (mk_type_exp pos) t_params in
    t_params, t_res in
  { adv_name = name;
    adv_pos = fpos;
    adv_param = params;
    adv_res = t_res;
    adv_odecl = List.map mk_odecl odecl
  }

let check_oracle pos osig fct =
  let fsig = List.map (fun v -> v.v_type) fct.f_param, fct.f_res.v_type in
  try
    List.iter2 Unification.unify_type (fst osig) (fst fsig);
    Unification.unify_type (snd osig) (snd fsig)
  with _ ->
    pos_error pos "the function %s has type %a where the type %a is expected"
      fct.f_name PpAst.pp_fct_sig fsig PpAst.pp_fct_sig osig

let check_oracles pos osigs fcts =
  try
    List.iter2 (check_oracle pos) osigs fcts
  with _ ->
    pos_error pos "wrong number of oracles in adversary definition"


let mk_adv_body pos adv oracles =
  let find_oracle name =
    try Global.find_fct name
    with Not_found -> pos_error pos "unknow function %s" name in
  let fcts = List.map find_oracle oracles in
  check_oracles pos adv.adv_odecl fcts;
  FctAdv (adv, fcts)

(*~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~*)
(** {2 Annotations } *)

let get_fun pos (gnames, fname) =
  let (_, game) =
    match gnames with
      | [] -> bug "unqualifed function name"
      | top :: gnames ->
        let top =
          try  Global.find_game top
          with Not_found ->
            pos_error pos
              "game lookup failed for `%s' at toplevel"
              top
        in
          List.fold_left
            (fun (ctxt, top) gname ->
               try
                 let g = List.find (fun g -> g.g_name = gname) top.g_subgames in
                   (g :: ctxt, g)
               with Not_found ->
                 pos_error pos
                   "game lookup failed for `%s' in context `%s'"
                   gname
                   (String.concat "." (List.rev_map (fun g -> g.g_name) ctxt)))
            ([], top) gnames
  in
    try  Global.find_fct_game fname game
    with Not_found ->
      pos_error pos
        "function lookup failed for `%s' in context `%s'"
        fname (String.concat "." gnames)


let rec mk_req_mem _pos lvenv venv1 venv2 names =
  let mk_cmp (pos, v) =
    let e1 = Ebase (AstYacc.Eat ((pos, Ebase (AstYacc.Eident v)), 1)) in
    let e2 = Ebase (AstYacc.Eat ((pos, Ebase (AstYacc.Eident v)), 2)) in
    let cmp =
      (Ebase (AstYacc.Ebinop (get_tk_name TK_EQ, (pos, e1), (pos, e2)))) in
    fst (mk_var2_exp lvenv venv1 venv2 (pos, cmp))
  in
  let rec prop names = match names with
    | [] -> bug "parser should fail when no name in equivalence list"
    | v::[] -> Fol.pred_of_term (mk_cmp v)
    | v::tl -> Fol.pand (Fol.pred_of_term (mk_cmp v)) (prop tl)
  in prop names

let g_bounded_vars mk_type_exp lvenv decl =
  let do_param (lvenv, params) ((pos, name), t) =
    let lvenv, lv = Global.add_lvar lvenv name (mk_type_exp pos t) in
    lvenv, lv::params
  in
  let lvenv, lvars = (List.fold_left do_param (lvenv, []) decl) in
  let lvars = List.rev lvars in
  lvenv, lvars

let bounded_vars = g_bounded_vars mk_type_exp

let logical_token =
  let s_and = get_tk_name TK_AND in
  let s_or = get_tk_name TK_OR in
  let s_impl = get_tk_name TK_IMPL in
  let s_iff = get_tk_name TK_IFF in
  let s_not = get_tk_name TK_NOT in
  fun s ->
    match s with
    | s when s = s_and  -> Some TK_AND
    | s when s = s_or   -> Some TK_OR
    | s when s = s_impl -> Some TK_IMPL
    | s when s = s_iff  -> Some TK_IFF
    | s when s = s_not  -> Some TK_NOT
    | _ -> None

let mk_fol lvenv mk_t mk_req mk_e fol_p =
  let pred_of_term lvenv pos p =
    let e, t = mk_e lvenv (pos,p) in
    Unification.raise_unify_type t Tbool pos 
      "this expression should have type bool";
    Fol.pred_of_term e in
  let rec aux lvenv (pos, p) =
    match p with
    | Ast.Ebase (AstYacc.Ebinop(op,p1,p2)) ->
        begin match logical_token op with
        | Some TK_AND  -> Fol.pand (aux lvenv p1) (aux lvenv p2)
        | Some TK_OR   -> Fol.por (aux lvenv p1) (aux lvenv p2)
        | Some TK_IMPL -> Fol.pimplies (aux lvenv p1) (aux lvenv p2)
        | Some TK_IFF  -> Fol.piff (aux lvenv p1) (aux lvenv p2)
        | _ -> pred_of_term lvenv pos p
        end
    | Ast.Elet(xs,e,p) ->
        let e',t1 = mk_e lvenv e in
        let lvenv, lvars = 
          match xs with
          | [] -> 
              bug 
                "EcTyping.mk_fol : found a let expression without binding variable"
          | [x] ->
              let lvenv, v = Global.add_lvar lvenv (snd x) t1 in
              lvenv,[v]
          | _ ->
              let lt =
                try EcTerm.get_tuple t1 
                with Not_found ->
                  pos_error (fst e) "a tuple with %i arguments is expected"
                    (List.length xs) in
              if List.length lt <> List.length xs then
                pos_error pos "a pattern with %i arguments is expected"
                  (List.length lt); 
              let lvenv, lvars = 
                List.fold_left2
                  (fun (lvenv,lvars) x t ->
                    let lvenv, lv = Global.add_lvar lvenv (snd x) t in
                    lvenv, lv::lvars) (lvenv, []) xs lt in
              lvenv, List.rev lvars 
        in
        Fol.Plet(lvars,e', aux lvenv p)
    | Ast.Ebase (AstYacc.Eforall(decl, triggers, p)) ->
        let lvenv, lvars = g_bounded_vars mk_t lvenv decl in
        let triggers = mk_triggers lvenv triggers in
        let p = aux lvenv p in
        Fol.forall_trigger lvars triggers p 
(*        let qq v p = Fol.forall_pred ~fresh:true v p in
        let res = List.fold_right qq lvars p in
        res *)
    | Ast.Ebase (AstYacc.Eexists(decl, triggers, p)) ->
        let lvenv, lvars = g_bounded_vars mk_t lvenv decl in
        let triggers = mk_triggers lvenv triggers in
        let p = aux lvenv p in
        Fol.exists_trigger lvars triggers p         
  (*
        let qq v p = Fol.exists_pred ~fresh:true v p in
        let res = List.fold_right qq lvars p in
        res *)
    | Ast.Eif(e1,e2,e3) ->
        let e1',tb = mk_e lvenv e1 in
        let msg = "guards in conditional expression must be of type 'bool'" in
        Unification.raise_unify_type tb Tbool pos msg;
        let p2 = aux lvenv e2 in
        let p3 = aux lvenv e3 in
        Fol.pif e1' p2 p3
    | Ast.Ebase (AstYacc.Eeqvar xs) -> mk_req lvenv (pos, xs)
    | Ast.Eapp("!", [p1]) ->
        (try Fol.pnot(aux lvenv p1)
        with _ -> mk_app pos lvenv p "!" [p1])
    | Ast.Eapp(id,args) -> mk_app pos lvenv p id args
    | _ -> pred_of_term lvenv pos p
  and mk_triggers lvenv triggers =
    List.map (fun l -> List.map (mk_e lvenv) l) triggers
  and mk_app pos lvenv p id args = 
    try
      let pr = Global.find_predicate id in
      let tparams = Fol.predicate_type pr in
      let msg = "wrong type in call argument" in
      let mk_arg arg t =
        let e,te = mk_e lvenv arg in
        Unification.raise_unify_type te t (fst arg) msg;
        e in
      if List.length args <> List.length tparams then
        pos_error pos "bad number of arguments";
      let args = List.map2 mk_arg args tparams in
      Fol.papp (pr,args) 
    with Not_found -> pred_of_term lvenv pos p in
  aux lvenv fol_p

let mk_prop lvenv p =
  let tvars = TyVarsMap.create () in
  let mk_t = g_mk_type_exp (Some tvars) in
  let mk_req _env (pos, _) =
    pos_error pos "restricted equality not allowed in proposition" in
  mk_fol lvenv mk_t mk_req mk_lvar_exp p

let mk_side_prop side venv p =
  let lvenv = Global.lvenv_of_venv venv side in
  mk_prop lvenv p

let mk_axiom p = mk_prop (Global.empty_lvenv ()) p

let mk_rel lvenv venv1 venv2 =
  let mk_req lvenv (pos, l) = mk_req_mem pos lvenv venv1 venv2 l in
  let mk_e lvenv = mk_var2_exp lvenv venv1 venv2 in
   mk_fol lvenv mk_type_exp mk_req mk_e

(*
let mkeq_globals f1 f2 =
  try
    List.iter2 (fun (s1, v1) (s2, v2) ->
      if s1 <> s2 then raise Not_found;
      if not (Unification.eq_type v1.v_type v2.v_type) then raise Not_found)
      f1.f_game.g_vars f2.f_game.g_vars;
    Fol.peq_lvars
      (List.map snd f1.f_game.g_vars) (List.map snd f2.f_game.g_vars)
  with _ -> user_error "The two games should have the same global variables"
*)

let mkeq_globals f1 f2 =
  let lv1, lv2 = List.map snd f1.f_game.g_vars, List.map snd f2.f_game.g_vars in
  let find v1 v2 =  
    v1.v_name = v2.v_name && Unification.eq_type v1.v_type v2.v_type in
  let l = 
    List.fold_left (fun l v1 ->
      try 
        let v2 = List.find (find v1) lv2  in
        (v1,v2)::l
      with _ -> l) [] lv1 in
  let l1, l2 = List.split l in
  Fol.peq_lvars l1 l2

let mk_rnd_info venv1 venv2 (oname,t) info =
  match info with
    | RIid -> RIid
    | RIidempotant (oname',e) ->
        let name = 
          match oname', oname with
          | Some name, _ | None, Some name -> name
          | None, None -> 
              user_error 
                "You should give a name to the parameter of the function" in
        let venv,v = Global.add_lvar (Global.empty_lvenv ()) name t in
        let pos_e = fst e in
        let e = mk_var2_exp venv venv1 venv2 e in
        Unification.raise_unify_type (snd e) t pos_e "Type mismatch"; 
        RIidempotant (v,fst e)
    | RIbij ((oname1, e1), (oname2, e2)) ->
        let name1, name2 = 
          match oname1, oname2, oname with
          | Some name1, Some name2, _ -> name1, name2
          | None, None, Some name -> name, name
          | _ ->  user_error 
                "You should give a name to the parameter of the function" in
        let lvenv1,v1 = Global.add_lvar (Global.empty_lvenv ()) name1 t in
        let lvenv2,v2 = Global.add_lvar (Global.empty_lvenv ()) name2 t in
        let pos_e1 = fst e1 in
        let pos_e2 = fst e2 in
        let e1 = mk_var2_exp lvenv1 venv1 venv2 e1 in
        let e2 = mk_var2_exp lvenv2 venv1 venv2 e2 in 
        Unification.raise_unify_type (snd e1) t pos_e1 "Type mismatch"; 
        Unification.raise_unify_type (snd e2) t pos_e2 "Type mismatch";          
        RIbij ((v1,fst e1), (v2,fst e2))

let mk_inv f1 f2 venv venv1 venv2 = function
  | Inv_global r -> Inv_global (mk_rel venv venv1 venv2 r)
  | Inv_upto ((bad1,bad2), None) ->
    Inv_upto (mk_side_prop Fol.FVleft venv1 bad1,
              mk_side_prop Fol.FVright venv2 bad2,
              mkeq_globals f1 f2)
  | Inv_upto ((bad1,bad2), Some inv) ->
    Inv_upto (mk_side_prop Fol.FVleft venv1 bad1,
              mk_side_prop Fol.FVright venv2 bad2,
              mk_rel venv venv1 venv2 inv)

let mk_info f1 f2 venv venv1 venv2 = 
  function
    | (None,l) -> (Inv_global (mkeq_globals f1 f2), l)
    | (Some inv,l) -> (mk_inv f1 f2 venv venv1 venv2 inv,l) 

(* let mk_helper f1 f2 venv venv1 venv2 = function *)
(*   | Helper_inv inv -> Helper_inv (mk_info f1 f2 venv venv1 venv2 inv) *)
(*   | Helper_eager s -> *)
(*     Helper_eager (mk_stmt venv1 s, mk_stmt venv2 s) *)

let mk_eager f1 f2 s =
  let venv1 = Global.game_venv f1.f_game in
  let venv2 = Global.game_venv f2.f_game in
  (mk_stmt venv1 s, mk_stmt venv2 s)

(* let mk_equiv_kind f1 f2 = function *)
(*   | Aequiv_spec (pre, post, info) -> *)
(*     let lvenv = Global.empty_lvenv () in *)
(*     let venv1 = Global.game_venv f1.f_game in *)
(*     let venv_pre1 = Global.fun_pre_venv f1 in *)
(*     let venv_post1 = Global.fun_post_venv f1 in *)
(*     let venv2 = Global.game_venv f2.f_game in *)
(*     let venv_pre2 = Global.fun_pre_venv f2 in *)
(*     let venv_post2 = Global.fun_post_venv f2 in *)
(*     let pre = mk_rel lvenv venv_pre1 venv_pre2 pre in *)
(*     let post = mk_rel lvenv venv_post1 venv_post2 post in *)
(*     let info = mk_helper f1 f2 lvenv venv1 venv2 info in *)
(*     Aequiv_spec (pre, post, info) *)
(*   | Aequiv_inv (inv,l) -> *)
(*     let lvenv = Global.empty_lvenv () in *)
(*     let venv1 = Global.game_venv f1.f_game in *)
(*     let venv2 = Global.game_venv f2.f_game in *)
(*     Aequiv_inv (mk_inv f1 f2 lvenv venv1 venv2 inv, l) *)

let mk_pr pos f e =
  let f = get_fun pos f in
  let venv = Global.fun_post_venv f in
  let e, _ = mk_var_exp venv e in
  (Ebase (f, e):real_exp), Treal

let add_var_r _ (pos, _) _ =
  pos_error pos "let expression not allowed here"

let mk_real_cmp ((pos, _) as pe) =
  let (e, t) =
    try mk_g_exp () add_var_r mk_pr mk_no_var mk_no_random pe
    with ex -> catch_op_not_found pos ex in
  Unification.raise_unify_type t Tbool pos
    "only bool expression is allowed here";
  e

let mk_pr_bad_hint pos (_, r1) (_, r2) (_, bad) id =
  match r1, r2, bad with
    | Ebase (AstYacc.Epr (f1, _)), Ebase (AstYacc.Epr (f2, _)),
  Ebase (AstYacc.Epr (_, bad)) ->
      let f1 = get_fun pos f1 in
      let venv = Global.fun_post_venv f1 in
      let bad1, _ = mk_var_exp venv bad in
      let f2 = get_fun pos f2 in
      let venv = Global.fun_post_venv f2 in
      let bad2, _ = mk_var_exp venv bad in
      Pr_bad (bad1, bad2, id)
    | _ -> pos_error pos "do not known how to build upto bad info"

let mk_pr_hint ((pos, e):AstYacc.p_exp) hint =
  match hint with
    | AstYacc.Hsame -> Pr_same
    | AstYacc.Hsplit -> Pr_split
    | AstYacc.Hadmit -> Pr_admit
    | AstYacc.Hcompute -> Pr_compute
    | AstYacc.Hnone ->  Pr_none
    | AstYacc.Hauto -> assert false
    | AstYacc.Hfailure (n, p1,p2,l) ->
      begin match e with
        | Ebase(AstYacc.Ebinop(name, (_, Ebase(AstYacc.Epr(fname,_))), _))
            when name = get_tk_name TK_LE ->
          let f = get_fun pos fname in
          let g = f.f_game in
          let venv = Global.game_venv g in
          (* Warning we should check the types *)
          let bad, count = fst (mk_var_exp venv p1), fst (mk_var_exp venv p2) in
          let mk_l (s, e) = 
            let f' = 
              try Global.find_fct_game s g 
              with _ -> user_error "unknown function %s" s in
            let venv = Global.fun_pre_venv f' in
            let e = fst (mk_var_exp venv e) in
            f', e in
          Pr_failure (n, (bad:var_exp), (count:var_exp), List.map mk_l l)
        | _ -> pos_error pos "this expression is not allowed here"
      end
    | AstYacc.Husing id ->
      match e with
        | Ebase (AstYacc.Ebinop (name, _, _)) when name = get_tk_name TK_EQ  ->
          Pr_equiv id
        | Ebase (AstYacc.Ebinop (name, e1, e2))
            when name = get_tk_name TK_LE ->
          begin match e1, e2 with
            | (_, Eapp (abs, [(_, Ebase (AstYacc.Ebinop (minus,r1,r2)))])), bad
              when abs = "abs" && minus = get_tk_name TK_MINUS ->
              mk_pr_bad_hint pos r1 r2 bad id
            | _, (_, Ebase (AstYacc.Ebinop 
                              (plus, 
                               (_,Ebase (AstYacc.Ebinop(mult,_,_ ))), 
                               _))) when 
                plus = get_tk_name TK_PLUS &&
                                      mult = get_tk_name TK_STAR
                                      -> Pr_equiv id
            | r1, (_, Ebase (AstYacc.Ebinop (plus, r2, bad)))
              when plus = get_tk_name TK_PLUS ->
              mk_pr_bad_hint pos r1 r2 bad id
            | _ -> Pr_equiv id
          end
        | _ -> pos_error pos "this expression is not allowed here"

let mk_proba pe hint =
  (mk_real_cmp pe, mk_pr_hint pe hint)

let mk_claim _pos (re, id) = mk_proba re id

let mk_app _pos lvenv venv_pre1 venv_pre2 _pre app = 
  match app with
  | None -> None
  | Some (alpha,delta) ->
      let pos_a,_ = alpha in
      let pos_d,_ = delta in
      let (alpha',ta) = mk_var2_exp lvenv venv_pre1 venv_pre2 alpha in
      let (delta',td) = mk_var2_exp lvenv venv_pre1 venv_pre2 delta in
      let msg =
        "skew must be of type 'real'"
      in Unification.raise_unify_type ta Treal pos_a msg;
      let msg =
        "slack must be of type 'real'"
      in Unification.raise_unify_type td Treal pos_d msg;
      Some(alpha',delta')
  
let mk_equiv pos f1 f2 concl =
  let f1 = get_fun pos f1 in
  let f2 = get_fun pos f2 in
  let lvenv = Global.empty_lvenv () in
  match concl with
  | AstYacc.Aequiv_spec (pre,post,app) ->
      let venv_pre1 = Global.fun_pre_venv f1 in
      let venv_post1 = Global.fun_post_venv f1 in
      let venv_pre2 = Global.fun_pre_venv f2 in
      let venv_post2 = Global.fun_post_venv f2 in
      let pre = mk_rel lvenv venv_pre1 venv_pre2 pre in
      let post = mk_rel lvenv venv_post1 venv_post2 post in
      (* TODO: Should we realy use venv_pre1 and venv_pre2 *)
      let app = mk_app pos lvenv venv_pre1 venv_pre2 pre app in
      f1,f2,pre,post,app
  | AstYacc.Aequiv_inv inv ->
      let venv1 = Global.game_venv f1.f_game in
      let venv2 = Global.game_venv f2.f_game in
      let inv = mk_inv f1 f2 lvenv venv1 venv2 inv in
      let pre,post = FunLogic.build_inv_spec inv f1 f2 in
      f1,f2,pre,post,None

(*
      let venv1 = Global.game_venv f1.f_game in
      let venv2 = Global.game_venv f2.f_game in
      let inv = mk_inv f1 f2 lvenv venv1 venv2 in
*)      






let mk_info f1 f2 info =
    let lvenv = Global.empty_lvenv () in
    let venv1 = Global.game_venv f1.f_game in
    let venv2 = Global.game_venv f2.f_game in
    mk_info f1 f2 lvenv venv1 venv2 info

(*~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~*)

let mk_pred venv1 venv2 p =
  mk_rel (Global.empty_lvenv ()) venv1 venv2 p

(*~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~*)

let check_pre f1 f2 pre =
  let fv1, fv2 = Fol.fv_pred pre in
  let env1,env2 = Global.fun_pre_venv f1, Global.fun_pre_venv f2 in
  if not (Global.check_fv env1 fv1 && Global.check_fv env2 fv2) then
    cannot_apply "check_pre" "bad precondition"

let check_post f1 f2 post =
  let fv1, fv2 = Fol.fv_pred post in
  let env1,env2 = Global.fun_post_venv f1, Global.fun_post_venv f2 in
  if not (Global.check_fv env1 fv1 && Global.check_fv env2 fv2) then
    cannot_apply "check_post" "bad postcondition"

(*~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~*)

let bounded_vvars venv decl =
  let do_param (venv, params) ((pos, name), t) =
    let venv, v = Global.add_var venv pos name (mk_type_exp pos t) in
    venv, v::params
  in
  let venv, vars = (List.fold_left do_param (venv, []) decl) in
  let vars = List.rev vars in
  venv, vars

let mk_app_opt lvenv app = match app with
  | None -> None
  | Some (alpha,delta) ->
    let pos_a = fst alpha in
    let alpha,t = mk_lvar_exp lvenv alpha in
    let msg = "skew expression must be of type 'real'"
    in Unification.raise_unify_type Treal t pos_a msg;
    let pos_d = fst delta in
    let delta,t = mk_lvar_exp lvenv delta in
    let msg =
      "slack expression must be of type 'real'"
    in Unification.raise_unify_type Treal t pos_d msg;
    Some(alpha,delta)


let mk_popspec
    ((decl,((pos_x1,x1),pexp1,cond1),((pos_x2,x2),pexp2,cond2),concl):AstYacc.pop_spec) =
  let lvenv,largvars = bounded_vars (Global.empty_lvenv()) decl in
  let  venv, argvars = bounded_vvars (Global.empty_venv()) decl in
  match concl with 
    | AstYacc.Aequiv_inv _ -> 
      user_error "Bad specification"
    | AstYacc.Aequiv_spec (pre,post,app) ->
      begin
        let pexp1,type_res1 = mk_rnd_exp venv pexp1 in
        let pexp2,type_res2 = mk_rnd_exp venv pexp2 in

        let lvenv,l_x1 = Global.add_lvar lvenv x1 type_res1 in
        let lvenv,l_x2 = Global.add_lvar lvenv x2 type_res2 in

        let pre = mk_prop lvenv pre in
        let post = mk_prop lvenv post in

        let app = mk_app_opt lvenv app in

        let cond1,cond2 = match cond1,cond2 with
          | None, None -> None, None
          | Some e1, Some e2 -> 
            let venv1,_ = Global.add_var venv pos_x1 x1 type_res1 in
            let venv2,_ = Global.add_var venv pos_x2 x2 type_res2 in
            let msg = "conditional expression must be of type bool" in
            let pos1 = fst e1 in
            let e1,t = mk_var_exp venv1 e1 in
            Unification.raise_unify_type Tbool t pos1 msg;
            let pos2 = fst e2 in
            let e2,t = mk_var_exp venv2 e2 in
            Unification.raise_unify_type Tbool t pos2 msg;
            Some e1, Some e2
          | _ -> assert false
        in
        ((largvars,argvars),(l_x1,pexp1,cond1),(l_x2,pexp2,cond2),(pre,post,app):Fol.pop_spec)
      end

let mk_pop_aspec 
    (decl,((_,x),(_,pop),args),(pre,post)) =
  let lvenv = Global.empty_lvenv () in
  let lvenv,argvars = bounded_vars lvenv decl in
  let argtypes = List.map Fol.lv_type argvars in


  let find_var_type (pos,v) = 
    try Global.find_lvar lvenv v
    with Not_found ->
      pos_error pos "the identifier %s is not a variable" v
  in
  let lvars = List.map find_var_type  args in
  let types = List.map Fol.lv_type lvars in

  let op,type_res = 
    try Global.find_op ~prob:true EcUtil.dummy_pos pop types 
    with _ -> 
      EcUtil.user_error "Unknown probabilistic operator %s:%a -> _" pop
        (EcUtil.pp_list ~sep:(format_of_string "*") PpAst.pp_type_exp) types
  in
  let lvenv,x = Global.add_lvar lvenv x type_res in

  let pre = mk_prop lvenv pre in
  let post = mk_prop lvenv post in
  (argvars,argtypes),(x,op,lvars),(pre,post)










(*~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~*)

let mk_predicate decl body =
  let lvenv = Global.empty_lvenv () in
  let tvars = TyVarsMap.create () in
  let mk_t = g_mk_type_exp (Some tvars) in
  let lvenv, lvar = g_bounded_vars mk_t lvenv decl in
  let mk_req _env (pos, _) =
    pos_error pos "restricted equality not allowed in proposition"
  in
    TyVarsMap.iter tvars (fun _ tvar -> tvar.tv_def <- Open);
    (lvar, mk_fol lvenv mk_t mk_req mk_lvar_exp body)

let mk_apredicate (pos, dom) =
  let tvars = TyVarsMap.create () in
  let mk_t = g_mk_type_exp (Some tvars) in
  let dom = List.map (fun ty -> mk_t pos ty) dom in
    TyVarsMap.iter tvars (fun _ tvar -> tvar.tv_def <- Open);
    dom

(* -------------------------------------------------------------------- *)
type igame_match_error =
    | IGM_Missing of string
    | IGM_SigMismatch of string

exception IGameMatchError of igame_match_error

let interface_match g ig =
  let check_for_decl decl =
    let pred = fun (x, _) -> x = decl.if_name in
      match EcUtil.try_find pred g.g_functions with
        | None        -> raise (IGameMatchError (IGM_Missing decl.if_name))
        | Some (_, f) ->
          let inames, itypes = List.split decl.if_params
          and names , types  =
            List.split (List.map (fun p -> (p.v_name, p.v_type)) f.f_param)
          in
            if names <> inames then
              raise (IGameMatchError (IGM_SigMismatch decl.if_name));
            try
              Unification.unify_type_list types itypes;
              Unification.unify_type decl.if_type f.f_res.v_type;
            with Unification.TypeMismatch _ ->
              raise (IGameMatchError (IGM_SigMismatch decl.if_name))
  in
    try
      List.iter check_for_decl ig.gi_functions;
      true
    with IGameMatchError _ -> false
