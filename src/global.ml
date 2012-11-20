(* -------------------------------------------------------------------- *)
open EcUtil
open EcScope
open Ast

module C = Context

(* -------------------------------------------------------------------- *)
type why_export =
  | WE_type of Ast.tdef
  | WE_cnst of Ast.const_body
  | WE_op of Ast.oper_body
  | WE_pred of Fol.predicate

let why_export = ref ([] : why_export list)

(* -------------------------------------------------------------------- *)
module Axioms = struct
  type data = bool * Fol.pred * Fol.why3_axiom

  let iter (_f : string * data -> unit) =
    ()                                  (* FIXME *)
end

(* -------------------------------------------------------------------- *)
type eobj = [
| `Theory     of theory
| `Operator   of oper_body
| `Interface  of igame
| `Module     of game
| `ModuleDecl of string * igame
]

let eobj_name = function
  | `Theory     t      -> t.th_name
  | `Operator   o      -> o.op_name
  | `Interface  i      -> i.gi_name
  | `ModuleDecl (n, _) -> n
  | `Module     m      -> m.g_name

type pretheory_item = [theory_item | `Axiom of Fol.pred]

type pretheory = theory_item   C.context
type pregame   = game_item     C.context
type preigame  = igamesig_item C.context

module PreGame = struct
  let empty : pregame = C.empty ()
end

module PreInterface = struct
  let empty : preigame = C.empty ()
end

type preobj = [
| `Theory    of pretheory
| `Module    of pregame
| `Interface of preigame
]

type scope = (string * preobj) list

module Typing = struct
  let game (_scope : scope) ((_name, _m) : string * pregame) =
    (assert false : game)
end

module TopLevel = struct
  type top = ((string * preobj) list) ref

  let top : top = ref [ ("<top>", `Theory (C.empty ())) ]

  let name_clash_error scope leaf name =
    let path = List.map eobj_name (scope @ [leaf]) in
      user_error "cannot refined symbol `%s' in scope `%s'"
        name (String.concat "~>" path)

  let invalid_scope () = failwith "invalid-scope" (* FIXME *)

  let top_scope () =
    List.hd !top                        (* FIXME *)

  let extend (o : string * preobj) =
    top := o :: !top

  let bind (o : eobj) =
    match !top with
      | [] -> assert false
      | (n, s) :: scope ->
        let s =
          match s, o with
            | `Module s, (`Module    m as o) -> `Module (C.bind m.g_name  o s)
            | `Theory s, (`Module    m as o) -> `Theory (C.bind m.g_name  o s)
            | `Theory s, (`Interface i as o) -> `Theory (C.bind i.gi_name o s)
            | _        , _                   -> invalid_scope ()
        in
          top := (n, s) :: scope

  let open_game (name : string) =
    match snd (top_scope ()) with
      | `Interface _ -> invalid_scope ()
      | `Theory    _
      | `Module    _ -> extend (name, `Module PreGame.empty)

  let abort_game () =
    match !top with
      | (_, `Module _) :: scope -> top := scope
      | _ -> invalid_scope ()

  let close_game () =
    match !top with
      | (name, `Module m) :: scope ->
          let m = Typing.game scope (name, m) in
            bind (`Module m)
      | _ -> invalid_scope ()

  let open_igame (name : string) =
    match snd (top_scope ()) with
      | `Interface _
      | `Module    _ -> invalid_scope ()
      | `Theory    _ -> extend (name, `Interface PreInterface.empty)

  let abort_igame () =
    match !top with
      | (_, `Interface _) :: scope -> top := scope
      | _ -> invalid_scope ()
end

(** List of global declaration to export *)
let pred_list  = ref []                 (* Predicates list *)
let axiom_list = ref []                 (* Axioms     list *)
let axiom_h    = ref []

(*~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~*)
(*~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~*)
(*~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~*)
(* Global state *)

module type IFlag = sig
  type flag

  val get : unit -> flag
  val set : flag -> unit
end

module Timeout : IFlag with type flag = int = struct
  type flag = int

  let timeout = ref 3

  let get = fun () -> !timeout
  let set = fun v  -> timeout := v
end

module WithProof : IFlag with type flag = bool = struct
  type flag = bool

  let withproof = ref true

  let get = fun () -> !withproof
  let set = fun v  -> withproof := v
end

(*
let change_withproof () =
  state.withproof <- not state.withproof;
  warning "Proof mode is now %s"
    (if state.withproof then "ON" else "OFF")
*)

(*~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~*)
(** {2 Checking not defined string } *)

let primitive_types = [
  "unit", Tunit;
  "int" , Tint ;
  "bool", Tbool;
  "real", Treal;
]

let check_not_in_ctxt txt ctxt name pos =
  if C.exists name ctxt then
    pos_error pos
      "cannot redefine '%s'@, this name has already been defined as a '%s'@."
      name txt

(*~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~*)
(** {2 Findind things }
    * All these functions [find_xxx] can raise not found *)

let find_primitive_type name =
  List.assoc name primitive_types

(*
(** Notice that we can have several operators with the same name,
    * but with different types.
    * @raise OpNotFound when this name is not defined for these types.
    * *)
exception OpNotFound of (string * type_exp list)
    
let find_op ?(prob=false) pos name type_args : oper * type_exp =
  let tbl = if prob then pop_tbl else op_tbl in
  let ops =  Hashtbl.find_all tbl name in
  (* Notice that [Hashtbl.find_all] gives all the operators with this name
   * in reverse order of introduction in the table. *)
  let fv = EcTerm.fv_types type_args in
  let rec find l = match l with
    | [] ->
      EcTerm.reset_poly fv;
      raise (OpNotFound (name, type_args))
    | o::tl ->
      begin
        let poly,(t_params,t_res) = EcTerm.instanciate_op o pos in
        try
          let t_res = if prob then List.hd t_params else t_res in
          let t_params = if prob then List.tl t_params else t_params in
          Unification.unify_type_list t_params type_args;
          let o = {o with op_type = (t_params,t_res)} in
          ((pos,o,poly),t_res)
        with Unification.TypeMismatch _ ->
          EcTerm.reset_poly fv;
          find tl
          | e -> bug "Global.find_op: unexpected exception %s" (Printexc.to_string e)
      end
  in find ops
*)

(*~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~*)
(** {2 Add things in tables}
    * All these functions [add_xxx] first check if it is correct to add that name
    * in the environment, and raise PosError if not.
*)

(** @raise PosError if name is already defined with the same type. *)
(*
let add_op ?(prob=false) op =
  (* Sanity check *)
  let check_is_closed t = 
    match t with 
      | Tvar tv -> 
        begin
          match tv.tv_def with
            | Open -> bug "Operator %s has open type variables" op.op_name;
            | _ -> ()
        end
      | _ -> () 
  in
  List.iter (check_is_closed) (fst op.op_type);
  (* ENDOF Sanity check *)
  let name = op.op_name in
  check_not_adv name op.op_pos;
  let tbl = if prob then pop_tbl else op_tbl in
  Hashtbl.iter
    (fun _ op' -> if op'.op_why = op.op_why then
        pos_error op.op_pos "op why name %s already use" (fst op.op_why)) tbl;
  try
    let (op',_) = 
      if prob then find_op ~prob:true op.op_pos name (List.tl (fst op.op_type)) 
      else find_op ~prob:false op.op_pos name (fst op.op_type)
    in
    pos_error op.op_pos
      "cannot redefine an operator with the same input types@,\
      '%s' has already been defined at %a@."
      name pp_pos (EcTerm.op_body op').op_pos
  with OpNotFound _ ->
    EcTerm.reset_poly op.op_poly;
    if prob then
      debug db_glob "add %a" PpAst.pp_pop_decl op
    else
      debug db_glob "add %a" PpAst.pp_op_decl op;
    Hashtbl.add tbl name op;
    op_list := op :: !op_list;
    why_export := WE_op op :: !why_export

let add_axiom axiom s p =
  let why3 = Fol.mk_axiom s p in
  let ax = if axiom then "axiom" else "lemma" in
  debug db_glob "@[<hov 2>add %s %s :@;%a@]@." ax s Fol.pp_pred p;
  if List.exists (fun (s',_) -> s = s') !axiom_list then
    user_error "an axiom with name %s already exists" s;
  axiom_list := (s,(ref true,p, why3))::!axiom_list

let find_axiom name =
  let (r,ax,_) = List.assoc name !axiom_list in
  !r, ax  

let add_predicate s dom =
  let p = Fol.mk_predicate s dom in
  debug db_glob "@[<h>add pred %a@]@." Fol.pp_predicate p;
  pred_list := p::!pred_list;
  why_export := WE_pred p :: !why_export

let add_apredicate s p =
  let p = Fol.mk_apredicate s p in
  debug db_glob "@[<h>add apred %a@]@." Fol.pp_predicate p;
  pred_list := p::!pred_list;
  why_export := WE_pred p :: !why_export

let add_popspec name p = 
  debug db_glob "@[<h>add pop spec : %s@]@." name;
  if List.mem name predefined_pop_specs || List.mem_assoc name !pop_specs then 
    user_error "a spec with name %s already exists" name;
  pop_specs := (name,p)::!pop_specs
let find_popspec name = 
  List.assoc name !pop_specs

let add_pop_aspec name p = 
  debug db_glob "@[<h>add pop aspec : %s@]@." name;
  if List.mem name predefined_pop_aspecs || List.mem_assoc name !pop_aspecs then 
    user_error "a aspec with name %s already exists" name;
  pop_aspecs := (name,p)::!pop_aspecs


let find_pop_aspec name = 
  List.assoc name !pop_aspecs

let set_all_axiom b =
  let l = init_axiom_list () in
  List.iter (fun (s,(r,_,_)) -> if not (List.mem_assoc s l) then r := b) !axiom_list 

let set_axiom l =
  List.iter (fun (s,(r,_,_)) -> if List.mem s l then r := true) !axiom_list

let unset_axiom l =
  List.iter (fun (s,(r,_,_)) -> if List.mem s l then r := false) !axiom_list
*)

(*~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~*)
(** {2 Initialisation} *)

(*
let t_bool_binop = ([Tbool; Tbool], Tbool)
let t_int_binop = ([Tint; Tint], Tint)
let t_real_binop = ([Treal; Treal], Treal)
let t_int_binop_bool = ([Tint; Tint], Tbool)
let t_real_binop_bool = ([Treal; Treal], Tbool)

let builtins_pos n = ("<builtins>", (0, n, 0), (0, n, 0))

(* let add_tk_op tk nat why t_op assoc prec = *)
(*   let op_body = *)
(*     EcTerm.mk_op_body (get_tk_name tk) (Some nat) (why,false) t_op None *)
(*       true (builtins_pos 10) assoc prec in *)
(*   add_op op_body *)

let add_native_op s nat why t_op =
  let op_body = 
    EcTerm.mk_op_body s (Some nat) (why,false) t_op None 
      false (builtins_pos 20) None 0 in
  add_op op_body

let add_primitive_type name pos t_poly def =
  let test = 
    List.for_all 
      (fun t -> match t with Tvar { tv_def = Open } -> true | _ -> false) 
      t_poly in
  if not test then bug "Global.add_primitive_type";
  let tdef = EcTerm.mk_tdef name pos t_poly def in
  add_type tdef

let add_why3_type name ts poly =
   add_type 
    { t_name = name; 
      t_wsymbol = ts;
      t_native_why = true;
      t_pos = dummy_pos;
      t_poly = poly;
      t_def = None
    }

let add_why3_native_cnst name ls t =
  let fv = EcTerm.fv_type t in
  add_cnst 
    {
     c_name = name;
     c_poly = fv;
     c_type = t;
     c_pos  = dummy_pos;
     c_def  = None;
     c_why3 = ls,None;
     c_native_why = true
   }

let num_op = ref 0 

let new_num () =
  incr num_op;
  string_of_int !num_op

let add_why3_op native infix name ls t assoc prec = 
  let fv = 
    let (tparams,tres) = t in
    EcTerm.fv_types (tres::tparams) in
  add_op 
    {
     op_name   = name;
     op_native = Some native;
     op_why    = new_num (), false;
     op_why3   = ls,None;
     op_native_why = true;
     op_id     = UID.fresh_op name;
     op_poly   = fv;
     op_type   = t;
     op_body   = None;
     op_infix  = infix;
     op_pos    = dummy_pos;
     op_assoc  = assoc;
     op_prec   = prec;
   }  

let add_why3_native_op nat infix name ls t_op =
  add_why3_op nat infix name ls t_op None 0

let add_why3_tk_op tk nat ls t_op assoc prec =
  add_why3_op nat true (get_tk_name tk) ls t_op assoc prec

let option_type ta =
  let tdef = find_type "option" dummy_pos in
  Tnamed {tdef with t_poly = [ta]}

let list_type ta = 
  let tdef = find_type "list" dummy_pos in
  Tnamed {tdef with t_poly = [ta]}

let map_type ta tb =
  let tdef = find_type "map" dummy_pos in
  Tnamed {tdef with t_poly = [ta;tb]}
  

let init () =
  (* Type from why *)
  let ta = Tvar (EcTerm.mk_tvar "'a" dummy_pos) in
  let tb = Tvar (EcTerm.mk_tvar "'b" dummy_pos) in
  add_why3_type "list" EcWhy3.ts_list [ta];
  add_why3_type "option" EcWhy3.ts_option [ta];
  add_primitive_type "map" dummy_pos [ta;tb] None;

  (* builtin operators *)

  let t = Tvar (EcTerm.mk_tvar ~tvar_def:Ast.Closed "'a" (builtins_pos 20)) in
  add_why3_tk_op TK_EQ EQ Why3.Term.ps_equ ([t; t], Tbool) None 70;

  (* boolean *)
  add_why3_tk_op TK_AND AND EcWhy3.ls_andb t_bool_binop (Some false) 80;
  add_why3_tk_op TK_OR OR EcWhy3.ls_orb t_bool_binop (Some false) 85;
  add_why3_tk_op TK_XOR XOR EcWhy3.ls_xorb t_bool_binop (Some false) 85;
  add_why3_tk_op TK_NOT NOT EcWhy3.ls_notb ([Tbool], Tbool) None 75;

  (* integer *)
  add_why3_tk_op TK_LT INT_LT EcWhy3.ps_lt_int t_int_binop_bool None 70;
  add_why3_tk_op TK_LE INT_LE EcWhy3.ps_le_int t_int_binop_bool None 70;
  add_why3_tk_op TK_MINUS INT_OPP EcWhy3.ls_opp_int ([Tint],Tint) None 35;
  add_why3_tk_op TK_PLUS INT_ADD EcWhy3.ls_add_int t_int_binop (Some false) 50;
  add_why3_tk_op TK_MINUS INT_SUB EcWhy3.ls_sub_int t_int_binop (Some false) 50;
  add_why3_tk_op TK_STAR INT_MUL EcWhy3.ls_mul_int t_int_binop (Some false) 40;
  add_why3_tk_op TK_DIV INT_DIV EcWhy3.ls_div_int t_int_binop (Some false) 40;
  add_why3_tk_op TK_MOD INT_MOD EcWhy3.ls_mod_int t_int_binop (Some false) 40;
  add_why3_tk_op TK_HAT INT_POW EcWhy3.ls_pow_int t_int_binop (Some false) 30;
  add_why3_native_op INT_ABS false "abs" EcWhy3.ls_abs_int ([Tint],Tint);

  (* real *)
  add_why3_tk_op TK_LT REAL_LT EcWhy3.ps_lt_real t_real_binop_bool None 70;
  add_why3_tk_op TK_LE REAL_LE EcWhy3.ps_le_real t_real_binop_bool None 70;
  add_why3_tk_op TK_MINUS REAL_OPP EcWhy3.ls_opp_real ([Treal],Treal) None 35;
  add_why3_tk_op TK_PLUS REAL_ADD EcWhy3.ls_add_real t_real_binop (Some false) 50;
  add_why3_tk_op TK_MINUS REAL_SUB EcWhy3.ls_sub_real t_real_binop (Some false) 50;
  add_why3_tk_op TK_STAR REAL_MUL EcWhy3.ls_mul_real t_real_binop (Some false) 40;
  add_why3_tk_op TK_DIV REAL_DIV EcWhy3.ls_div_real t_real_binop (Some false) 40;
  add_why3_tk_op TK_HAT REAL_POW EcWhy3.ls_pow_real t_real_binop (Some false) 30;
  add_why3_native_op REAL_OF_INT false "real_of_int" EcWhy3.ls_real_of_int 
    ([Tint], Treal);
  add_native_op "real_of_bool" REAL_OF_BOOL "real_of_bool" ([Tbool], Treal);
  add_why3_native_op REAL_ABS false "abs" EcWhy3.ls_abs_real ([Treal],Treal);
  add_why3_native_op REAL_EXP false "exp" EcWhy3.ls_exp_real ([Treal],Treal);

  (* option *)
  let ta = Tvar (EcTerm.mk_tvar ~tvar_def:Ast.Closed "'a" (builtins_pos 20)) in
  add_why3_native_op SOME_OPT false "Some" EcWhy3.ls_some 
    ([ta], option_type ta);
  add_why3_native_cnst "None" EcWhy3.ls_none (option_type ta);

  (* list *)
  let t = Tvar (EcTerm.mk_tvar ~tvar_def:Ast.Closed "'a" (builtins_pos 20)) in
  let lt = list_type t in
  add_why3_tk_op TK_CONS CONS_LIST EcWhy3.ls_cons ([t; lt], lt) (Some true) 60;
  add_why3_native_cnst "[]" EcWhy3.ls_nil lt;
  add_why3_native_op IN_LIST false "mem" EcWhy3.ls_mem ([t;lt], Tbool);
  add_why3_native_op LENGTH_LIST false "length" EcWhy3.ls_length ([lt], Tint);
  add_why3_tk_op TK_APP APPEND_LIST EcWhy3.ls_app  ([lt;lt], lt) (Some true) 60;
 
  (* map *)
  let ta = Tvar (EcTerm.mk_tvar ~tvar_def:Ast.Closed "'a" (builtins_pos 20)) in
  let tb = Tvar (EcTerm.mk_tvar ~tvar_def:Ast.Closed "'b" (builtins_pos 20)) in
  let tm = map_type ta tb in
  add_native_op "upd" PUPD_MAP "upd_map" ([tm;ta;tb], tm);
  add_native_op "get" PGET_MAP "get_map" ([tm;ta], tb);
  add_native_op "in_dom" PINDOM_MAP "in_dom_map" ([ta;tm], Tbool);
  add_native_op "in_rng" PINRNG_MAP "in_rng_map" ([tb;tm], Tbool);
  
 (* bitstring *)
 (* *)
  save_global ()


let _ = init ()
*)

(* All this function needs initialisation *)

let bool_not = assert false
let bool_and = assert false

let op_int_le  = assert false            (* FIXME *)
let op_int_lt  = assert false
let op_int_add = assert false
let op_int_sub = assert false
let op_int_mul = assert false
let op_int_pow = assert false

let op_fst         = assert false
let op_snd         = assert false
let op_upd_map     = assert false
let op_get_map     = assert false
let op_length_list = assert false
let op_in_list     = assert false

(*

let bool_not =
  fst (find_op dummy_pos (get_tk_name TK_NOT) [Tbool])

let bool_and =
  fst (find_op dummy_pos (get_tk_name TK_AND) (fst t_bool_binop))

let op_int_le =
  fst (find_op dummy_pos (get_tk_name TK_LE) (fst t_int_binop_bool))

let op_int_lt =
  fst (find_op dummy_pos (get_tk_name TK_LT) (fst t_int_binop_bool))

let op_real_of_int =
  fst (find_op dummy_pos "real_of_int" [Tint])

let op_real_of_bool =
  fst (find_op dummy_pos "real_of_bool" [Tbool])

let op_real_mul =
  fst (find_op dummy_pos  (get_tk_name TK_STAR) (fst t_real_binop))

let op_real_add =
  fst (find_op dummy_pos  (get_tk_name TK_PLUS) (fst t_real_binop))

let op_real_sub =
  fst (find_op dummy_pos  (get_tk_name TK_MINUS) (fst t_real_binop))

let op_real_div =
  fst (find_op dummy_pos  (get_tk_name TK_DIV) (fst t_real_binop))

let op_real_pow =
  fst (find_op dummy_pos  (get_tk_name TK_HAT) (fst t_real_binop)) 

let op_real_le =
  fst (find_op dummy_pos  (get_tk_name TK_LE) (fst t_real_binop))

let op_real_eq =
  fst (find_op dummy_pos (get_tk_name TK_EQ) (fst t_real_binop))

let op_int_pow =
  fst (find_op dummy_pos  (get_tk_name TK_HAT) (fst t_int_binop))

let op_int_mul =
  fst (find_op dummy_pos  (get_tk_name TK_STAR) (fst t_int_binop))

let op_int_add =
  fst (find_op dummy_pos  (get_tk_name TK_PLUS) (fst t_int_binop))

let op_int_sub =
  fst (find_op dummy_pos  (get_tk_name TK_MINUS) (fst t_int_binop))
*)

  (*
let op_fst t =
  fst (find_op dummy_pos "fst" [t])

let op_snd t =
  fst (find_op dummy_pos "snd" [t])

  
let op_upd_map tm = 
  try match EcTerm.get_named_type "map" tm with
  | [tk;tv] -> fst (find_op dummy_pos "upd" [tm;tk;tv])
  | _ -> bug "[Global] : op_upd_map, bad number of arguments" 
  with Not_found -> bug "[Global] : op_upd_map" 


let op_get_map tm =
  try match EcTerm.get_named_type "map" tm with
  | [tk;_] -> fst (find_op dummy_pos "get" [tm;tk])
  | _ ->bug "[Global] : op_get_map, bad number of arguments"
  with Not_found -> bug "[Global] : op_get_map"


let op_length_list t =
  fst (find_op dummy_pos "length" [list_type t])

let op_in_list t =
  fst (find_op dummy_pos "mem" [t;list_type t])

(*~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~*)

let check_fv env fv =
  let check x = List.exists (fun (_,y) -> EcTerm.eq_var x y) env in
  EcTerm.Vset.for_all check fv

(*~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~*)

let rzero =
  
  Eapp(op_real_of_int,[Ecnst (Eint 0)])

let rone =
  Eapp(op_real_of_int,[Ecnst (Eint 1)])


let itr n =
  Eapp(op_real_of_int,[Ecnst (Eint n)])


(** Commands for find and print declarations or definitions *)

(** Show game definition *)
let find_and_show_game name =
  try 
    let g = find_game name in
      Format.printf "%a" PpAst.pp_game g
   with Not_found -> ()

(** Show axiom definition *)
let find_and_show_axiom name = 
  try
    let (b,ax) = find_axiom name in
    Format.printf "@[<hov 2>axiom %s:@;%a@]@." name Fol.pp_pred ax;
    if not b then Format.printf "is unset@."
  with Not_found -> ()

(** Show pred definition *)
let find_and_show_pred name = 
  try
    let p = find_predicate name in    
    Format.printf "@[<h>pred @[<hov 2>%a@]@]@." Fol.pp_predicate p;
    if Fol.opacity p then Format.printf "is opaque@."
  with Not_found -> ()


(** Show type definition *)
let find_and_show_type name =
  try
    let ty = Hashtbl.find type_tbl name in
    Format.printf "%a" PpAst.pp_type_def ty
  with Not_found -> ()

(** Show cnst declaration *)
let find_and_show_cnst name =
  try
    let c = find_cst name in
      Format.printf "%a" PpAst.pp_cnst_def c
  with Not_found -> ()

(** Show all op declarations *)
let find_and_show_op name =
  try
    let xs = Hashtbl.find_all op_tbl name in
      List.iter (Format.printf "%a" PpAst.pp_op_decl) xs
  with Not_found -> ()

(** Show all pop declarations *)
let find_and_show_pop name =
  try
    let xs = Hashtbl.find_all pop_tbl name in
      List.iter (Format.printf "%a" PpAst.pp_pop_decl) xs
  with Not_found -> ()

(** Show adversary declaration *)
let find_and_show_adv name =
  try
    let a = Hashtbl.find adv_tbl name in
      Format.printf "%a" PpAst.pp_adv_decl a
  with Not_found -> ()

let find_and_show_fct (gnames, fname) =
  let (_, game) =
    match gnames with
      | [] -> bug "unqualifed function name"
      | top :: gnames ->
        let top =
          try  find_game top
          with Not_found ->
            user_error
              "game lookup failed for `%s' at toplevel"
              top
        in
          List.fold_left
            (fun (ctxt, top) gname ->
               try
                 let g = List.find (fun g -> g.g_name = gname) top.g_subgames in
                   (g :: ctxt, g)
               with Not_found ->
                 user_error
                   "game lookup failed for `%s' in context `%s'"
                   gname
                   (String.concat "." (List.rev_map (fun g -> g.g_name) ctxt)))
            ([], top) gnames in
  let f =
    try  find_fct_game fname game
    with Not_found ->
      user_error
        "function lookup failed for `%s' in context `%s'"
        fname (String.concat "." gnames)
  in
    Format.printf "%a" PpAst.pp_fct f

let print_set_axiom b =
  let l = List.filter (fun (_,(r,_,_)) -> !r = b) !axiom_list in
  let pp fmt (s,_) = Format.fprintf fmt "%s" s in
  Format.printf "%a@." (pp_list ~sep:", " pp) (List.rev l)

let print_all_axiom () =
  List.iter 
    (fun (name,(r,ax,_)) -> 
      Format.printf "@[<hov 2>axiom@ %s:@;%a@]@." name Fol.pp_pred ax;
      if not !r then Format.printf "is unset@.")
    (List.rev !axiom_list)

let print_all_op () =
  List.iter 
    (Format.printf "%a" PpAst.pp_op_decl)
    (List.rev !op_list)

let print_all_cnst () =
  List.iter 
    (Format.printf "%a" PpAst.pp_cnst_def)
    (List.rev !cnst_list)

let print_all_pred () =
  List.iter 
    (fun p -> 
      Format.printf "@[<h>pred@ %a@]@." Fol.pp_predicate p;
      if Fol.opacity p then Format.printf "is opaque@.")
    (List.rev !pred_list)

let print_all_type () =
  List.iter (Format.printf "%a" PpAst.pp_type_def)
    (List.rev !type_list)



(*** Adding bitstring *)
(* TODO Deal with undo ??? *)
(* let bitstring_size = ref []  *)

let add_bitstring c =
  try ignore (EcTerm.find_bitstring c) 
  with Not_found -> 
    let name = EcTerm.add_bitstring c in
    let t = Ast.Tbitstring c in
    let op_body =
      EcTerm.mk_op_body "^^" None ("xor_bs_"^name,false) 
         ([t;t],t) None true (builtins_pos 100) (Some false) 30 in
    add_op op_body;
    let zero_body =
      let name = "bs0_"^name in
      let ls = EcTerm.mk_fsymbol name ([],t) in
      { c_name = name;
        c_poly = [];
        c_type = t;
        c_pos  = dummy_pos;
        c_def  = None;
        c_why3 = ls,None;
        c_native_why = false } in
    add_cnst zero_body;
    let zero = Ecnst (Ecst (zero_body, [])) in

    let x = Fol.logic_lvar "x" t in
    let y = Fol.logic_lvar "y" t in
    let z = Fol.logic_lvar "z" t in
    let tx,ty, tz = Ebase x, Ebase y, Ebase z in
    let mk_xor x y =
      Eapp((dummy_pos,op_body,[]), [x;y]) in
    (* commutativity *)
    let p = 
      Fol.forall_trigger [x;y] [] 
        (Fol.peq (mk_xor tx ty) (mk_xor ty tx)) in
    let pname = "xor_"^name^"_comm" in    
    add_axiom false pname p;
    (* associativity *)
    let p = 
      Fol.forall_trigger [x;y;z] [] 
        (Fol.peq (mk_xor (mk_xor tx ty) tz) (mk_xor tx (mk_xor ty tz))) in  
    let pname =  "xor_"^name^"_assoc" in    
    add_axiom false pname p;
    (* zero_r *)
    let p = 
      Fol.forall_trigger [x] [] 
        (Fol.peq (mk_xor tx zero) tx) in
    let pname =  "xor_"^name^"_zero_r" in    
    add_axiom false pname p;
    (* cancel *)
    let p = 
      Fol.forall_trigger [x] [] 
        (Fol.peq (mk_xor tx tx) zero) in
    let pname =  "xor_"^name^"_cancel" in    
    add_axiom false pname p
*)
