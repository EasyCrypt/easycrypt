(*~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~*)

open EcUtil
open Ast

(*~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~*)
(** {2 Global tables} *)

(** General structure for register a new global element than need 
 * to be save for the undo/restore mechanism *)
type register = {
  r_save : int -> unit;
  r_restore : int -> unit;
}

type global_stack = {
  mutable gs_init  : int; (*The number after load easycrypt_base*)
  mutable gs_count : int;
  mutable gs_reg   : register list;
}

let global_stack = {
  gs_init = 0;
  gs_count = 0;
  gs_reg   = [];
}

(** All global variable that need to be save, must call 
 * to add_register for register *)
let add_register s r =
  global_stack.gs_reg <-{ r_save = s; r_restore = r} :: global_stack.gs_reg

let save_init_global () = 
  global_stack.gs_init <- global_stack.gs_count


let save_global () =
  let nc = global_stack.gs_count + 1 in 
  List.iter (fun r -> r.r_save nc) global_stack.gs_reg;
  global_stack.gs_count <- nc

let restore_global  = function
  (*  We assume that 0 is to recover the initial state,
   * after to load easycrypt_base  *)
  | 0 -> 
    let k = global_stack.gs_init in
      List.iter (fun r -> r.r_restore k)  global_stack.gs_reg; 
      global_stack.gs_count <- k
  | k ->
    List.iter (fun r -> r.r_restore k)  global_stack.gs_reg; 
    global_stack.gs_count <- k



(*~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~*)
(** Save and restore functions for list *)
(*~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~*)

let list_save href lref n =
  if (!href = []) || not (!lref == snd(List.hd !href)) then
    href := (n,!lref) :: !href 

let rec list_restore href lref n = 
  match !href  with
  | [] -> lref := []
  | (i,_)::l when (i > n) -> begin href := l;list_restore href lref n end
  | (_,l)::_ -> lref := l


(* Warning the list [lref] should not contain reference *)
let add_list_register lref =
  let href = ref [] in
  add_register (list_save href lref) (list_restore href lref)

let init_register_list () = 
  let lref = ref [] in
  add_list_register lref;
  lref

let hash_list_restore key tbl href lref n =
   let old = !lref in
   list_restore href lref n;
   if not (old == !lref) then
     begin
       Hashtbl.clear tbl;
       List.iter (fun e -> Hashtbl.add tbl (key e) e) !lref
     end

let add_hash_list_register key tbl lref =
  let href = ref [] in
  add_register (list_save href lref) (hash_list_restore key tbl href lref)

let init_register_hash_list key  =
  let tbl = Hashtbl.create 17 in
  let lref = ref [] in
  add_hash_list_register key tbl lref;
  tbl, lref
(* Is not working, because restore compare the list and not de hash*)
(*let init_register_hash key =
  fst (init_register_hash_list key)*)



(*~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~*)
(** Save and restore functions for hash *)
(*~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~*)


let hash_save href tbl n =
(*TODO: Check if we really need to save *)
  (*if not (!lref == snd(List.hd !href)) then*)
    href := (n,(Hashtbl.copy tbl)) :: !href

let rec hash_restore href tbl n = 
  match !href  with
    | [] -> Hashtbl.clear tbl 
    | (i,_)::l when (i > n) -> begin href := l;hash_restore href tbl n end
    | (_,l)::_ -> begin Hashtbl.clear tbl; Hashtbl.iter (Hashtbl.add tbl) l;end


let init_register_hash () =
  let tbl = Hashtbl.create 17 in
  let href = ref [] in
  add_register (hash_save href tbl) (hash_restore href tbl);
  tbl

(** List of global declaration to export *)
type why_export =
  | WE_type of Ast.tdef
  | WE_cnst of Ast.const_body
  | WE_op of Ast.oper_body
  | WE_pred of Fol.predicate

let why_export = init_register_list ()

  

(* TODO merge ***_tbl ***_list *)

let type_tbl, type_list = init_register_hash_list (fun td -> td.t_name) 

(** Table of constant *)

let cnst_tbl, cnst_list = init_register_hash_list (fun cb -> cb.c_name) 

(** Table of operators *)

let op_tbl, op_list = init_register_hash_list (fun ob -> ob.op_name)

(* Is not working, no one use pop_list *)
(* let pop_tbl, pop_list = init_register_hash_list (fun ob -> ob.op_name) *)

let pop_tbl = init_register_hash ()

(* List of predicate *)

let pred_list = ref []

(*~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~*)
(** Save and restore functions for pred list.
 * We need to save the value, instead of the reference.  
 * Would be great if we have a generic function for save/restore that before 
 * push the structure in the list, apply a function like 'getValue' for 
 * remove reference .... *)
(*~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~*)
let _ = 
  let h = ref [] in

  let save n = 
    h := (n,List.map (fun p -> p, Fol.opacity p) !pred_list) :: !h in

  let rec restore n =
    match !h  with
      | [] -> pred_list := []
      | (i,_)::l when (i > n) -> begin h := l;restore n end
      | (_,l)::_ ->
       pred_list := List.map (fun (p,b) -> Fol.set_opacity b p;p) l in

  add_register save restore

(* List of axioms *)

let axiom_list = ref []

(*~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~*)
(** Save and restore functions for axiom_list.
 * See comments below 'pred_list'*)
(*~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~*)
let axiom_h = ref []

let _ = 

  let save n = 
    axiom_h := (n,List.map (fun (s,(r,ax, w)) -> (s,(!r,ax,w))) !axiom_list) 
         :: !axiom_h in

  let rec restore n =
    match !axiom_h  with
      | [] -> axiom_list := []
      | (i,_)::l when (i > n) -> begin axiom_h := l;restore n end
      | (_,l)::_ ->
        axiom_list   :=  List.map (fun (s,(b,ax,w)) -> (s,(ref b, ax,w))) l in
  add_register save restore


let init_axiom_list () =
  List.assoc (global_stack.gs_init) !axiom_h

(** Table of adversaries *)

let adv_tbl = init_register_hash () (*(fun a -> a.adv_name)*)

(* List of probabilitic operators specifications *)

let pop_specs = init_register_list ()
let predefined_pop_specs = []

let pop_aspecs = init_register_list ()
let predefined_pop_aspecs = [] 
(* let pop_wpspecs = init_register_list () *)
(* let predefined_pop_wpspecs = [] *)

(** Table of games and their interfaces *)

let game_tbl = init_register_hash () (*(fun g -> g.g_name)*)
let igame_tbl = init_register_hash ()

(** The current game *)
type scope =
  | SC_Game  of game
  | SC_IGame of game_interface_body

let current_scope = ref (None : scope option)

let cur_game msg =
  match !current_scope with
    | Some (SC_Game g) -> g
    | _ -> bug "No current game for %s" msg

let cur_igame msg =
  match !current_scope with
    | Some (SC_IGame ig) -> ig
    | _ -> bug "No current game interface of %s" msg

(*~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~*)
(*~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~*)
(*~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~*)
(* Global state *)

(* TODO : move timeout in whyCmd *)
type state = {
  mutable withproof : bool;
  mutable timeout   : int;
}

let state = {
  withproof = true;
  timeout = 3;
}

let set_timeout n =
  state.timeout <- n

let get_timeout () =
  state.timeout

let get_num_instr () = global_stack.gs_count

let withproof () = state.withproof

let set_withproof b =
  state.withproof <- b

let change_withproof () =
  state.withproof <- not state.withproof;
  warning "Proof mode is now %s"
    (if state.withproof then "ON" else "OFF")


(*~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~*)
(** {2 Checking not defined string } *)

let primitive_types = 
  [ "unit", Tunit;  "int", Tint; "bool",Tbool; "real", Treal]


let check_not_type name pos =
  check_not_in_tbl "type" type_tbl name pos;
  check_not_in_list "type" primitive_types name pos

let check_not_constant name pos =
  check_not_in_tbl "constant" cnst_tbl name pos

let check_not_operator name pos =
  check_not_in_tbl "prob operator" pop_tbl name pos;
  check_not_in_tbl "operator" op_tbl name pos

let check_not_adv name pos =
  check_not_in_tbl "adversary" adv_tbl name pos

(*~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~*)
(** {2 Variable environment } *)

type venv = (string * var) list
type lvenv = (string * Fol.lvar) list

let add_venv_var venv name v = (name, v)::venv

let empty_venv () = []
let empty_lvenv () = []

let add_lvar lvenv name ty =
  let lv = Fol.logic_lvar name ty in
  let lvenv = add_venv_var lvenv name lv in
  lvenv, lv

let iter_lvenv f env = List.iter (fun (s, v) -> f s v) env

let game_venv game = game.g_vars

let fun_pre_venv fct =
  let venv = game_venv fct.f_game in
  List.fold_left (fun venv v -> add_venv_var venv v.v_name v) venv fct.f_param

let fun_post_venv fct =
  let venv = game_venv fct.f_game in
  let vres = fct.f_res in
  add_venv_var venv vres.v_name vres

let fun_local_venv f =
  let venv = fun_pre_venv f in
  let fd = EcTerm.fct_def f in
  List.fold_left (fun venv v -> add_venv_var venv v.v_name v) venv fd.f_local

let find_var venv s = List.assoc s venv

let find_lvar lvenv s = List.assoc s lvenv

let check_var venv name pos =
  (* check_not_constant name pos; (\* TODO: WHY? *\) *)
  check_not_in_list "variable" venv name pos

let add_var venv pos name t =
  check_var venv name pos;
  let v = EcTerm.mk_local name t pos in
  let venv = add_venv_var venv name v in
  venv, v

let find_cst name = Hashtbl.find cnst_tbl name 

let fresh_var venv name t =
  let rec aux i =
    let s = Format.sprintf "%s_%i" name i in
    try let _ = find_var venv s in aux (i+1) 
    with _ -> 
      try let _ = find_cst s in aux (i+1)
      with _ -> add_var venv dummy_pos s t in
  try let _ = find_var venv name in aux 0
  with _ ->
    try let _ = find_cst name in aux 0
    with _ -> add_var venv dummy_pos name t

let iter_venv f env = List.iter (fun (s, v) -> f s v) env

let eq_env env1 env2 =
  try
    let in_env env s _v = ignore (find_var env s) in
    iter_venv (in_env env1) env2; iter_venv (in_env env2) env1; true
  with Not_found -> false

let lvenv_of_venv venv side =
  List.map (fun (name, v) -> (name, Fol.lvar_of_var v side)) venv
(*~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~*)
(** {2 Findind things }
    * All these functions [find_xxx] can raise not found *)

let find_adv name pos =
  try Hashtbl.find adv_tbl name
  with _ -> pos_error pos "unknown adversary %s@." name

let iter_adv f = Hashtbl.iter f adv_tbl
let fold_adv f c = Hashtbl.fold f adv_tbl c


let find_primitive_type name =
  List.assoc name primitive_types

let find_type name pos =
  try Hashtbl.find type_tbl name
  with _ -> pos_error pos "unknown type %s@." name

let iter_types f = List.iter f (List.rev !type_list)
let fold_types f acc = List.fold_left f acc !type_list
let iter_cnst f = List.iter f (List.rev !cnst_list)
let fold_cnst f acc = List.fold_left f acc !cnst_list
let iter_ops f = List.iter f (List.rev !op_list)
let fold_ops f acc = List.fold_left f acc !op_list
let iter_axioms f = List.iter f (List.rev !axiom_list)

let find_predicate name = 
  List.find (fun pr -> name = Fol.predicate_name pr) !pred_list

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

(* Finding games and functions *)
let find_igame name = Hashtbl.find igame_tbl name

let find_game gname = Hashtbl.find game_tbl gname

let iter_game f = Hashtbl.iter f game_tbl
let fold_game f c = Hashtbl.fold f game_tbl c

(** @raise Not_found when the function name is not in the game. *)
let find_fct_game fct game = List.assoc fct game.g_functions

(** @raise Not_found when the function name is not registered. *)
let find_fct fctname = find_fct_game fctname (cur_game "find_fct")




(*~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~*)
(** {2 Add things in tables}
    * All these functions [add_xxx] first check if it is correct to add that name
    * in the environment, and raise PosError if not.
*)

let add_type tdef =
  let name = tdef.t_name in
  let pos = tdef.t_pos in
  check_not_type name pos;
  debug db_glob "add %a" PpAst.pp_type_def tdef;
  Hashtbl.add type_tbl name tdef;
  type_list := tdef :: !type_list;
  why_export := WE_type tdef :: !why_export

let add_cnst c =
  let name, pos = c.c_name, c.c_pos in
  check_not_constant name pos;
  debug db_glob "add %a" PpAst.pp_cnst_def c;
  Hashtbl.add cnst_tbl name c;
  cnst_list := c :: !cnst_list;
  why_export := WE_cnst c ::!why_export


(** @raise PosError if name is already defined with the same type. *)
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



let add_adv adv =
  let name, pos = adv.adv_name, adv.adv_pos in
  check_not_operator name pos;
  check_not_adv name pos;
  debug db_glob "add adversary : %a" PpAst.pp_adv_decl adv;
  Hashtbl.add adv_tbl name adv

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

let add_global pos name t =
  let game = cur_game "add_global" in
  check_not_operator name pos;
  check_not_in_list "function" game.g_functions name pos;
  check_not_in_list "global" game.g_vars name pos;
  let v = EcTerm.mk_global name t pos in
  game.g_vars <- (name,v) :: game.g_vars



let add_fct pos name params t_res body =
  let game = cur_game "add_fct" in
  check_not_operator name pos;
  check_not_in_list "function" game.g_functions name pos;
  check_not_in_list "global" game.g_vars name pos;
  let res = EcTerm.mk_local "res" t_res pos in
  let fct = { f_name = name; f_game = game;
              f_pos = pos; f_param = params;
              f_body = body; f_res = res;
              f_modify = EcTerm.Vset.elements (EcTerm.global_modified body);
              f_read = EcTerm.Vset.elements (EcTerm.global_read body)
            } in
  debug db_add_loc "add function : %s@." fct.f_name;
  game.g_functions <- (name, fct) :: game.g_functions;
  fct

let start_igame name pos =
  if !current_scope <> None then
    bug "already in a opened scope";
  check_not_in_tbl "igame" igame_tbl name pos;
  let ig =
    { gi_name      = name;
      gi_pos       = pos ;
      gi_functions = []  ; }
  in
    debug db_add_loc "[global start game interface: %s@." name;
    Hashtbl.add igame_tbl name ig;
    current_scope := Some (SC_IGame ig)

let close_igame () =
  let igame = cur_igame "close_igame" in
    igame.gi_functions <- List.rev (igame.gi_functions);
    debug db_glob "[global] end game interface: %s@." igame.gi_name;
    debug db_glob "%a@." PpAst.pp_igame igame;
    current_scope := None

let abort_igame () =
  try
    let igame = cur_igame "abort_igame" in
      debug db_glob "[global] abort game interface: %s@." igame.gi_name;
      Hashtbl.remove igame_tbl igame.gi_name;
      current_scope := None
  with _ -> ()

let start_game name interface pos =
  if !current_scope <> None then
    bug "already in a opened scope";
  check_not_in_tbl "game" game_tbl name pos;
  let g =
    let i = GI_Named interface in
      { g_name      = name;
        g_pos       = pos ;
        g_interface = i   ;
        g_vars      = []  ;
        g_functions = []  ;
      }
  in
    debug db_add_loc "[global] start game: %s@." name;
    Hashtbl.add game_tbl name g;
    current_scope := Some (SC_Game g)

let close_game () =
  let game = cur_game "close_game" in
  game.g_vars <- List.rev (game.g_vars);
  game.g_functions <- List.rev (game.g_functions);
  debug db_glob "[global] end game: %s@." game.g_name;
  debug db_glob "%a@." PpAst.pp_game game;
  current_scope := None

let abort_game () =
  try
    let game = cur_game "close_game" in
    debug db_glob "[global] abort game: %s@." game.g_name;
    Hashtbl.remove game_tbl game.g_name;
    current_scope := None
  with _ -> ()

(*~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~*)
(** {2 Initialisation} *)

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

(* All this function needs initialisation *)
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

let find_and_show_fct (gname,fname) =
  let g = 
    try find_game gname 
    with Not_found -> user_error "unknown game %s" gname in
  let f = 
    try find_fct_game fname g 
    with Not_found -> user_error "unknown function %s in game %s" fname gname in
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
