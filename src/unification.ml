(** Unification of type *)

open EcUtil
open Ast


exception TypeMismatch of type_exp * type_exp

let rec unify_type t1 t2 =
  debug db_type "[unification] unify_type: %a  ~~~ %a@."
    PpAst.pp_type_exp_d t1 PpAst.pp_type_exp_d t2;
  match t1, t2 with
    | Tunit, Tunit | Tint, Tint | Tbool, Tbool | Treal, Treal -> ()
    | Tbitstring k1, Tbitstring k2 ->
        if EcTerm.eq_exp k1 k2 then ()
        else raise (TypeMismatch (t1, t2))
    | Ttuple l1, Ttuple l2 ->
        if List.length l1 = List.length l2 then List.iter2 unify_type l1 l2
        else raise (TypeMismatch (t1, t2))
    | Tnamed { t_def = Some t }, _ -> unify_type t t2
    | _, Tnamed { t_def = Some t } -> unify_type t1 t
    | Tnamed tn1, Tnamed tn2 ->
        if tn1.t_name = tn2.t_name && 
          List.length tn1.t_poly = List.length tn2.t_poly then
          List.iter2 unify_type tn1.t_poly tn2.t_poly
        else raise (TypeMismatch (t1, t2))
  (* Types variables *)
    | Tvar v1, Tvar v2 when EcTerm.eq_tvar v1 v2 -> ()
    | Tvar {tv_def = Defined t'} , t -> unify_type t' t
    | t, Tvar {tv_def = Defined t'}  -> unify_type t t'
    | Tvar ({tv_def = Open} as td1), Tvar ({tv_def = Open} as td2) ->
      debug db_type "identifying type variable %a with %a@."
        PpAst.pp_tvar td2 PpAst.pp_tvar td1;
      td2.tv_def <- Defined (Tvar td1)
    | Tvar ({tv_def = Open} as td),  t
    | t, Tvar ({tv_def = Open} as td) ->
      debug db_type "instanciate type variable %s into %a@."
        td.tv_name PpAst.pp_type_exp t;
      td.tv_def <- Defined t
    | _, _ -> raise (TypeMismatch (t1, t2))

let unify_type t1 t2 =
  debug db_type "[Start unification] unify_type: %a  ~~~ %a@."
    PpAst.pp_type_exp_d t1 PpAst.pp_type_exp_d t2;
  unify_type t1 t2

let unify_type_list tl1 tl2 = 
  if List.length tl1= List.length tl2 then  List.iter2 unify_type tl1 tl2 else
    raise (TypeMismatch (Ttuple tl1, Ttuple tl2))

(** @raise PosError with the message when the types are not compatible. *)
let raise_unify_type t1 t2 pos msg =
  try unify_type t1 t2
  with TypeMismatch (_t1', _t2') ->
    pos_error pos "%s. Type '%a' is not compatible with type '%a'"
      msg PpAst.pp_type_exp_d t1 PpAst.pp_type_exp_d t2

let eq_type  = EcTerm.seq_type 


