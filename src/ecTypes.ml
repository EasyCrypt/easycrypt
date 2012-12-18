(* -------------------------------------------------------------------- *)
open EcUtils
open EcSymbols
open EcIdent
open EcPath
open EcUidgen

(* -------------------------------------------------------------------- *)
type ty =
  | Tunivar of EcUidgen.uid
  | Tvar    of EcIdent.t
  | Ttuple  of ty list
  | Tconstr of EcPath.path * ty list 

type dom = ty list
type tysig = dom * ty 

type ty_decl = {
  td_params : EcIdent.t list;
  td_body   : ty
}

(* -------------------------------------------------------------------- *)
let ty_dump pp =
  let rec ty_dump pp = function
    | Tunivar i ->
        EcDebug.single pp ~extra:(string_of_int i) "Tunivar"

    | Tvar a ->
        EcDebug.single pp ~extra:(EcIdent.tostring a) "Tvar"

    | Ttuple tys ->
        EcDebug.onhlist pp "Ttuple" ty_dump tys

    | Tconstr (p, tys) ->
        let strp = EcPath.tostring p in
          EcDebug.onhlist pp ~extra:strp "Tconstr" ty_dump tys
  in
    fun ty -> ty_dump pp ty

(* -------------------------------------------------------------------- *)
let tunit      = Tconstr(EcCoreLib.p_unit, [])
let tbool      = Tconstr(EcCoreLib.p_bool, [])
let tint       = Tconstr(EcCoreLib.p_int , [])
let tbitstring = Tconstr(EcCoreLib.p_bitstring, [])

let tlist ty =
  Tconstr (EcCoreLib.p_list, [ ty ])

(* -------------------------------------------------------------------- *)
let mkunivar () = Tunivar (EcUidgen.unique ())

let map f t = 
  match t with 
  | Tunivar _ | Tvar _ -> t
  | Ttuple lty -> Ttuple (List.map f lty)
  | Tconstr(p, lty) -> Tconstr(p, List.map f lty)

let fold f s = function
  | Tunivar _ | Tvar _ -> s
  | Ttuple lty -> List.fold_left f s lty
  | Tconstr(_, lty) -> List.fold_left f s lty

let sub_exists f t =
  match t with
  | Tunivar _ | Tvar _ -> false
  | Ttuple lty -> List.exists f lty
  | Tconstr (p, lty) -> List.exists f lty

(* -------------------------------------------------------------------- *)
module Subst = struct
  let uni1 ((id, t) : uid * ty) =
    let rec uni1 = function
      | Tunivar id' when uid_equal id id' -> t
      | u -> map uni1 u
    in
      fun u -> uni1 u

  let uni (uidmap : ty EcUidgen.Muid.t) =
    let rec uni = function
      | (Tunivar id) as t -> odfl t (EcUidgen.Muid.find_opt id uidmap)
      | t -> map uni t
    in
      fun t -> uni t
end

(* -------------------------------------------------------------------- *)
exception UnBoundUni of EcUidgen.uid
exception UnBoundVar of EcIdent.t

let full_get_uni s id = 
  try Muid.find id s with _ -> raise (UnBoundUni id) 

let full_inst_uni s = 
  let rec subst t = 
    match t with
    | Tunivar id -> full_get_uni s id
    | _ -> map subst t in
  subst 

let inst_uni s = 
  let rec subst t = 
    match t with
    | Tunivar id -> odfl t (Muid.find_opt id s )
    | _ -> map subst t in
  subst 

let inst_uni_dom s = List.map (inst_uni s)
    
let inst_var s = 
  let rec subst t = 
    match t with 
    | Tvar id -> Mid.find_def t id s 
    | _ -> map subst t in
  subst

let init_substvar lv lt = 
  assert (List.length lv = List.length lt);
  List.fold_left2 (fun s v t -> Mid.add v t s) Mid.empty lv lt

let occur_uni u = 
  let rec aux t = 
    match t with
    | Tunivar u' -> uid_equal u u'
    | _ -> sub_exists aux t in
  aux

(* -------------------------------------------------------------------- *)
let init_unit params = 
    List.fold_left (fun s v -> Mid.add v (mkunivar ()) s) Mid.empty params 

let freshen (params : EcIdent.t list) (ty : ty) =
  let vars = init_unit params in
  inst_var vars ty 

let freshendom params dom = 
  let vars = init_unit params in
  List.map (inst_var vars) dom

let freshensig params (dom,codom) = 
  let vars = init_unit params in
  List.map (inst_var vars) dom, inst_var vars codom


(* -------------------------------------------------------------------- *)
type lpattern =
  | LSymbol of EcIdent.t
  | LTuple  of EcIdent.t list

type tyexpr =
  | Eint      of int                              (* int. literal       *)
  | Eflip                                         (* flip               *)
  | Einter    of tyexpr * tyexpr                  (* interval sampling  *)
  | Ebitstr   of tyexpr                           (* bitstring sampling *)
  | Eexcepted of tyexpr * tyexpr                  (* restriction        *)
  | Elocal    of EcIdent.t * ty                   (* local variable     *)
  | Evar      of EcPath.path * ty                 (* module variable    *)
  | Eapp      of EcPath.path * tyexpr list * ty   (* op. application    *)
  | Elet      of lpattern * tyexpr * tyexpr       (* let binding        *)
  | Etuple    of tyexpr list                      (* tuple constructor  *)
  | Eif       of tyexpr * tyexpr * tyexpr         (* _ ? _ : _          *)

let mk_var local p ty =
  if local then
    Elocal (EcPath.basename p, ty)
   else
    Evar (p, ty)

(* -------------------------------------------------------------------- *)
let ids_of_lpattern = function
  | LSymbol id -> [id] 
  | LTuple ids -> ids

let e_map ft fe e = 
  match e with 
  | Eint _ | Eflip -> e 
  | Elocal (id, ty)       -> Elocal (id, ft ty)
  | Evar (id, ty)         -> Evar (id, ft ty)
  | Eapp (p, args, ty)    -> Eapp (p, List.map fe args, ft ty)
  | Elet (lp, e1, e2)     -> Elet (lp, fe e1, fe e2)
  | Etuple le             -> Etuple (List.map fe le)
  | Eif (e1, e2, e3)      -> Eif (fe e1, fe e2, fe e3)
  | Einter (e1,e2)        -> Einter (fe e1, fe e2)
  | Ebitstr e             -> Ebitstr (fe e)
  | Eexcepted (e1, e2)    -> Eexcepted (fe e1, fe e2)

(* -------------------------------------------------------------------- *)
module Esubst = struct 
  let uni (uidmap : ty EcUidgen.Muid.t) =
    let rec aux e = e_map (Subst.uni uidmap) aux e in
      aux
end
