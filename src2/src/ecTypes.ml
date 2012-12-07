(* -------------------------------------------------------------------- *)
open EcUtils
open EcSymbols
open EcIdent
open EcPath
open EcUidgen
(* -------------------------------------------------------------------- *)
type tybase = Tunit | Tbool | Tint | Treal | Tbitstring

let tyb_equal : tybase -> tybase -> bool = (==)

type ty =
  | Tbase   of tybase
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
let tunit      () = Tbase Tunit
let tbool      () = Tbase Tbool
let tint       () = Tbase Tint
let tbitstring () = Tbase Tbitstring

let tbitstring () = Tbase Tbitstring

let tlist ty =
  Tconstr (EcCoreLib.list, [ ty ])

let tmap domty codomty =
  Tconstr (EcCoreLib.map, [ domty; codomty ])

(* -------------------------------------------------------------------- *)
let mkunivar () = Tunivar (EcUidgen.unique ())

let map f t = 
  match t with 
  | Tbase _ | Tunivar _ | Tvar _ -> t
  | Ttuple lty -> Ttuple (List.map f lty)
  | Tconstr(p, lty) -> Tconstr(p, List.map f lty)

let fold f s = function
  | Tbase _ | Tunivar _ | Tvar _ -> s
  | Ttuple lty -> List.fold_left f s lty
  | Tconstr(_, lty) -> List.fold_left f s lty

let sub_exists f t =
  match t with
  | Tbase _ | Tunivar _ | Tvar _ -> false
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
      | (Tunivar id) as t -> odfl t (EcUidgen.Muid.tryfind id uidmap)
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
    | Tunivar id -> Muid.get t id s 
    | _ -> map subst t in
  subst 

let inst_uni_dom s = List.map (inst_uni s)
    
let inst_var s = 
  let rec subst t = 
    match t with 
    | Tvar id -> Mid.get t id s 
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
  | Eunit                                   (* unit literal      *)
  | Ebool   of bool                         (* bool literal      *)
  | Eint    of int                          (* int. literal      *)
  | Elocal  of EcIdent.t * ty               (* local variable    *)
  | Evar    of EcPath.path * ty             (* module variable   *)
  | Eapp    of EcPath.path * tyexpr list    (* op. application   *)
  | Elet    of lpattern * tyexpr * tyexpr   (* let binding       *)
  | Etuple  of tyexpr list                  (* tuple constructor *)
  | Eif     of tyexpr * tyexpr * tyexpr     (* _ ? _ : _         *)
  | Ernd    of tyrexpr                      (* random expression *)
(* FIXME : flatten this *)
and tyrexpr =
  | Rbool                                    (* flip               *)
  | Rinter    of tyexpr * tyexpr             (* interval sampling  *)
  | Rbitstr   of tyexpr                      (* bitstring sampling *)
  | Rexcepted of tyrexpr * tyexpr            (* restriction        *)
  | Rapp      of EcPath.path * tyexpr list   (* p-op. application  *)

let e_map ft fe fr e = 
  match e with 
  | Eunit | Ebool _  | Eint _ -> e 
  | Elocal (id, ty) -> Elocal(id,ft ty)
  | Evar(id,ty) -> Evar(id,ft ty)
  | Eapp(p,args) -> Eapp(p, List.map fe args)
  | Elet(lp,e1,e2) -> Elet(lp, fe e1, fe e2)
  | Etuple le -> Etuple(List.map fe le)
  | Eif(e1,e2,e3) -> Eif(fe e1, fe e2, fe e3)
  | Ernd r -> Ernd(fr r)

let re_map fe fr = function
  | Rbool -> Rbool
  | Rinter(e1,e2) -> Rinter(fe e1, fe e2)
  | Rbitstr e -> Rbitstr(fe e)
  | Rexcepted(e1,e2) -> Rexcepted(fr e1, fe e2)
  | Rapp(p, args) -> Rapp(p, List.map fe args)

module Esubst = struct 
  let uni (uidmap : ty EcUidgen.Muid.t) =
    let tuni = Subst.uni uidmap in
    let rec aux e = e_map tuni aux raux e 
    and raux r = re_map aux raux r in
    aux
end




