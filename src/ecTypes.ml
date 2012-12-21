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

(* -------------------------------------------------------------------- *)
let tunit      = Tconstr(EcCoreLib.p_unit, [])
let tbool      = Tconstr(EcCoreLib.p_bool, [])
let tint       = Tconstr(EcCoreLib.p_int , [])
let tbitstring = Tconstr(EcCoreLib.p_bitstring, [])

let tlist ty =
  Tconstr (EcCoreLib.p_list, [ ty ])

(* -------------------------------------------------------------------- *)

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

module Tuni = struct
  let subst1 ((id, t) : uid * ty) =
    let rec aux = function
      | Tunivar id' when uid_equal id id' -> t
      | u -> map aux u in
    aux

  let subst (uidmap : ty Muid.t) =
    let rec aux = function
      | (Tunivar id) as t -> odfl t (Muid.find_opt id uidmap)
      | t -> map aux t in
    aux 

  let subst_dom uidmap = List.map (subst uidmap)

  let occur u = 
    let rec aux t = 
      match t with
      | Tunivar u' -> uid_equal u u'
      | _ -> sub_exists aux t in
    aux

  let rec fv_rec fv t = 
    match t with
    | Tunivar id -> Suid.add id fv 
    | _ -> fold fv_rec fv t 

  let fv = fv_rec Suid.empty

  let fv_sig (dom, codom) = 
    List.fold_left fv_rec (fv codom) dom


end

module Tvar = struct 
  let subst1 (id,t) = 
    let rec aux = function
      | Tvar id' when id_equal id id' -> t
      | u -> map aux u in
    aux

  let subst (s : ty Mid.t) =
    let rec aux = function
      | (Tvar id) as t -> odfl t (Mid.find_opt id s)
      | t -> map aux t in
    aux 

  let init lv lt = 
    assert (List.length lv = List.length lt);
    List.fold_left2 (fun s v t -> Mid.add v t s) Mid.empty lv lt

  let rec fv_rec fv t = 
    match t with
    | Tvar id -> Sid.add id fv 
    | _ -> fold fv_rec fv t 

  let fv = fv_rec Sid.empty

  let fv_sig (dom, codom) = 
    List.fold_left fv_rec (fv codom) dom

end
 

(* -------------------------------------------------------------------- *)
type pvar_kind = 
  | PVglob
  | PVloc 

type prog_var = 
    { pv_name : EcPath.path;
      pv_kind : pvar_kind }

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
  | Evar      of prog_var * ty                 (* module variable    *)
  | Eapp      of EcPath.path * tyexpr list * ty   (* op. application    *)
  | Elet      of lpattern * tyexpr * tyexpr       (* let binding        *)
  | Etuple    of tyexpr list                      (* tuple constructor  *)
  | Eif       of tyexpr * tyexpr * tyexpr         (* _ ? _ : _          *)

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
  | Einter (e1, e2)       -> Einter (fe e1, fe e2)
  | Ebitstr e             -> Ebitstr (fe e)
  | Eexcepted (e1, e2)    -> Eexcepted (fe e1, fe e2)

(* -------------------------------------------------------------------- *)
module Esubst = struct 

  let mapty onty = 
    let rec aux e = e_map onty aux e in
    aux 

  let uni (uidmap : ty Muid.t) = mapty (Tuni.subst uidmap)

end

(* -------------------------------------------------------------------- *)
module Dump = struct
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

  let ex_dump pp =
    let rec ex_dump pp = function
      | Eint i ->
          EcDebug.single pp ~extra:(string_of_int i) "Eint"

      | Eflip ->
          EcDebug.single pp "Eflip"

      | Einter (e1, e2) ->
          EcDebug.onhlist pp "Einter" ex_dump [e1; e2]
        
      | Ebitstr e ->
          EcDebug.onhlist pp "Ebitstr" ex_dump [e]

      | Eexcepted (e1, e2) ->
          EcDebug.onhlist pp "Eexcepted" ex_dump [e1; e2]

      | Elocal (x, ty) ->
          EcDebug.onhlist pp
            "Elocal" ~extra:(EcIdent.tostring x)
            ty_dump [ty]
        
      | Evar (x, ty) ->
          EcDebug.onhlist pp
            "Evar" ~extra:(EcPath.tostring x.pv_name)
            ty_dump [ty]

      | Eapp (p, args, ty) ->
          let aprinter pp =
            EcDebug.onhlist pp ~enum:true "Arguments" ex_dump args
          and tprinter pp =
            EcDebug.onhlist pp "Type" ty_dump [ty]
          in
            EcDebug.onseq pp "Eapp" ~extra:(EcPath.tostring p)
              (Stream.of_list [tprinter; aprinter])

      | Elet (p, e1, e2) ->
          let printers = [ex_dump^~ e1; ex_dump^~ e2] in
            EcDebug.onseq pp "Elet" (Stream.of_list printers)
        
      | Etuple es ->
          EcDebug.onhlist pp ~enum:true "Etuple" ex_dump es
        
      | Eif (c, e1, e2) ->
          EcDebug.onhlist pp "Eif" ex_dump [c; e1; e2]
    in
      fun e -> ex_dump pp e
end
