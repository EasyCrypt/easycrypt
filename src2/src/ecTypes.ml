(* -------------------------------------------------------------------- *)
open EcUtils
open EcSymbols
open EcPath
open EcUidgen
(* -------------------------------------------------------------------- *)
type tybase = Tunit | Tbool | Tint | Treal | Tbitstring

let tyb_equal : tybase -> tybase -> bool = (==)

type ty =
  | Tbase   of tybase
  | Tunivar of EcUidgen.uid
  | Trel    of int
  | Ttuple  of ty Parray.t 
  | Tconstr of EcPath.path * ty Parray.t

type ty_decl = int * ty

(* -------------------------------------------------------------------- *)
let tunit      () = Tbase Tunit
let tbool      () = Tbase Tbool
let tint       () = Tbase Tint
let tbitstring () = Tbase Tbitstring

let tlist ty =
  Tconstr (EcCoreLib.list, Parray.of_array [| ty |])

let tmap domty codomty =
  Tconstr (EcCoreLib.map, Parray.of_array [| domty; codomty |])

(* -------------------------------------------------------------------- *)
let mkunivar () = Tunivar (EcUidgen.unique ())

let map f t = 
  match t with 
  | Tbase _ | Tunivar _ | Trel _ -> t
  | Ttuple lty -> Ttuple (Parray.map f lty)
  | Tconstr(p, lty) -> Tconstr(p, Parray.map f lty)

let fold f s = function
  | Tbase _ | Tunivar _ | Trel _ -> s
  | Ttuple lty -> Parray.fold_left f s lty
  | Tconstr(_, lty) -> Parray.fold_left f s lty

let sub_exists f t =
  match t with
  | Tbase _ | Tunivar _ | Trel _ -> false
  | Ttuple lty -> Parray.exists f lty
  | Tconstr (p, lty) -> Parray.exists f lty

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
exception UnBoundRel of int
exception UnBoundUni of EcUidgen.uid
exception UnBoundVar of EcUidgen.uid

let full_get_rel s i = try Parray.get s i with _ -> raise (UnBoundRel i) 

let full_inst_rel s =
  let rec subst t = 
    match t with
    | Trel i -> full_get_rel s i 
    | _ -> map subst t in
  subst 

let full_get_uni s id = 
  try Muid.find id s with _ -> raise (UnBoundUni id) 

let full_inst_uni s = 
  let rec subst t = 
    match t with
    | Tunivar id -> full_get_uni s id
    | _ -> map subst t in
  subst 

let occur_uni u = 
  let rec aux t = 
    match t with
    | Tunivar u' -> uid_equal u u'
    | _ -> sub_exists aux t in
  aux

(* -------------------------------------------------------------------- *)
let freshen (n : int) (ty : ty) =
  let vars = Parray.init n (fun _ -> mkunivar ()) in
    full_inst_rel vars ty

(* -------------------------------------------------------------------- *)
(* FIXME: does not compile anymore
let close su lty t =
  let count = ref (-1) in
  let fresh_rel () = incr count;!count in
  let lty, t = (Parray.map (Subst.uni su) lty, Subst.uni su t) in
  let rec gen sv t =
    match t with
    | Tbase _ -> sv, t 
    | Tunivar u ->
        (try sv, Muid.find u su with _ ->
          let r = fresh_rel () in
          let t = Trel("'a", r) in
          (Muid.add u t su, sv), t)
    | Trel _ -> assert false
    | Ttuple lty -> let s,lty = gens s lty in s, Ttuple(lty)
    | Tconstr(p, lty) -> let s,lty = gens s lty in s, Tconstr(p, lty)
  and gens s lt = 
    let s = ref s in
    let lt = Parray.map (fun t -> let s',t = gen !s t in s := s'; t) lt in
    !s, lt in
  let s, lt = gens (Muid.empty,Muid.empty) lty in
  let s, t = gen s t in
  let merge _ u1 u2 = 
    match u1, u2 with
    | Some u1, None -> Some (full_inst s u1)
    | None, Some _ -> u2 
    | _, _ -> assert false in
  let s = Muid.merge merge su (fst s), snd s in
  s, lt, t 
*)

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

and tyrexpr =
  | Rbool                                    (* flip               *)
  | Rinter    of tyexpr * tyexpr             (* interval sampling  *)
  | Rbitstr   of tyexpr                      (* bitstring sampling *)
  | Rexcepted of tyrexpr * tyexpr            (* restriction        *)
  | Rapp      of EcPath.path * tyexpr list   (* p-op. application  *)
