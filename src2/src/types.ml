(* -------------------------------------------------------------------- *)
open Symbols
open Parsetree
open UidGen
(* -------------------------------------------------------------------- *)
type tybase = Tunit | Tbool | Tint | Treal

let tyb_equal : tybase -> tybase -> bool = (==)

type ty =
  | Tbase   of tybase
  | Tvar    of UidGen.uid
  | Tunivar of UidGen.uid
  | Trel    of int
  | Ttuple  of ty list
  | Tconstr of Path.path * ty list


(* -------------------------------------------------------------------- *)
let tunit () = Tbase Tunit
let tbool () = Tbase Tbool
let tint  () = Tbase Tint

(* -------------------------------------------------------------------- *)
let mkunivar () = Tvar (UidGen.unique ())

let map f t = 
  match t with 
  | Tbase _ | Tvar _ | Tunivar _ | Trel _ -> t
  | Ttuple lty -> Ttuple (List.map f lty)
  | Tconstr(p, lty) -> Tconstr(p, List.map f lty)

let fold f s = function
  | Tbase _ | Tvar _ | Tunivar _ | Trel _ -> s
  | Ttuple lty -> List.fold_left f s lty
  | Tconstr(_, lty) -> List.fold_left f s lty

let sub_exists f t =
  match t with
  | Tbase _ | Tvar _ | Tunivar _ | Trel _ -> false
  | Ttuple lty -> List.exists f lty
  | Tconstr (p, lty) -> List.exists f lty

exception UnBoundRel of int
exception UnBoundUni of UidGen.uid
exception UnBoundVar of UidGen.uid

let subst_rel s =
  let get i = try s.(i) with _ -> raise (UnBoundRel i) in
  let rec subst t = 
    match t with
    | Trel i -> get i 
    | _ -> map subst t in
  subst 

let subst_uni s = 
  let get id = try Muid.find id s with _ -> raise (UnBoundUni id) in
  let rec subst t = 
    match t with
    | Tunivar id -> get id
    | _ -> map subst t in
  subst 

let subst_var s = 
  let get id = try Muid.find id s with _ -> raise (UnBoundVar id) in
  let rec subst t = 
    match t with
    | Tvar id -> get id
    | _ -> map subst t in
  subst 

let occur_uni u = 
  let rec aux t = 
    match t with
    | Tunivar u' -> uid_equal u u'
    | _ -> sub_exists aux t in
  aux

let close s lty t =
  let count = ref (-1) in
  let fresh_rel () = incr count;!count in
  let rec gen ((su, sv) as s) t =
    match t with
    | Tbase _ -> s, t 
    | Tvar v -> 
        (try s, Muid.find v sv with _ ->
          let r = fresh_rel () in
          let t = Trel r in
          (su, Muid.add v t sv), t)
    | Tunivar u ->
        (try s, Muid.find u su with _ ->
          let r = fresh_rel () in
          let t = Trel r in
          (Muid.add u t su, sv), t)
    | Trel _ -> assert false
    | Ttuple lty -> let s,lty = gens s lty in s, Ttuple(lty)
    | Tconstr(p, lty) -> let s,lty = gens s lty in s, Tconstr(p, lty)
  and gens s lt = 
    let s,r = 
      List.fold_left 
        (fun (s,r) t -> let s,t = gen s t in s, (t::r)) (s,[]) lt in
    s, List.rev r in
  let s, lt = gens (s,Muid.empty) lty in
  let s, t = gen s t in
  s, lt, t 


  


        

















(* -------------------------------------------------------------------- *)
type local = symbol * int

type tyexpr =
  | Eunit                                   (* unit literal      *)
  | Ebool   of bool                         (* bool literal      *)
  | Eint    of int                          (* int. literal      *)
  | Elocal  of local * ty                   (* local variable    *)
  | Eident  of Path.path * ty               (* symbol            *)
  | Eapp    of Path.path * tyexpr list      (* op. application   *)
  | Elet    of lpattern * tyexpr * tyexpr   (* let binding       *)
  | Etuple  of tyexpr list                  (* tuple constructor *)
  | Eif     of tyexpr * tyexpr * tyexpr     (* _ ? _ : _         *)
  | Ernd    of tyrexpr                      (* random expression *)

and tyrexpr =
  | Rbool                                   (* flip               *)
  | Rinter    of tyexpr * tyexpr            (* interval sampling  *)
  | Rbitstr   of tyexpr                     (* bitstring sampling *)
  | Rexcepted of tyrexpr * tyexpr           (* restriction        *)
  | Rapp      of Path.path * tyexpr list    (* p-op. application  *)
