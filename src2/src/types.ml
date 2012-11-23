(* -------------------------------------------------------------------- *)
open Utils
open Symbols
open Path
open UidGen
(* -------------------------------------------------------------------- *)
type tybase = Tunit | Tbool | Tint | Treal

let tyb_equal : tybase -> tybase -> bool = (==)

type ty =
  | Tbase   of tybase
  | Tvar    of string * UidGen.uid
  | Tunivar of UidGen.uid
  | Trel    of string * int
  | Ttuple  of ty Parray.t 
  | Tconstr of Path.path * ty Parray.t

type ty_decl = int * ty
(* -------------------------------------------------------------------- *)
let tunit () = Tbase Tunit
let tbool () = Tbase Tbool
let tint  () = Tbase Tint

(* -------------------------------------------------------------------- *)
let mkunivar () = Tunivar (UidGen.unique ())

let map f t = 
  match t with 
  | Tbase _ | Tvar _ | Tunivar _ | Trel _ -> t
  | Ttuple lty -> Ttuple (Parray.map f lty)
  | Tconstr(p, lty) -> Tconstr(p, Parray.map f lty)

let fold f s = function
  | Tbase _ | Tvar _ | Tunivar _ | Trel _ -> s
  | Ttuple lty -> Parray.fold_left f s lty
  | Tconstr(_, lty) -> Parray.fold_left f s lty

let sub_exists f t =
  match t with
  | Tbase _ | Tvar _ | Tunivar _ | Trel _ -> false
  | Ttuple lty -> Parray.exists f lty
  | Tconstr (p, lty) -> Parray.exists f lty

exception UnBoundRel of int
exception UnBoundUni of UidGen.uid
exception UnBoundVar of UidGen.uid

let full_get_rel s i = try Parray.get s i with _ -> raise (UnBoundRel i) 

let full_inst_rel s =
  let rec subst t = 
    match t with
    | Trel(_, i) -> full_get_rel s i 
    | _ -> map subst t in
  subst 

let full_get_uni s id = 
  try Muid.find id s with _ -> raise (UnBoundUni id) 

let get_uni s id t = try Muid.find id s with _ -> t 

let full_inst_uni s = 
  let rec subst t = 
    match t with
    | Tunivar id -> full_get_uni s id
    | _ -> map subst t in
  subst 

let inst_uni s = 
  let rec subst t = 
    match t with
    | Tunivar id -> get_uni s id t
    | _ -> map subst t in
  subst 

let full_get_var s id = 
  try Muid.find id s with _ -> raise (UnBoundVar id) 

let full_inst_var s = 
  let rec subst t = 
    match t with
    | Tvar(_, id) -> full_get_var s id
    | _ -> map subst t in
  subst 

let full_inst (su,sv) = 
  let rec subst t = 
    match t with
    | Tvar(_, id) -> full_get_var sv id
    | Tunivar id -> full_get_uni su id
    | _ -> map subst t in
  subst

let occur_uni u = 
  let rec aux t = 
    match t with
    | Tunivar u' -> uid_equal u u'
    | _ -> sub_exists aux t in
  aux

let close su lty t =
  let count = ref (-1) in
  let fresh_rel () = incr count;!count in
  let lty, t = Parray.map (inst_uni su) lty, inst_uni su t in
  let rec gen ((su, sv) as s) t =
    match t with
    | Tbase _ -> s, t 
    | Tvar(n, v) -> 
        (try s, Muid.find v sv with _ ->
          let r = fresh_rel () in
          let t = Trel(n, r) in
          (su, Muid.add v t sv), t)
    | Tunivar u ->
        (try s, Muid.find u su with _ ->
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

type clone_info = {
    cl_path : Path.subst_path;
    cl_ty : ty_decl Mp.t;
  }


let clone_ty cl = 
  let rec aux = function
    | Tbase _ | Trel _ as t -> t
    | Tvar _ | Tunivar _ -> assert false 
    | Ttuple lty -> Ttuple (Parray.map aux lty)
    | Tconstr(p,lty) ->
        let lty = Parray.map aux lty in
        match try Some (Mp.find p cl.cl_ty) with _ -> None with
        | Some (n,tdef) ->
            assert (n = Parray.length lty);
            full_inst_rel lty tdef 
        | None -> 
            let p = Path.subst_path cl.cl_path p in
            Tconstr(p,lty) in
  aux





            
            
          
       
  
  

  


        

















(* -------------------------------------------------------------------- *)
type local = symbol * int

type lpattern =
  | LSymbol of local
  | LTuple  of local list

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
  | Rbool                                    (* flip               *)
  | Rinter    of tyexpr * tyexpr             (* interval sampling  *)
  | Rbitstr   of tyexpr                      (* bitstring sampling *)
  | Rexcepted of tyrexpr * tyexpr            (* restriction        *)
  | Rapp      of Path.path * tyexpr list (* p-op. application  *)
