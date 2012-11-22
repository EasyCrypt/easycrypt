(* -------------------------------------------------------------------- *)
open UidGen
open Types

exception TypeVarCycle of uid * ty

let check_cycle u t =
  if occur_uni u t then raise (TypeVarCycle(u, t))

exception CanNotUnify of ty * ty

(** TODO implement this once scope are done *)
let get_type env p = assert false
let is_def_type env p = assert false

let unfold_type env p lt =
  let n,t = get_type env p in
  let lt = Array.of_list lt in
  assert (n = Array.length lt);
  subst_rel lt t 

let unify env = 
  let repr s t = 
    match t with
    | Tunivar id -> (try Muid.find id s with _ -> t)
    | _ -> t in
  let bind s u t = 
    assert (not (Muid.mem u s));
    check_cycle u t; 
    let rec subst = function
      | Tunivar u' when uid_equal u u' -> t 
      | t' -> Types.map subst t' in
    Muid.add u t (Muid.map subst s) in
  let rec aux s t1 t2 = 
    let t1, t2 = repr s t1, repr s t2 in
    match t1, t2 with
    | Trel _, _ -> assert false
    | _, Trel _ -> assert false
    | Tunivar u1, Tunivar u2 -> 
        if uid_equal u1 u2 then s 
        else bind s u1 t2
    | Tunivar id, t | t, Tunivar id -> bind s id t 
    | Tbase b1, Tbase b2 when tyb_equal b1 b2 -> s
    | Tvar v1, Tvar v2 when uid_equal v1 v2 -> s
    | Ttuple lt1, Ttuple lt2 ->
        if List.length lt1 = List.length lt2 then 
          raise (CanNotUnify(t1,t2))
        else List.fold_left2 aux s lt1 lt2
    | Tconstr(p1, lt1), Tconstr(p2,lt2) when Path.path_equal p1 p2 ->
        if List.length lt1 = List.length lt2 then
          raise (CanNotUnify(t1,t2))
        else List.fold_left2 aux s lt1 lt2
    | Tconstr(p, lt), t when is_def_type env p ->
        aux s (unfold_type env p lt) t
    | t, Tconstr(p, lt) when is_def_type env p ->
        aux s t (unfold_type env p lt)
    | _, _ -> raise (CanNotUnify(t1,t2)) in
  aux
