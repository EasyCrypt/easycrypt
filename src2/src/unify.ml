(* -------------------------------------------------------------------- *)
open Utils
open UidGen
open Types

exception TypeVarCycle of uid * ty

let check_cycle u t =
  if occur_uni u t then raise (TypeVarCycle(u, t))

exception UnificationFailure of ty * ty

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
    | Tvar(_, v1), Tvar(_, v2) when uid_equal v1 v2 -> s

    | Ttuple lt1, Ttuple lt2 ->
        if Parray.length lt1 <> Parray.length lt2 then 
          raise (UnificationFailure(t1,t2))
        else Parray.fold_left2 aux s lt1 lt2

    | Tconstr(p1, lt1), Tconstr(p2, lt2) when Path.equal p1 p2 ->
        if Parray.length lt1 <> Parray.length lt2 then
          raise (UnificationFailure(t1,t2))
        else Parray.fold_left2 aux s lt1 lt2

    | Tconstr(p, lt), t
    | t, Tconstr(p, lt) when Env.Ty.defined p env ->
        aux s t (Env.Ty.unfold p lt env)

    | _, _ -> raise (UnificationFailure(t1, t2)) in
  aux
