open Ast
open EcTerm

let assign_params p args =
  List.map2 (fun v a -> Sasgn(Ltuple[v],a)) p args

type zipper =
  | Zif1 of exp * stmt * stmt * zipper   (* Z(if e then [] else s1; s2) *)
  | Zif2 of exp * stmt * stmt * zipper   (* Z(if e then s1 else []; s2) *)
  | Zcons of instr * zipper             (* Z(i;[]) *)
  | Zempty                               (* [] *)

(*let rec unzip s z =
  match z with
  | Zif1(e,s2,s',z) -> unzip (Sif(e,s,s2)::s') z
  | Zif2(e,s1,s',z) -> unzip (Sif(e,s1,s)::s') z
  | Zcons(i,z) -> unzip (i::s) z
  | Zempty -> s *)

let rec zip_stmt s z =
  match s with
    | [] -> z
    | i::s -> zip_stmt s (Zcons(i,z))

(* f should be defined *)

let inline_fct venv vars f args =
  let fd = fct_def f in
  let venv = ref venv in
  let fresh v =
    let env, v' = Global.fresh_var !venv v.v_name v.v_type in
    venv := env; v' in
  let (dp,rp) = g_mk_renaming fresh f.f_param in
  let (dl,rl) = g_mk_renaming fresh fd.f_local in
  let init = assign_params dp args in
  let r = rp@rl in
  let stmt = rename_stmt r fd.f_def in
  let res =
    match fd.f_return with
      | Some res -> [Sasgn(vars,rename_exp r res)]
      | None -> [] in
  dp@dl, !venv, init@(stmt@res)

let rec inline env cond k s z =
  match s with
    | Sif(e,s1,s2)::s' -> inline env cond k s1 (Zif1(e,s2,s',z))
    | Scall(vars,f,args) :: s' when cond k vars f args ->
      let info,venv = env in
      let d', venv, sf = inline_fct venv vars f args in
      let z = zip_stmt sf z in
      inline ((k,d')::info, venv) cond (k+1) s' z
    | i::s' -> inline env cond (k+1) s' (Zcons(i,z))
    | [] -> unzip_inline env cond k [] z

and unzip_inline env cond k s z =
  match z with
    | Zif1(e,s2,s',z) -> inline env cond k s2 (Zif2(e,s,s',z))
    | Zif2(e,s1,s',z) -> inline env cond k s' (Zcons(Sif(e,s1,s),z))
    | Zcons(i,z) -> unzip_inline env cond k (i::s) z
    | Zempty ->
      let info, venv = env in
      List.rev info, venv, s

type cond = int -> lasgn -> fct -> exp list -> bool

type info = (int * Ast.vars_decl) list

let inline env cond s = inline ([],env) cond 0 s Zempty


(* TODO : move this in EcTerm *)
let rec as_defined_call cond s =
  match s with
    | [] -> false
    | Scall(_,f,_)::_ when is_defined_fct f && cond f -> true
    | Sif(_,s1,s2)::s ->
      as_defined_call cond s1 || as_defined_call cond s2 || 
        as_defined_call cond s
    | _::s -> as_defined_call cond s

let as_defined_call_in lf s =
  as_defined_call (fun f -> List.mem f.f_name lf) s

let as_defined_call  =
  as_defined_call (fun _ -> true)

let last_pos s =
  let rec aux k s =
    match s with
      | [] -> k
      | Sif(_,s1,s2)::s -> aux (aux (aux k s1) s2) s
      | _ :: s -> aux (k+1) s in
  let k = aux (-1) s in
  if k < 0 then raise Not_found
  else k





