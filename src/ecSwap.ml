open Ast
open EcTerm

exception CanNotSwap of string
exception CanNotSwapWR of string

let msg s1 s2 m1r2 =
  Format.fprintf Format.str_formatter
    "can not swap statements@\n  %a@\nand@\n  %a@\nthey are not independent on %a"
    (PpAst.pp_stmt ~num:false) s1 (PpAst.pp_stmt ~num:false) s2
    PpAst.pp_vset m1r2;
  Format.flush_str_formatter ()


let can_swap s1 s2 =
  let m1, m2 = modified_stmt s1, modified_stmt s2 in
  let r1, r2 = read_stmt s1, read_stmt s2 in
  let m2r1 = Vset.inter m2 r1 in
  if not (Vset.is_empty m2r1) then raise (CanNotSwap (msg s1 s2 m2r1));
  let m1m2 = Vset.inter m1 m2 in
  if not (Vset.is_empty m1m2) then raise (CanNotSwap (msg s1 s2 m1m2));
  let m1r2 = Vset.inter m1 r2 in
  if not (Vset.is_empty m1r2) then raise (CanNotSwapWR (msg s1 s2 m1r2))

let independent s1 s2 =
  let m1, m2 = modified_stmt s1, modified_stmt s2 in
  let r1, r2 = read_stmt s1, read_stmt s2 in
  let m2r1 = Vset.inter m2 r1 in
  let m1m2 = Vset.inter m1 m2 in
  let m1r2 = Vset.inter m1 r2 in
  if not (Vset.is_empty m2r1 && Vset.is_empty m1m2  && Vset.is_empty m1r2) 
  then false else true



let rec subst_in_instr excep subst instr =
  match instr with
    | Sif (b,s_then,s_else) ->
      let b = Fol.change_vars_in_var_exp subst b in
      let s_then = subst_in_stmt excep subst s_then in
      let s_else = subst_in_stmt excep subst s_else in
      Sif (b,s_then,s_else)
    | Scall (x,f,args) -> 
      let read_f = global_read_fct f in
      if (Vset.exists (fun v -> match subst v with None -> false | _ -> true ) read_f)
      then raise (CanNotSwap excep);
      let args = List.map (Fol.change_vars_in_var_exp subst) args in
      Scall (x,f,args)
    | Sasgn (Ltuple vs,e) ->
      let e = Fol.change_vars_in_var_exp subst e in
      Sasgn (Ltuple vs, e)
    | Sasgn _ -> raise (CanNotSwap excep)
    | Swhile (e,s) -> 
      let e = Fol.change_vars_in_var_exp subst e in
      let s = subst_in_stmt excep subst s in
      Swhile (e,s)
    | Sassert b ->
      let b = Fol.change_vars_in_var_exp subst b in
      Sassert b
and subst_in_stmt excep subst stmt =
  List.map (subst_in_instr excep subst) stmt

(*
 * swap_stmt tries further to swap *assignment* statements 
 *)
let swap_stmt (s1:Ast.stmt) (s2:Ast.stmt) =
  try can_swap s1 s2; s2
  with CanNotSwapWR excep -> 
    let push s instr = 
      match instr with
        | Sasgn (Ltuple [v],e) when EcTerm.is_var_exp e ->
          subst_in_stmt excep (fun x -> if EcTerm.eq_var x v then Some e else None) s
        | _ -> 
          try can_swap [instr] s2; s2 
          with CanNotSwapWR excep -> raise (CanNotSwap excep)
    in
    List.fold_left push s2 (List.rev s1)


    
let swap start length delta s =
  if start < 0 then raise (CanNotSwap "first instruction starts at position 1");
  let ls = List.length s in
  let last = start + length - 1 in
  if ls < start + length - 1 then
    raise (CanNotSwap
             (Format.sprintf "last position %i is out of the code" last));
  if (if delta < 0 then start < -delta else ls < last + delta) then
    raise
      (CanNotSwap
         (Format.sprintf
            "Can not move instructions %i to %i of %i, %i is to large"
            start last delta delta));
  let hd, s2 = EcUtil.list_shop start s in
  let to_move, tl = EcUtil.list_shop length s2 in
  if delta < 0 then
    let hd, sw = EcUtil.list_shop (List.length hd + delta) hd in
    let to_move = swap_stmt sw to_move in
    List.flatten [hd; to_move; sw; tl]
  else
    let sw, tl = EcUtil.list_shop delta tl in
    let sw = swap_stmt to_move sw in
    List.flatten [hd; sw; to_move; tl]

let pop n s =
  let len = List.length s in
  swap (len - 1) 1 (-n) s

let push n s = swap 0 1 n s

let pg_swap_fct info s =
  let s = List.rev s in
  let s =
    match info with
      | AstLogic.SKpop k -> pop k s
      | AstLogic.SKpush k -> push k s
      | AstLogic.SKswap (start, length, delta) -> swap start length delta s in
  List.rev s


