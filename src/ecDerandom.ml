open EcUtil
open Ast

(** {2 Derandomization } *)

let derandomize_rnd_var venv ov r =
  match ov with
  | Some (Ltuple [x]) -> 
      Global.fresh_var venv x.v_name x.v_type
  | _ -> 
      Global.fresh_var venv "r" (EcTerm.type_of_random r)
  
let derandomize_rnd venv ov r =
  if EcTerm.is_cnst_rnd r then
    let venv, x = derandomize_rnd_var venv ov r in
    venv, [Sasgn(Ltuple [x],Ernd r)], Ebase x
  else cannot_apply 
    "derandomize" "encountered non-constant random expression %a"
         PpAst.pp_random r

let rec derandomize_exp venv ov e =
  match e with
  | Ecnst _ | Ebase _  -> (venv,[],e)
  | Ernd r -> derandomize_rnd venv ov r
  | Epair l ->
      let (venv, rargs,args) = 
        List.fold_right 
          (fun e (venv, rargs,args) ->
            let (venv, r,e) = derandomize_exp venv None e in
            (venv, r@rargs,e::args)) 
          l (venv, [],[]) 
      in venv, rargs, Epair args
  | Eapp (op, args) ->
      let (venv, rargs,args) = 
        List.fold_right 
          (fun e (venv, rargs,args) ->
             let (venv, r,e) = derandomize_exp venv None e in
             (venv, r@rargs,e::args)) 
          args (venv, [],[]) 
      in venv, rargs, Eapp(op,args)
  | Eif (b, e1, e2) ->
      let (venv, rb,b) = derandomize_exp venv None b in
      let (venv, r1,e1) = derandomize_exp venv None e1 in
      let (venv, r2,e2) = derandomize_exp venv None e2 in
      venv, rb@r1@r2, Eif(b,e1,e2)
  | Elet (xs,e1,e2) ->
      let (venv,r1,e1) = derandomize_exp venv None e1 in
      let (venv,r2,e2) = derandomize_exp venv None e2 in
      venv, r1@r2, Elet(xs,e1,e2)

let rec derandomize_instr venv i =
  match i with
  | Sasgn(x,e) -> 
      let venv, sr, e = derandomize_exp venv (Some x) e in
      venv, sr,Sasgn(x,e)
  | Scall (x,f,args) -> 
      let rec do_exp venv l = match l with
        | [] -> venv, [], []
        | e::l -> 
            let venv, r,e = derandomize_exp venv None e in
            let venv, lr, le = do_exp venv l in
              venv, (r::lr), (e::le)
      in
      let venv, r, args = do_exp venv args in
        venv, List.flatten r, Scall(x,f,args)
  (* well-typed guards do not contain random expressions *)
  | Sif(e,s1,s2) ->
      let venv, sre,e = derandomize_exp venv None e in
      let venv, sr1,s1 = derandomize_stmt venv s1 in
      let venv, sr2,s2 = derandomize_stmt venv s2 in
      venv, sre@sr1@sr2,Sif(e,s1,s2)
  (* well-typed guards do not contain random expressions *)
  | Sassert e -> 
    let venv, sre,e = derandomize_exp venv None e in
    venv, sre, Sassert e
  | Swhile (e,s) ->
    let venv, sr, s = derandomize_stmt venv s in
    venv, [], Swhile (e,sr@s)

and derandomize_stmt venv s =
  let rec do_stmt venv l = match l with
    | [] -> venv, [], []
    | s::l -> 
        let venv, r, s = derandomize_instr venv s in
        let venv, lr, ls = do_stmt venv l in
          venv, (r::lr), (s::ls)
  in
  let venv, r, s = do_stmt venv s in
  venv, List.flatten r, s


	    






