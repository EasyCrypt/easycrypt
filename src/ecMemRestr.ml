open EcUtils
open EcPath
open EcMaps
open EcAst
open EcCoreMemRestr
open EcCoreModules
open EcCoreSubst
open EcTypes
open EcCoreFol
open EcEnv

module Uses = struct
  let empty =
    { us_calls  = Sx.empty
    ; us_reads  = Sx.empty
    ; us_writes = Sx.empty }


  let union us1 us2 =
    { us_calls  = Sx.union us1.us_calls us2.us_calls
    ; us_reads  = Sx.union us1.us_reads  us2.us_reads
    ; us_writes = Sx.union us1.us_writes us2.us_writes }

  let add_call uses f = { uses with us_calls = Sx.add f uses.us_calls }

  let norm env uses =
    let norm_sx = Sx.map (NormMp.norm_xpv env) in
    let nuses = ref
      { us_calls  = Sx.empty
      ; us_reads  = norm_sx uses.us_reads
      ; us_writes = norm_sx uses.us_writes
      }
    in

    let add_uses uses =
      nuses :=
        { !nuses with
          us_reads  = Sx.union !nuses.us_reads  (norm_sx uses.us_reads);
          us_writes = Sx.union !nuses.us_writes (norm_sx uses.us_writes) }
    in

    let done_ = ref Sx.empty in
    let rec on_calls f =
      let f = NormMp.norm_xfun env f in
      if Sx.mem f !done_ then ()
      else begin
        done_ := Sx.add f !done_;
        match (Fun.by_xpath f env).f_def with
        | FBdef fd ->
          add_uses fd.f_uses;
          Sx.iter on_calls fd.f_uses.us_calls
        | FBalias _ -> assert false
        | FBabs _ -> nuses := add_call !nuses f
     end
    in

    Sx.iter on_calls uses.us_calls;
    !nuses

  let to_mem_restr params uses =
    let c = mr_globals (Sx.union uses.us_reads uses.us_writes) in
    let abs = mr_globfuns params uses.us_calls in
    mr_union c abs

  let to_type env params uses =
    let sx = Sx.union uses.us_reads uses.us_writes in
    let sx = Sx.elements sx in
    let c = List.map (fun x -> Var.by_xpath x env) sx in
    let abs = Sx.elements uses.us_calls in
    let abs = List.map (fun xp -> tglob (functor_fun params xp)) abs in
    ttuple (c @ abs)

  let to_form env params uses mem =
    let sx = Sx.union uses.us_reads uses.us_writes in
    let sx = Sx.elements sx in
    let c = List.map (fun x -> f_pvar (pv_glob x) (Var.by_xpath x env) mem) sx in
    let abs = Sx.elements uses.us_calls in
    let abs = List.map (fun xp -> f_glob (functor_fun params xp) mem) abs in
    f_tuple (c @ abs)

end

let funs_uses_core env params fs =
  let env = EcEnv.Mod.bind_params params env in
  let on_fun uses f =
    let f = NormMp.norm_xfun env f in
    let fun_ = Fun.by_xpath f env in
    match fun_.f_def with
    | FBdef fd  -> Uses.union uses (Uses.norm env fd.f_uses)
    | FBalias _ -> assert false
    | FBabs _   -> Uses.add_call uses f
  in
  let fuses = List.fold_left on_fun Uses.empty fs in
  env, fuses

let ff_norm_restr env ff = 
  let _, fuses = funs_uses_core env ff.ff_params [ff.ff_xp] in
  Uses.to_mem_restr ff.ff_params fuses

let ff_norm env ff mem =
  let _, fuses = funs_uses_core env ff.ff_params [ff.ff_xp] in
  Uses.to_form env ff.ff_params fuses mem

let ff_norm_ty env ff =
  let _, fuses = funs_uses_core env ff.ff_params [ff.ff_xp] in
  Uses.to_type env ff.ff_params fuses

let funs_uses_mr env params fs =
  let env, fuses = funs_uses_core env params fs in
  let mer = Uses.to_mem_restr params fuses in
  env, mer

let fun_uses_mr env f =
  snd (funs_uses_mr env [] [f])

let module_uses env mp omty =
  let me, _ = EcEnv.Mod.by_mpath mp env in

  let params, body =
    match omty with
    | None -> me.me_params, me.me_sig_body
    | Some mty ->
        let sig_ = EcEnv.ModTy.sig_of_mt env mty in
        sig_.mis_params, sig_.mis_body
  in

  let fs =
    let mp = m_apply mp (List.map (fun (x, _) -> mident x) params) in
    let on_fun (Tys_function funsig) = xpath mp funsig.fs_name in
    List.map on_fun body
  in
  params, snd (funs_uses_core env params fs)

let module_uses_mr env mp omty =
  let params, uses = module_uses env mp omty in
  Uses.to_mem_restr params uses

let module_uses_ty env mp omty =
  let params, uses = module_uses env mp omty in
  Uses.to_type env params uses

let module_uses_form env mp omty =
  let params, uses = module_uses env mp omty in
  Uses.to_form env params uses



let rec norm_mem_restr env mr =
  match mr with
  | Empty | All -> mr
  | Var x -> Var(NormMp.norm_xpv env x)
  | GlobFun ff ->
    let env = Mod.bind_params ff.ff_params env in
    let xp = NormMp.norm_xfun env ff.ff_xp in
    let fun_ = Fun.by_xpath xp env in
    begin match fun_.f_def with
    | FBdef fd ->
      let uses = Uses.norm env fd.f_uses in
      Uses.to_mem_restr ff.ff_params uses
    | FBalias _ -> assert false
    | FBabs _ -> mr_globfun ff.ff_params xp
    end
  | Union(s1, s2) -> mr_union (norm_mem_restr env s1) (norm_mem_restr env s2)
  | Inter(s1, s2) -> mr_inter (norm_mem_restr env s1) (norm_mem_restr env s2)
  | Diff (s1, s2) -> mr_diff  (norm_mem_restr env s1) (norm_mem_restr env s2)


let rec dump_mem_restr mr =
  match mr with
  | Empty -> "0"
  | All -> " * "
  | Var x -> Format.sprintf "%s" (EcPath.x_tostring x)
  | GlobFun ff -> 
    Format.sprintf "{%s => %s}" 
      (String.concat "," <| List.map (fun (x, mt) ->
        Format.sprintf "%s : %s" (EcIdent.tostring x) (EcPath.tostring mt.mt_name))
        ff.ff_params)
      (EcPath.x_tostring ff.ff_xp)
  | Inter (l, r) -> Format.sprintf "(%s ^ %s)" (dump_mem_restr l) (dump_mem_restr r)
  | Union (l, r) -> Format.sprintf "(%s | %s)" (dump_mem_restr l) (dump_mem_restr r)
  | Diff (l, r) -> Format.sprintf "(%s - %s)" (dump_mem_restr l) (dump_mem_restr r)


let rec norm_globs_restrs env f =
  let has_mod b =
    List.exists (fun (_,gty) ->
      match gty with GTmodty _ -> true | _ -> false) b in

  let norm_bind env (x, gty) =
    match gty with
    | GTty ty -> begin
      match ty.ty_node with
      | Tglob ff -> (x, GTty (ff_norm_ty env ff))
      | _ -> (x, gty)
      end
    | GTmodty (mt, mr) -> (x, (GTmodty (mt, norm_mem_restr env mr)))
    | GTmem _ -> (x, gty)
  in

  match f.f_node with
  | Fquant (q, bd, f) -> 
    let env = if has_mod bd then EcEnv.Mod.add_mod_binding bd env else env in
    f_quant q (List.map (norm_bind env) bd) (norm_globs_restrs env f)
  | Fglob (ff, m) -> ff_norm env ff m
  | Fif (f1, f2, f3) -> 
    f_if
      (norm_globs_restrs env f1)
      (norm_globs_restrs env f2)
      (norm_globs_restrs env f3)
  | Fmatch (b, fs, ty) ->
    f_match 
      (norm_globs_restrs env b)
      (List.map (norm_globs_restrs env) fs)
      ty
  | Flet (lv, f1, f2) ->
    f_let 
      lv 
      (norm_globs_restrs env f1)
      (norm_globs_restrs env f2)
  | Fapp (e, es) -> 
    f_app 
      (norm_globs_restrs env e)
      (List.map (norm_globs_restrs env) es)
      f.f_ty
  | Ftuple es -> 
      f_tuple (List.map (norm_globs_restrs env) es)
  | Fproj (e, i) -> 
    f_proj (norm_globs_restrs env e) i f.f_ty
  | _ -> f

let sup env ff =
  let env' = EcEnv.Mod.bind_params ff.ff_params env in
  (* The xpath is know to be normalised so it is abstract *)
  match (Fun.by_xpath ff.ff_xp env').f_def with
  | FBdef _ | FBalias _ -> assert false
  | FBabs oi ->
    let env, omr = funs_uses_mr env ff.ff_params oi.oi_calls in
    let omr = if List.length oi.oi_calls = 0 then mr_full else omr in
    let a = m_functor ff.ff_xp.x_top in
    let amr =
      let me, _ = Mod.by_mpath a env in
      match me.me_body with
      | ME_Alias _ | ME_Structure _ -> assert false
      | ME_Decl (_mty, mr) -> norm_mem_restr env mr
    in
    let mr = mr_inter amr omr in
    mr

let rec compare_modtype mty1 mty2 =
  let c = p_compare mty1.mt_name mty2.mt_name in
  if c <> 0 then c else
  let s, c = compare_modparams Fsubst.f_subst_id mty1.mt_params mty2.mt_params in
  if c <> 0 then c else
  let args2 = List.map (Fsubst.mp_subst s) mty2.mt_args in
  List.compare m_compare mty1.mt_args args2

and compare_modparams s mp1 mp2 =
  match mp1, mp2 with
  | [], [] -> s, 0
  | [], _ -> s, 1
  | _, [] -> s, -1
  | (x1, mt1) :: mp1, (x2, mt2) :: mp2 ->
    let s = Fsubst.f_bind_absmod s x2 x1 in
    let mt2 = Fsubst.mty_subst s mt2 in
    let c = compare_modtype mt1 mt2 in
    if c <> 0 then s, c else
    compare_modparams s mp1 mp2

(* We assume that the xpath in Var and GlobFun are in normal form *)
let rec compare_mem_restr mer1 mer2 =
  match mer1, mer2 with
  | Empty, Empty ->  0
  | Empty, _     -> -1
  | _, Empty     ->  1

  | All, All ->  0
  | All, _       -> -1
  | _, All       ->  1

  | Var x1, Var x2 -> x_compare x1 x2
  | Var _, _ -> -1
  | _, Var _ ->  1

  | GlobFun ff1, GlobFun ff2 ->
    compare_ff ff1 ff2
  | GlobFun _, _ -> -1
  | _, GlobFun _ ->  1

  | Union(s11, s12), Union(s21, s22) ->
    let c = compare_mem_restr s11 s21 in
    if c <> 0 then c else compare_mem_restr s12 s22
  | Union _, _ -> -1
  | _, Union _ -> 1

  | Inter(s11, s12), Inter(s21, s22) ->
    let c = compare_mem_restr s11 s21 in
    if c <> 0 then c else compare_mem_restr s12 s22
  | Inter _, _ -> -1
  | _, Inter _ -> 1

  | Diff(s11, s12), Diff(s21, s22) ->
    let c = compare_mem_restr s11 s21 in
    if c <> 0 then c else compare_mem_restr s12 s22

and compare_ff ff1 ff2 =
  let s, c = compare_modparams Fsubst.f_subst_id ff1.ff_params ff2.ff_params in
  if c <> 0 then c else
  let xp2 =Fsubst.x_subst s ff2.ff_xp in
  x_compare ff1.ff_xp xp2

module Mset = EcMaps.Map.Make (struct
  type t = mem_restr
  let compare = compare_mem_restr
end)

let ff_alpha_equal ff1 ff2 =
  compare_ff ff1 ff2 = 0

let ff_ntr_compare (ff1 : functor_fun) (ff2 : functor_fun) =
  match x_ntr_compare ff1.ff_xp ff2.ff_xp with
  | 0 ->
    List.compare
      (fun (id1, _) (id2, _) -> EcIdent.id_ntr_compare id1 id2)
      ff1.ff_params ff2.ff_params
  | n -> n

(* ---------------------------------------------------------------- *)
type meta = int
module Mmeta = Map.Make (struct type t = meta let compare = compare end)

type meta_var =
  | Meta of meta
  | Gvar of xpath

(* ---------------------------------------------------------------- *)

(* if sign then x \in s else x \nin s *)
type mem =
  { sign : bool
  ; var  : meta_var
  ; set  : mem_restr }

let mem sign (var:meta_var) (set:mem_restr) =
  { sign; var; set }

type meta_state =
  { value   : xpath option  (* The meta is known to be the given global *)
  ; mem     : bool Mset.t    (* mem[s] = b => if b then meta \in s else meta \nin s *)
  }

type var_state = bool Mset.t  (* true means the var is in the set (the key of the map) *)

let empty_var_state = Mset.empty

let empty_meta_state =
  { value = None
  ; mem = Mset.empty }

type local_state =
  { next : meta
  ; var  : var_state Mx.t
  ; meta : meta_state Mmeta.t
  ; todo : mem list
  ; unsat : bool }  (* true means unsat; false unknown *)

let empty_local_state =
  { next = 0
  ; var = Mx.empty
  ; meta = Mmeta.empty
  ; todo = []
  ; unsat = false
  }

let fresh_meta st =
  let next = st.next in
  next, { st with next = next + 1 }

let find_meta (st:local_state) (m:meta) =
  Option.value (Mmeta.find_opt m st.meta) ~default:empty_meta_state

let find_var (st:local_state) (m:xpath) =
  Option.value (Mx.find_opt m st.var) ~default:empty_var_state

let oget x = oget ~exn:Not_found x

let norm (st:local_state) mv =
  match mv with
  | Gvar _ -> mv
  | Meta m ->
      try
        let ms = Mmeta.find m st.meta in
        Gvar (oget ms.value)
      with Not_found -> mv

let set_unsat unsat st =
  { st with unsat = st.unsat || unsat}

exception SAT of local_state

let push (st:local_state) r =
  { st with todo = r :: st.todo }

let pushs (st:local_state) rs =
  { st with todo = List.rev_append rs st.todo }

let add_meta (st:local_state) m ms =
  { st with meta = Mmeta.add m ms st.meta }

(* Precondition m.value = None *)
let set_eq sign (m:meta) (v:xpath) (st:local_state) =
  let ms = find_meta st m in
  assert (ms.value = None);
  if sign then
    let todo =
      Mset.fold (fun s sign todo -> {sign; var = Gvar v; set = s} :: todo) ms.mem [] in
    let ms = { value = Some v; mem = Mset.empty } in
    let st = add_meta st m ms in
    pushs st todo
  else
    try
      let b = Mset.find (Var v) ms.mem in
      set_unsat b st
    with Not_found ->
      let ms = { ms with mem = Mset.add (Var v) false ms.mem } in
      add_meta st m ms

let rec set_mem sign mv a st =
  let s = GlobFun a in
  match mv with
  | Gvar x ->
    let vs = find_var st x in
    begin match Mset.find s vs with
    | sign' -> set_unsat (sign <> sign') st
    | exception Not_found ->
      let vs = Mset.add s sign vs in
      { st with var = Mx.add x vs st.var }
    end
  | Meta m ->
    let ms = find_meta st m in
    begin match ms.value with
    | Some x -> set_mem sign (Gvar x) a st
    | None ->
      begin match Mset.find s ms.mem with
      | sign' -> set_unsat (sign <> sign') st
      | exception Not_found ->
        let ms = { value = None; mem = Mset.add s sign ms.mem } in
        add_meta st m ms
      end
    end

let set_all sign mv st =
  let s = All in
  match mv with
  | Gvar _ -> set_unsat (not sign) st
  | Meta m ->
    let ms = find_meta st m in
    begin match ms.value with
    | Some _ -> set_unsat (not sign) st
    | None ->
      begin match Mset.find s ms.mem with
      | sign' -> set_unsat (sign <> sign') st
      | exception Not_found ->
        let ms = { value = None; mem = Mset.add s sign ms.mem } in
        add_meta st m ms
      end
    end


let add_adv env sign mv ff (st:local_state) =
  let st = set_mem sign mv ff st in
  if sign then
    (* x in ff -> x in sup ff *)
    let sup = sup env ff in
    push st (mem true mv sup)
  else
    let ff' =
      let a = m_functor ff.ff_xp.x_top in
      let me, _ = Mod.by_mpath a env in
      match me.me_body with
      | ME_Alias _ | ME_Structure _ -> assert false
      | ME_Decl (mty, _) ->
        let xp =
          let args = List.map (fun (x, _) -> mident x) mty.mt_params in
          xpath (m_apply a args) ff.ff_xp.x_sub in
        { ff_params = mty.mt_params; ff_xp = xp }
    in

    set_mem sign mv ff' st


let dump_var (v : meta_var) =
  match v with
  | Gvar x -> EcPath.x_tostring x
  | Meta m -> "v" ^ string_of_int m

let dump_mem r =
  if r.sign then
    Printf.sprintf "%s \\in %s" (dump_var r.var) (dump_mem_restr r.set) 
  else
    Printf.sprintf "%s \\notin %s" (dump_var r.var) (dump_mem_restr r.set) 

let rec solve ?(depth = 0) (env : env) (st : local_state) =
  if st.unsat then ( (*Printf.printf "%d: UNSAT\n" depth;*) ())
  else match st.todo with
  | [] -> raise (SAT st)
  | r :: todo ->
          (*
  Printf.printf "Processing %d: %s\n" depth (dump_mem r);
  Printf.printf "Todo: %s\n" (String.concat " <| " (List.map dump_mem todo));
  *)
    process depth env r {st with todo}

(* precondition st.unsat = false *)
and process depth (env : env) (r : mem) (st : local_state) =
  let sts =
    match r.set with
    | Empty -> [set_unsat r.sign st]
    | All -> [set_all r.sign r.var st]
    | Var v ->
      begin match norm st r.var with
      | Meta m -> [set_eq r.sign m v st]  (* add the fact that m =sign v *)
      | Gvar v' ->
        [set_unsat ((x_equal v v') <> r.sign) st]
      end
    | GlobFun ff -> [add_adv env r.sign r.var ff st]
    | Union (s1,s2) ->
      let r1 = { r with set = s1 } in
      let r2 = { r with set = s2 } in
      if r.sign then
        (* mv in s1 U s2 = mv in s1 || mv in s2 *)
        [push st r1; push st r2]
       else
         (* !(mv in s1 U s2) = !(mv in s1) && !(mv in s2) *)
         [pushs st [r1; r2]]
     | Diff (s1, s2) ->
       let r1 = { r with set = s1 } in
       let r2 = { r with sign = not r.sign; set = s2 } in
       if r.sign then
         (* mv in s1 \ s2 = mv in s1 && !mv in s2 *)
         [pushs st [r1; r2]]
       else
         (* !(mv in s1 \ s2) = !(mv in s1) || mv in s2 *)
         [push st r1; push st r2]
     | Inter (s1, s2) ->
       let r1 = { r with set = s1 } in
       let r2 = { r with set = s2 } in
       if r.sign then
         (* mv in s1 inter s2 = mv in s1 && mv in s2 *)
         [pushs st [r1; r2]]
       else
         (* !(mv in s1 inter s2) = !(mv in s1) || !(mv in s2) *)
         [push st r1; push st r2]
  in

  (*
  if List.length sts <> 1 then
      Printf.printf "SPLIT\n";
  *)
  List.iteri (fun i -> solve ~depth:(depth + i) env) sts


(* ------------------------------------------------------------------- *)
(* /!\ Precondition s1 and s2 should have been normalised *)
let core_subset env s1 s2 =
  (* add clause !(s1 subset s2)
     ------------------
     x \in s1 && x \nin s2
  *)
  let st = empty_local_state in
  let m, st = fresh_meta st in
  let st = pushs st [mem true (Meta m) s1; mem false (Meta m) s2] in
  try solve env st; true
  with SAT _ -> false

let subset env s1 s2 =
  let s1 = norm_mem_restr env s1 in
  let s2 = norm_mem_restr env s2 in

  core_subset env s1 s2

let disjoint env s1 s2 = subset env (Inter(s1, s2)) Empty

let equal env s1 s2 =
  let s1 = norm_mem_restr env s1 in
  let s2 = norm_mem_restr env s2 in
  (* FIXME try first to test is s1 = s2 module alpha *)
  core_subset env (Union (Diff(s1, s2), Diff(s2, s1))) Empty

let is_mem env sign x s =
  let st = empty_local_state in
  let s = norm_mem_restr env s in
  let st = push st (mem (not sign) (Gvar x) s) in
  try solve env st; true
  with SAT _ -> false
