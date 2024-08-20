(* -------------------------------------------------------------------- *)
open EcSymbols
open EcUtils
open EcAst
open EcTypes

module Msym = EcSymbols.Msym

(* -------------------------------------------------------------------- *)
type memory = EcAst.memory

let mem_equal = EcAst.mem_equal

(* -------------------------------------------------------------------- *)
type proj_arg = EcAst.proj_arg

let mk_lmt lmt_name lmt_decl lmt_proj =
  { lmt_name;
    lmt_decl;
    lmt_proj;
    lmt_ty = ttuple (List.map ov_type lmt_decl);
    lmt_n  = List.length lmt_decl;
  }

type memtype = EcAst.memtype

let lmt_hash = EcAst.lmt_hash

let mt_fv = EcAst.mt_fv

let lmt_equal = EcAst.lmt_equal

let mt_equal_gen = EcAst.mt_equal_gen

let mt_equal = EcAst.mt_equal

let mt_iter_ty f (Lmt_concrete mt) =
  oiter (fun lmt -> List.iter (fun v -> f v.ov_type) lmt.lmt_decl) mt

(* -------------------------------------------------------------------- *)
type memenv = EcAst.memenv

let me_equal_gen = EcAst.me_equal_gen
let me_equal = EcAst.me_equal

(* -------------------------------------------------------------------- *)
let memory   (m,_) = m
let memtype  (_,mt) = mt

(* -------------------------------------------------------------------- *)
exception DuplicatedMemoryBinding of symbol

(* -------------------------------------------------------------------- *)
let empty_local_mt ~witharg =
  let lmt = mk_lmt (if witharg then Some arg_symbol else None) [] Msym.empty in
  Lmt_concrete (Some lmt)

let empty_local ~witharg (me : memory) =
  me, empty_local_mt ~witharg

let abstract_mt = Lmt_concrete None
let abstract (me:memory) = me, abstract_mt

(* -------------------------------------------------------------------- *)
let is_bound_lmt x lmt =
  Some x = lmt.lmt_name || Msym.mem x lmt.lmt_proj

let is_bound x (Lmt_concrete mt) =
  match mt with
  | None -> false
  | Some lmt -> is_bound_lmt x lmt

let lookup (x : symbol) (Lmt_concrete mt : memtype)
  : (variable * proj_arg option * int option) option
=
  match mt with
  | None -> None
  | Some lmt ->
    if lmt.lmt_name = Some x then
      Some ({v_name = x; v_type = lmt.lmt_ty}, None, None)
    else
      match Msym.find_opt x lmt.lmt_proj with
      | Some (i,xty) ->
        if lmt.lmt_n = 1 then
          Some ({ v_name = odfl x lmt.lmt_name; v_type = xty}, None, None)
        else
          let v = { v_name = x; v_type = xty } in
          let pa =
            if lmt.lmt_name = None then None
            else Some { arg_ty = lmt.lmt_ty; arg_pos = i; } in
          Some(v, pa, Some i)
      | None -> None

let lookup_me x me = lookup x (snd me)

let is_bound_pv pv me = match pv with
  | PVglob _ -> false
  | PVloc id -> is_bound id me

(* -------------------------------------------------------------------- *)
let bindall_lmt (vs : ovariable list) lmt =
  let n = List.length lmt.lmt_decl in
  let add_proj mt_proj i v =
    match v.ov_name with
    | None -> mt_proj
    | Some x ->
        if lmt.lmt_name = Some x then raise (DuplicatedMemoryBinding x);
        let merger = function
          | Some _ -> raise (DuplicatedMemoryBinding x)
          | None   -> Some (n + i,v.ov_type)
        in Msym.change merger x mt_proj
  in
  let mt_decl = lmt.lmt_decl @ vs in
  let mt_proj = List.fold_lefti add_proj lmt.lmt_proj vs in
  mk_lmt lmt.lmt_name mt_decl mt_proj

let bindall_mt (vs : ovariable list) (Lmt_concrete mt : memtype) : memtype =
  match mt with
  | None -> assert false
  | Some lmt -> Lmt_concrete (Some (bindall_lmt vs lmt))

let bindall (vs : ovariable list) ((m,mt) : memenv) : memenv =
  m, bindall_mt vs mt

let bindall_fresh (vs : ovariable list) ((m, Lmt_concrete mt) : memenv) =
  match mt with
  | None -> assert false
  | Some lmt ->
    let is_bound x m = Some x = lmt.lmt_name || Msym.mem x m in
    let fresh_pv m v =
      match v.ov_name with
      | None   -> m, v
      | Some name ->
          let name =
            if not(is_bound name m) then name
            else
              let rec for_idx idx =
                let x = Printf.sprintf "%s%d" name idx in
                if is_bound x m then for_idx (idx+1)
                else x in
              for_idx 0 in
          Msym.add name (-1,v.ov_type) m, { v with ov_name = Some name } in
    let _, vs = List.map_fold fresh_pv lmt.lmt_proj vs in
    let lmt = bindall_lmt vs lmt in
    (m, Lmt_concrete (Some lmt)), vs

let bind_fresh v me =
  let me, vs = bindall_fresh [v] me in
  me, as_seq1 vs

(* -------------------------------------------------------------------- *)
let mt_subst st ((Lmt_concrete o) as arg) =
  match o with
  | None -> arg
  | Some mt ->
    let decl = mt.lmt_decl in
    let decl' =
      if st == identity then decl
      else
        List.Smart.map (fun vty ->
            let ty' = st vty.ov_type in
            if ty_equal vty.ov_type ty' then vty else {vty with ov_type = ty'}) decl in
    if decl ==(*phy*) decl' then
      arg
    else
      let lmt = mk_lmt
          mt.lmt_name decl' (Msym.map (fun (i,ty) -> i, st ty) mt.lmt_proj) in
      Lmt_concrete (Some lmt)

let me_subst sm st (m,mt as me) =
  let m' = EcIdent.Mid.find_def m m sm in
  let mt' = mt_subst st mt in
  if m' == m && mt' == mt then me else
    (m', mt')

(* -------------------------------------------------------------------- *)
let for_printing (Lmt_concrete mt) =
  match mt with
  | None -> None
  | Some mt -> Some (mt.lmt_name, mt.lmt_decl)

(* -------------------------------------------------------------------- *)
let rec pp_list sep pp fmt xs =
  let pp_list = pp_list sep pp in
    match xs with
    | []      -> ()
    | [x]     -> Format.fprintf fmt "%a" pp x
    | x :: xs -> Format.fprintf fmt "%a%(%)%a" pp x sep pp_list xs

let dump_memtype (Lmt_concrete mt) =
  match mt with
  | None -> "abstract"
  | Some mt ->
    let pp_vd fmt v =
      Format.fprintf fmt "@[%s: %s@]"
        (odfl "_" v.ov_name)
        (EcTypes.dump_ty v.ov_type)
    in
    Format.asprintf "@[{@[%a@]}@]" (pp_list ",@ " pp_vd) mt.lmt_decl

(* -------------------------------------------------------------------- *)
let get_name s p (_, Lmt_concrete mt) =
  match mt with
  | None -> None
  | Some mt -> begin
      match p with
      | None -> Some s
      | Some i ->
        if Some s = mt.lmt_name then
          omap fst (List.find_opt (fun (_,(i',_)) -> i = i') (Msym.bindings mt.lmt_proj))
        else
          None
    end

(* -------------------------------------------------------------------- *)
let local_type (Lmt_concrete mt) =
  match mt with
  | None -> None
  | Some mt -> Some (ttuple (List.map ov_type mt.lmt_decl))

let has_locals (Lmt_concrete mt) =
  Option.is_some mt
