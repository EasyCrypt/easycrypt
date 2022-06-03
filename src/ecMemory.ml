(* -------------------------------------------------------------------- *)
open EcSymbols
open EcUtils
open EcTypes

module Msym = EcSymbols.Msym

(* -------------------------------------------------------------------- *)
type memory = EcIdent.t

let mem_equal = EcIdent.id_equal

(* -------------------------------------------------------------------- *)
type proj_arg = {
  arg_quantum : quantum;      (* quantum / classical *)
  arg_ty      : ty;           (* type of the procedure argument "arg" or "qarg" *)
  arg_pos     : int;          (* projection *)
}

type local_memtype_ = {
    mt_name : symbol option;      (* provides access to the full local memory *)
    mt_decl : ovariable list;
    mt_proj : (int * ty) Msym.t;  (* where to find the symbol in mt_decl and its type *)
    mt_ty   : ty;                 (* ttuple (List.map v_type mt_decl) *)
    mt_n    : int;                (* List.length mt_decl *)
  }

let mk_lmt mt_name mt_decl mt_proj =
  let mt_ty = ttuple (List.map ov_type mt_decl) in
  let mt_n  = List.length mt_decl in
  { mt_name; mt_decl; mt_proj; mt_ty; mt_n; }

type local_memtype = {
  classical_lmt : local_memtype_;
  quantum_lmt   : local_memtype_ option;
}

(* [Lmt_schema] if for an axiom schema, and is instantiated to a concrete
   memory type when the axiom schema is.  *)
type memtype =
  | Lmt_concrete of local_memtype option
  | Lmt_schema

let lmem_hash_ lmem =
  let el_hash (s,(i,ty)) =
    Why3.Hashcons.combine2
      (Hashtbl.hash s)
      i (EcTypes.ty_hash ty) in
  let mt_proj_hash =
    Why3.Hashcons.combine_list el_hash 0 (Msym.bindings lmem.mt_proj) in
  let mt_name_hash = Why3.Hashcons.combine_option Hashtbl.hash lmem.mt_name in
  let mt_decl_hash = Why3.Hashcons.combine_list EcTypes.ov_hash 0 lmem.mt_decl in
  Why3.Hashcons.combine_list
    (fun i -> i)
    (EcTypes.ty_hash lmem.mt_ty)
    [ lmem.mt_n;
      mt_name_hash;
      mt_decl_hash;
      mt_proj_hash; ]

let lmem_hash lmem =
  EcUtils.ofold
    (fun lm i -> Why3.Hashcons.combine i (lmem_hash_ lm))
    (lmem_hash_ lmem.classical_lmt)
    lmem.quantum_lmt

let mt_concrete_fv lmt fv =
  List.fold_left (fun fv v ->
      EcIdent.fv_union fv v.ov_type.ty_fv
  ) fv lmt.mt_decl

let mt_fv = function
  | Lmt_schema              -> EcIdent.Mid.empty
  | Lmt_concrete None       -> EcIdent.Mid.empty
  | Lmt_concrete (Some lmt) ->
     let fv = EcIdent.Mid.empty in
     let fv = mt_concrete_fv lmt.classical_lmt fv in
     let fv = ofold mt_concrete_fv fv lmt.quantum_lmt in
     fv

let lmt_equal_ ty_equal mt1 mt2 =
  mt1.mt_name = mt2.mt_name
  &&
    if mt1.mt_name = None
    then
      Msym.equal (fun (_,ty1) (_,ty2) ->
          ty_equal ty1 ty2
        ) mt1.mt_proj mt2.mt_proj
    else
      List.all2 ov_equal mt1.mt_decl mt2.mt_decl

let lmt_equal ty_equal mt1 mt2 =
     lmt_equal_ ty_equal mt1.classical_lmt mt2.classical_lmt
  && opt_equal (lmt_equal_ ty_equal) mt1.quantum_lmt mt2.quantum_lmt

(* -------------------------------------------------------------------- *)
let mt_equal_gen ty_equal mt1 mt2 =
  match mt1, mt2 with
  | Lmt_schema,     Lmt_schema -> true

  | Lmt_schema,     Lmt_concrete _
  | Lmt_concrete _, Lmt_schema -> false

  | Lmt_concrete mt1, Lmt_concrete mt2 ->
    opt_equal (lmt_equal ty_equal) mt1 mt2

let mt_equal = mt_equal_gen ty_equal

(* -------------------------------------------------------------------- *)
let mt_concrete_iter_ty f lmt =
  List.iter (fun v -> f v.ov_type) lmt.mt_decl

(* -------------------------------------------------------------------- *)
let mt_iter_ty f mt =
  match mt with
  | Lmt_schema | Lmt_concrete None -> ()

  | Lmt_concrete (Some mt) ->
     mt_concrete_iter_ty f mt.classical_lmt;
     oiter (mt_concrete_iter_ty f) mt.quantum_lmt

(* -------------------------------------------------------------------- *)
type memenv = memory * memtype

let mem_hash (mem,mt) = match mt with
  | Lmt_schema -> 0
  | Lmt_concrete mt ->
    Why3.Hashcons.combine
      (EcIdent.id_hash mem)
      (Why3.Hashcons.combine_option lmem_hash mt)

let me_equal_gen ty_equal (m1,mt1) (m2,mt2) =
  mem_equal m1 m2 && mt_equal_gen ty_equal mt1 mt2

let me_equal = me_equal_gen ty_equal

(* -------------------------------------------------------------------- *)
let memory   (m,_) = m
let memtype  (_,mt) = mt

(* -------------------------------------------------------------------- *)
exception DuplicatedMemoryBinding of symbol
exception NoQuantumMemory

(* -------------------------------------------------------------------- *)
let empty_local_mt ~witharg quantum =
  let classical_lmt =
    mk_lmt (if witharg then Some arg_symbol else None) [] Msym.empty in
  let quantum_lmt =
    match quantum with
    | `Classical -> None
    | `Quantum   ->
       Some (mk_lmt (if witharg then Some qarg_symbol else None) [] Msym.empty)

  in Lmt_concrete (Some { classical_lmt; quantum_lmt; })

let empty_local ~witharg quantum (me : memory) =
  (me, empty_local_mt ~witharg quantum)

(* -------------------------------------------------------------------- *)
let schema_mt = Lmt_schema
let schema (me : memory) = me, schema_mt

let abstract_mt = Lmt_concrete None
let abstract (me : memory) = me, abstract_mt

let is_schema = function Lmt_schema -> true | _ -> false

(* -------------------------------------------------------------------- *)
let is_bound_lmt x lmt =
  Some x = lmt.mt_name || Msym.mem x lmt.mt_proj

let is_bound x mt =
  match mt with
  | Lmt_schema ->
     false
  | Lmt_concrete None ->
     false
  | Lmt_concrete (Some lmt) ->
     is_bound_lmt x lmt.classical_lmt
     || omap_dfl (is_bound_lmt x) false  lmt.quantum_lmt

let lmt_lookup_ (q : quantum) lmt x =
    let mk v_name v_type = { v_quantum = q; v_name; v_type; } in

    if lmt.mt_name = Some x then
      Some (mk x lmt.mt_ty, None, None)
    else
      match Msym.find_opt x lmt.mt_proj with
      | Some (i,xty) ->
        if lmt.mt_n = 1 then
          Some (mk (odfl x lmt.mt_name) xty, None, None)
        else
          let pa =
            if   is_none lmt.mt_name
            then None
            else Some { arg_quantum = q; arg_ty = lmt.mt_ty; arg_pos = i; } in
          Some(mk x xty, pa, Some i)

      | None -> None

let lookup (x : symbol) (mt : memtype) : (variable * proj_arg option * int option) option =
  match mt with
  | Lmt_schema ->
     None

  | Lmt_concrete None ->
     None

  | Lmt_concrete (Some lmt) -> begin
     match lmt_lookup_ `Classical lmt.classical_lmt x with
     | Some _ as aout -> aout
     | None -> obind (fun lmt -> lmt_lookup_ `Quantum lmt x) lmt.quantum_lmt
    end

let lookup_me x me =
  lookup x (snd me)

(* -------------------------------------------------------------------- *)
let is_bound_pv pv me =
  match pv with
  | PVglob _ -> false
  | PVloc (_,id) -> is_bound id me

(* -------------------------------------------------------------------- *)
let bind_lmt_ (vs : ovariable list) lmt =
  let n = List.length lmt.mt_decl in
  let add_proj mt_proj i v =
    match v.ov_name with
    | None -> mt_proj
    | Some x ->
       if lmt.mt_name = Some x then
         raise (DuplicatedMemoryBinding x);
       let merger = function
         | Some _ -> raise (DuplicatedMemoryBinding x)
         | None   -> Some (n + i,v.ov_type)
       in Msym.change merger x mt_proj
  in
  let mt_decl = lmt.mt_decl @ vs in
  let mt_proj = List.fold_lefti add_proj lmt.mt_proj vs in
  mk_lmt lmt.mt_name mt_decl mt_proj

(* -------------------------------------------------------------------- *)
let is_quantum vs =
  match vs with
  | [] ->
     `Classical

  | v :: vs ->
      assert (List.for_all (fun v' -> v'.ov_quantum = v.ov_quantum) vs);
      v.ov_quantum

(* -------------------------------------------------------------------- *)
let bindall_lmt (vs : ovariable list) lmt =
  match is_quantum vs with
  | `Classical ->
     { lmt with classical_lmt = bind_lmt_ vs lmt.classical_lmt }

  | `Quantum ->
     let quantum_lmt =
       bind_lmt_ vs (oget ~exn:NoQuantumMemory lmt.quantum_lmt)
     in { lmt with quantum_lmt = Some (quantum_lmt) }

(* -------------------------------------------------------------------- *)
let bindall_mt (vs : ovariable list) (mt : memtype) =
  match mt with
  | Lmt_schema | Lmt_concrete None ->
     assert false

  | Lmt_concrete (Some lmt) ->
     Lmt_concrete (Some (bindall_lmt vs lmt))

(* -------------------------------------------------------------------- *)
let bindall (vs : ovariable list) ((m, mt) : memenv) =
  (m, bindall_mt vs mt)

(* -------------------------------------------------------------------- *)
let bindall_fresh (vs : ovariable list) ((m, mt) : memenv) =
  match mt with
  | Lmt_schema | Lmt_concrete None -> assert false
  | Lmt_concrete (Some lmt) ->
     let boundmap_of_lmt lmt map =
       let map = ofold (fun x map -> Ssym.add x map) map lmt.mt_name in
       let map = Msym.fold (fun x _ map -> Ssym.add x map) lmt.mt_proj map in
       map in

     let bmap =
       let map = Ssym.empty in
       let map = boundmap_of_lmt lmt.classical_lmt map in
       let map = ofold boundmap_of_lmt map lmt.quantum_lmt in
       map in

    let fresh_pv bmap v =
      match v.ov_name with
      | None ->
         (bmap, v)

      | Some name ->
          let name =
            match Ssym.mem name bmap with
            | false ->
               name
            | true ->
               let rec for_idx idx =
                 let x = Printf.sprintf "%s%d" name idx in
                 if   Ssym.mem x bmap
                 then for_idx (idx+1)
                 else x
               in for_idx 0 in
          let bmap = Ssym.add name bmap in
          (bmap, { v with ov_name = Some name }) in

    let _, vs = List.map_fold fresh_pv bmap vs in
    let lmt = bindall_lmt vs lmt in
    (m, Lmt_concrete (Some lmt)), vs

(* -------------------------------------------------------------------- *)
let bind_fresh v me =
  let me, vs = bindall_fresh [v] me in
  me, as_seq1 vs

(* -------------------------------------------------------------------- *)
let mt_subst st mt =
  match mt with
  | Lmt_schema ->
     mt

  | Lmt_concrete None ->
     mt

  | Lmt_concrete (Some lmt) ->
     let for_lmt lmt =
       let decl =
         if st == identity then lmt.mt_decl else

         List.Smart.map (fun vty ->
           let ty' = st vty.ov_type in
           if ty_equal vty.ov_type ty' then vty else { vty with ov_type = ty'; }
         ) lmt.mt_decl
       in

       if   decl ==(*phy*) lmt.mt_decl
       then lmt
       else mk_lmt lmt.mt_name decl (Msym.map (fun (i, ty) -> i, st ty) lmt.mt_proj) in

    let classical_lmt = for_lmt lmt.classical_lmt in
    let quantum_lmt   = OSmart.omap for_lmt lmt.quantum_lmt in

    if   classical_lmt == lmt.classical_lmt && quantum_lmt == lmt.quantum_lmt
    then mt
    else Lmt_concrete (Some { classical_lmt; quantum_lmt; })

(* -------------------------------------------------------------------- *)
let me_subst sm st (m,mt as me) =
  let m' = EcIdent.Mid.find_def m m sm in
  let mt' = mt_subst st mt in
  if m' == m && mt' == mt then me else (m', mt')

(* -------------------------------------------------------------------- *)
type lmt_printing = symbol option * ovariable list
type mt_printing  = lmt_printing * lmt_printing option

let for_printing (mt : memtype) : mt_printing option =
  match mt with
  | Lmt_schema ->
     None
  | Lmt_concrete None ->
     None
  | Lmt_concrete (Some mt) ->
     let doit mt = mt.mt_name, mt.mt_decl in
     Some (doit mt.classical_lmt, omap doit mt.quantum_lmt)

(* -------------------------------------------------------------------- *)
let dump_memtype mt =
  match mt with
  | Lmt_schema ->
     "schema"

  | Lmt_concrete None ->
     "abstract"

  | Lmt_concrete (Some mt) ->
    let pp_vd fmt v =
      Format.fprintf fmt "@[%s: %s@]"
        (odfl "_" v.ov_name)
        (EcTypes.dump_ty v.ov_type)
    in

    Format.asprintf "@[{@[%a@] | @[%a@]}@]"
      (Format.pp_print_list
         ~pp_sep:(fun fmt () -> Format.fprintf fmt ",@ ") pp_vd)
      mt.classical_lmt.mt_decl
      (fun fmt -> function
        | None ->
           Format.fprintf fmt "-"
        | Some lmt ->
           Format.fprintf fmt "%a"
             (Format.pp_print_list
                ~pp_sep:(fun fmt () -> Format.fprintf fmt ",@ ") pp_vd)
             lmt.mt_decl)
      mt.quantum_lmt

(* -------------------------------------------------------------------- *)
let get_name_ s p mt =
  match p with
  | None ->
     Some s

  | Some i ->
     if Some s = mt.mt_name then
       omap fst (List.find_opt (fun (_,(i',_)) -> i = i') (Msym.bindings mt.mt_proj))
     else
       None

(* -------------------------------------------------------------------- *)
let get_name (q, s) p (_, mt) =
  match mt with
  | Lmt_schema ->
     None

  | Lmt_concrete None ->
     None

  | Lmt_concrete (Some mt) ->
     match q with
     | `Classical -> get_name_ s p mt.classical_lmt
     | `Quantum   -> obind (get_name_ s p) mt.quantum_lmt

(* -------------------------------------------------------------------- *)
let local_type mt =
  match mt with
  | Lmt_schema ->
     assert false
  | Lmt_concrete None ->
     None

  | Lmt_concrete (Some mt) ->
     let doit mt = ttuple (List.map ov_type mt.mt_decl) in
     Some (doit mt.classical_lmt, omap doit mt.quantum_lmt)

(* -------------------------------------------------------------------- *)
let has_locals mt = match mt with
  | Lmt_concrete (Some _) -> true
  | Lmt_concrete None -> false
  | Lmt_schema -> assert false
