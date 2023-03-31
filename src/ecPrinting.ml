(* -------------------------------------------------------------------- *)
open EcMaps
open EcSymbols
open EcUtils
open EcTypes
open EcModules
open EcDecl
open EcFol

module P  = EcPath
module EP = EcParser
module BI = EcBigInt
module EI = EcInductive

module Ssym = EcSymbols.Ssym
module Msym = EcSymbols.Msym
module Sid  = EcIdent.Sid
module Mid  = EcIdent.Mid
module Sp   = EcPath.Sp

(* -------------------------------------------------------------------- *)
type prpo_display = { prpo_pr : bool; prpo_po : bool; }

(* -------------------------------------------------------------------- *)
type 'a pp = Format.formatter -> 'a -> unit

(* -------------------------------------------------------------------- *)
module PPEnv = struct
  type t = {
    ppe_env     : EcEnv.env;
    ppe_locals  : symbol Mid.t;
    ppe_inuse   : Ssym.t;
    ppe_univar  : (symbol Mint.t * Ssym.t) ref;
    ppe_fb      : Sp.t;
    ppe_width   : int;
  }

  let ofenv (env : EcEnv.env) =
    let width =
      EcGState.asint ~default:0
        (EcGState.getvalue "PP:width" (EcEnv.gstate env)) in

    { ppe_env    = env;
      ppe_locals = Mid.empty;
      ppe_inuse  = Ssym.empty;
      ppe_univar = ref (Mint.empty, Ssym.empty);
      ppe_fb     = Sp.empty;
      ppe_width  = max 20 width; }

  let enter_by_memid ppe id =
    match EcEnv.Memory.byid id ppe.ppe_env with
    | None   -> ppe
    | Some m ->
      { ppe with
        ppe_env = EcEnv.Memory.set_active (fst m) ppe.ppe_env }

  let push_mem ppe ?(active = false) m =
    let ppe = { ppe with ppe_env = EcEnv.Memory.push m ppe.ppe_env } in
      match active with
      | true  -> enter_by_memid ppe (fst m)
      | false -> ppe

  let create_and_push_mem ppe ?active memenv =
    push_mem ppe ?active memenv

  let push_mems ppe ids =
    List.fold_left (push_mem ?active:None) ppe ids

  let create_and_push_mems ppe ids =
    List.fold_left (create_and_push_mem ?active:None) ppe ids

  let inuse ppe name =
    let env = ppe.ppe_env in

    let in_memories name =
      let env = ppe.ppe_env in
      let check mem = EcMemory.is_bound name (snd mem) in
      List.exists check (EcEnv.Memory.all env)

    in

         (Ssym.mem name ppe.ppe_inuse)
      || (Ssym.mem name (snd !(ppe.ppe_univar)))
      || (EcEnv.Mod.sp_lookup_opt      ([], name) env <> None)
      || (EcEnv.Var.lookup_local_opt        name  env <> None)
      || (EcEnv.Var.lookup_progvar_opt ([], name) env <> None)
      || (in_memories name)

  let add_local_r ?gen ?(force = false) ppe =
    fun id ->
      let addu =
        let id = EcIdent.name id in
        if String.length id > 0 then
          let c = id.[String.length id - 1] in
          c >= '0' && c <= '9'
        else
          false
      in

      let usergen, gen =
        match gen with
        | None ->
            (false, fun i ->
              Printf.sprintf "%s%s%d"
                (EcIdent.name id) (if addu then "_" else "") i)

        | Some gen ->
            (true, fun i -> gen i)
      in

      let first = ref true in
      let name  = ref (EcIdent.name id) in
      let i     = ref 0 in

        if not force then
          while (usergen && !first) || (inuse ppe !name) do
            first := false; name := gen !i; incr i
          done;

      let ppe =
        { ppe with
            ppe_inuse  = Ssym.add !name ppe.ppe_inuse;
            ppe_locals = Mid.add id !name ppe.ppe_locals; }
      in
        (!name, ppe)

  let add_local ?gen ?force ppe id =
    snd (add_local_r ?gen ?force ppe id)

  let add_locals ?force ppe xs = List.fold_left (add_local ?force) ppe xs

  let add_mods ?force ppe xs mty =
    let ppe = add_locals ?force ppe xs in
    { ppe with
        ppe_env =
          List.fold_left
            (fun env x -> EcEnv.Mod.bind_local x mty env)
            ppe.ppe_env xs; }

  let p_shorten cond p =
    let rec shorten prefix (nm, x) =
      match cond (nm, x) with
      | true  -> (nm, x)
      | false -> begin
        match prefix with
        | [] -> (nm, x)
        | n :: prefix -> shorten prefix (n :: nm, x)
      end
    in

    let (nm, x) = P.toqsymbol p in
    shorten (List.rev nm) ([], x)

  let ty_symb (ppe : t) p =
      let exists sm =
      try  EcPath.p_equal (EcEnv.Ty.lookup_path sm ppe.ppe_env) p
      with EcEnv.LookupFailure _ -> false
    in
      p_shorten exists p

  let tc_symb (ppe : t) p =
      let exists sm =
      try  EcPath.p_equal (EcEnv.TypeClass.lookup_path sm ppe.ppe_env) p
      with EcEnv.LookupFailure _ -> false
    in
      p_shorten exists p

  let rw_symb (ppe : t) p =
      let exists sm =
      try  EcPath.p_equal (EcEnv.BaseRw.lookup_path sm ppe.ppe_env) p
      with EcEnv.LookupFailure _ -> false
    in
      p_shorten exists p

  let ax_symb (ppe : t) p =
      let exists sm =
      try  EcPath.p_equal (EcEnv.Ax.lookup_path sm ppe.ppe_env) p
      with EcEnv.LookupFailure _ -> false
    in
      p_shorten exists p

  let op_symb (ppe : t) p info =
    let specs = [1, EcPath.pqoname (EcPath.prefix EcCoreLib.CI_Bool.p_eq) "<>"] in

    let check_for_local sm =
      if List.is_empty (fst sm) && inuse ppe (snd sm) then
        raise (EcEnv.LookupFailure (`QSymbol sm));
    in

    let lookup =
      match info with
      | None -> fun sm ->
          check_for_local sm;
          EcEnv.Op.lookup_path sm ppe.ppe_env

      | Some (mode, typ, dom) ->
          let filter =
            match mode with
            | `Expr -> fun _ op -> not (EcDecl.is_pred op)
            | `Form -> fun _ _  -> true
          in
          let tvi = Some (EcUnify.TVIunamed typ) in

        fun sm ->
          check_for_local sm;
          let ue = EcUnify.UniEnv.create None in
          match  EcUnify.select_op ~hidden:true ~filter tvi ppe.ppe_env sm ue dom with
          | [(p1, _), _, _, _] -> p1
          | _ -> raise (EcEnv.LookupFailure (`QSymbol sm)) in

    let exists sm =
        try EcPath.p_equal (lookup sm) p
       with EcEnv.LookupFailure _ -> false
    in
      (* FIXME: for special operators, do check `info` *)
      if   List.exists (fun (_, sp) -> EcPath.p_equal sp p) specs
      then ([], EcPath.basename p)
      else p_shorten exists p

  let ax_symb (ppe : t) p =
    let exists sm =
      try  EcPath.p_equal (EcEnv.Ax.lookup_path sm ppe.ppe_env) p
      with EcEnv.LookupFailure _ -> false
    in
      p_shorten exists p

  let sc_symb (ppe : t) p =
    let exists sm =
      try  EcPath.p_equal (EcEnv.Schema.lookup_path sm ppe.ppe_env) p
      with EcEnv.LookupFailure _ -> false
    in
    p_shorten exists p

  let th_symb (ppe : t) p =
    let exists sm =
      try  EcPath.p_equal (EcEnv.Theory.lookup_path sm ppe.ppe_env) p
      with EcEnv.LookupFailure _ -> false
    in
      p_shorten exists p

  let rec mod_symb (ppe : t) mp : EcSymbols.msymbol =
    let (nm, x, p2) =
      match mp.P.m_top with
      | `Local x ->
          let name =
            match Mid.find_opt x ppe.ppe_locals with
            | Some name -> name
            | None ->
                let name = EcIdent.name x in
                  match EcEnv.Mod.sp_lookup_opt ([], name) ppe.ppe_env with
                  | Some (p, _, _) when EcPath.mt_equal mp.P.m_top p.P.m_top -> name
                  | _ -> EcIdent.tostring x
          in
            ([], name, None)

      | `Concrete (p1, p2) ->
          let exists sm =
            match EcEnv.Mod.sp_lookup_opt sm ppe.ppe_env with
            | None -> false
            | Some (mp1, _, _) -> P.mt_equal mp1.P.m_top (`Concrete (p1, None))
          in

          let rec shorten prefix (nm, x) =
            match exists (nm, x) with
            | true  -> (nm, x)
            | false -> begin
                match prefix with
                | [] -> (nm, x)
                | n :: prefix -> shorten prefix (n :: nm, x)
            end
          in

          let (nm, x) = P.toqsymbol p1 in
          let (nm, x) = shorten (List.rev nm) ([], x) in
            (nm, x, p2)
    in
    let msymb =
        (List.map (fun x -> (x, [])) nm)
      @ [(x, List.map (mod_symb ppe) mp.P.m_args)]
      @ (List.map (fun x -> (x, [])) (odfl [] (p2 |> omap P.tolist)))
    in
      msymb

  let modtype_symb (ppe : t) mty : EcSymbols.msymbol =
    let exists sm =
      match EcEnv.ModTy.lookup_opt sm ppe.ppe_env with
      | None -> false
      | Some (p, _) -> P.p_equal p mty.mt_name
    in

    let rec shorten prefix (nm, x) =
      match exists (nm, x) with
      | true  -> (nm, x)
      | false -> begin
          match prefix with
          | [] -> (nm, x)
          | m :: prefix -> shorten prefix (m :: nm, x)
      end
    in

    let (nm, x) = P.toqsymbol mty.mt_name in
    let (nm, x) = shorten (List.rev nm) ([], x) in

    let isfunctor =
      List.all2 EcPath.m_equal
	      (List.map (fun (x, _) -> EcPath.mident x) mty.mt_params)
	      mty.mt_args
    in

    let msymb =
      match isfunctor with
      | true  -> (List.map (fun x -> (x, [])) nm) @ [(x, [])]
      | false ->
           (List.map (fun x -> (x, [])) nm)
         @ [(x, List.map (mod_symb ppe) mty.mt_args)]
    in
      msymb

  let local_symb ppe x =
    match Mid.find_opt x ppe.ppe_locals with
    | Some name -> name
    | None ->
        let name = EcIdent.name x in
          match EcEnv.Var.lookup_local_opt name ppe.ppe_env with
          | Some (id, _) when EcIdent.id_equal id x -> name
          | _ -> EcIdent.name x

  let tyvar (ppe : t) x =
    match Mid.find_opt x ppe.ppe_locals with
    | None   -> EcIdent.tostring x
    | Some x -> x

  exception FoundUnivarSym of symbol

  let tyunivar (ppe : t) i =
    if not (Mint.mem i (fst !(ppe.ppe_univar))) then begin
      let alpha  = "abcdefghijklmnopqrstuvwxyz" in

      let rec findx prefix i =
        let for1 x =
          let x = prefix ^ (String.make 1 x) in

          if i <= 0 then begin
            if not (inuse ppe x) then
              raise (FoundUnivarSym x)
          end else
            findx x (i-1)
        in
          String.iter for1 alpha
      in

      let x =
        try  for i = 0 to max_int do findx "#" i done; assert false
        with FoundUnivarSym x -> x
      in

      let (map, uses) = !(ppe.ppe_univar) in
        ppe.ppe_univar := (Mint.add i x map, Ssym.add x uses)
    end;

    oget (Mint.find_opt i (fst !(ppe.ppe_univar)))
end

(* -------------------------------------------------------------------- *)
let pp_id pp fmt x = Format.fprintf fmt "%a" pp x

(* -------------------------------------------------------------------- *)
let pp_null (_fmt : Format.formatter) = fun _ -> ()

(* -------------------------------------------------------------------- *)
let pp_if c pp1 pp2 fmt x =
  match c with
  | true  -> Format.fprintf fmt "%a" pp1 x
  | false -> Format.fprintf fmt "%a" pp2 x

(* -------------------------------------------------------------------- *)
let pp_maybe c tx pp fmt x =
  pp_if c (tx pp) pp fmt x

(* -------------------------------------------------------------------- *)
let pp_opt pp_el fmt = function
  | None   -> Format.fprintf fmt "None"
  | Some x -> Format.fprintf fmt "Some %a" pp_el x

(* -------------------------------------------------------------------- *)
let rec pp_list sep pp fmt xs =
  let pp_list = pp_list sep pp in
    match xs with
    | []      -> ()
    | [x]     -> Format.fprintf fmt "%a" pp x
    | x :: xs -> Format.fprintf fmt "%a%(%)%a" pp x sep pp_list xs

(* -------------------------------------------------------------------- *)
let pp_option pp fmt x =
  match x with None -> () | Some x -> pp fmt x

(* -------------------------------------------------------------------- *)
let pp_enclose ~pre ~post pp fmt x =
  Format.fprintf fmt "%(%)%a%(%)" pre pp x post

(* -------------------------------------------------------------------- *)
let pp_paren pp fmt x =
  pp_enclose ~pre:"(" ~post:")" pp fmt x

(* -------------------------------------------------------------------- *)
let pp_maybe_paren c pp =
  pp_maybe c pp_paren pp

(* -------------------------------------------------------------------- *)
let pp_string fmt x =
  Format.fprintf fmt "%s" x

(* -------------------------------------------------------------------- *)
let pp_path fmt p =
  Format.fprintf fmt "%s" (P.tostring p)

(* -------------------------------------------------------------------- *)
let pp_topmod ppe fmt p =
  Format.fprintf fmt "%a"
    EcSymbols.pp_msymbol (PPEnv.mod_symb ppe p)

(* -------------------------------------------------------------------- *)
let pp_tyvar ppe fmt x =
  Format.fprintf fmt "%s" (PPEnv.tyvar ppe x)

(* -------------------------------------------------------------------- *)
let pp_tyunivar ppe fmt x =
  Format.fprintf fmt "%s" (PPEnv.tyunivar ppe x)

(* -------------------------------------------------------------------- *)
let pp_tyname ppe fmt p =
  Format.fprintf fmt "%a" EcSymbols.pp_qsymbol (PPEnv.ty_symb ppe p)

(* -------------------------------------------------------------------- *)
let pp_tcname ppe fmt p =
  Format.fprintf fmt "%a" EcSymbols.pp_qsymbol (PPEnv.tc_symb ppe p)

(* -------------------------------------------------------------------- *)
let pp_rwname ppe fmt p =
  Format.fprintf fmt "%a" EcSymbols.pp_qsymbol (PPEnv.rw_symb ppe p)

(* -------------------------------------------------------------------- *)
let pp_axname ppe fmt p =
  Format.fprintf fmt "%a" EcSymbols.pp_qsymbol (PPEnv.ax_symb ppe p)

(* -------------------------------------------------------------------- *)
let pp_scname ppe fmt p =
  Format.fprintf fmt "%a" EcSymbols.pp_qsymbol (PPEnv.sc_symb ppe p)

(* -------------------------------------------------------------------- *)
let pp_thname ppe fmt p =
  EcSymbols.pp_qsymbol fmt (PPEnv.th_symb ppe p)

(* -------------------------------------------------------------------- *)
let pp_funname (ppe : PPEnv.t) fmt p =
  Format.fprintf fmt "%a.%s" (pp_topmod ppe) p.P.x_top p.P.x_sub

(* -------------------------------------------------------------------- *)
let pp_funname (ppe : PPEnv.t) fmt p =
  Format.fprintf fmt "%a.%s"
    (pp_topmod ppe) p.P.x_top p.P.x_sub

(* -------------------------------------------------------------------- *)
let msymbol_of_pv (ppe : PPEnv.t) p =
  match p with
  | PVloc name -> [(name,[])]

  | PVglob xp ->
    let mem =
      let env = ppe.PPEnv.ppe_env in
      obind (EcEnv.Memory.byid^~ env) (EcEnv.Memory.get_active env) in

    let exception Default in

    let x = xp.P.x_sub in

    try
      let pv' =
        EcEnv.Var.lookup_progvar_opt
          ?side:(omap fst mem) ([], x) ppe.PPEnv.ppe_env in

      match omap fst pv' with
      | Some (`Var pv') when EcEnv.NormMp.pv_equal ppe.PPEnv.ppe_env p pv'  ->
        [(x, [])]

      | _ ->
        raise Default

    with Default ->
      (PPEnv.mod_symb ppe xp.P.x_top)
      @ [(x, [])]


(* -------------------------------------------------------------------- *)
let pp_pv ppe fmt p =
  EcSymbols.pp_msymbol fmt (msymbol_of_pv ppe p)

(* -------------------------------------------------------------------- *)
exception NoProjArg

let get_projarg_for_var ppe x i =
  let m = oget ~exn:NoProjArg (EcEnv.Memory.current ppe.PPEnv.ppe_env) in
  if is_glob x then raise NoProjArg;
  oget ~exn:NoProjArg (EcMemory.get_name (get_loc x) (Some i) m)

let get_f_projarg ppe e i ty =
  match e.f_node with
  | Fpvar (x, m) ->
    let ppe = PPEnv.enter_by_memid ppe m in
    let s = get_projarg_for_var ppe x i in
    f_pvar (pv_loc s) ty m
  | _ -> raise NoProjArg

(* -------------------------------------------------------------------- *)
let all_mem_sym = "+all mem"

let pp_restr_s fmt = function
  | true -> Format.fprintf fmt "+"
  | false -> Format.fprintf fmt "-"

let pp_modtype1 (ppe : PPEnv.t) fmt mty =
  EcSymbols.pp_msymbol fmt (PPEnv.modtype_symb ppe mty)

(* -------------------------------------------------------------------- *)
let pp_local (ppe : PPEnv.t) fmt x =
  Format.fprintf fmt "%s" (PPEnv.local_symb ppe x)

(* -------------------------------------------------------------------- *)
let pp_local ?fv (ppe : PPEnv.t) fmt x =
  if is_none fv || oif (Mid.mem x) fv then
    pp_local ppe fmt x
  else pp_string fmt "_"

(* -------------------------------------------------------------------- *)
type assoc  = [`Left | `Right | `NonAssoc]
type iassoc = [`ILeft | `IRight | assoc]
type fixity = [`Prefix | `Postfix | `Infix of assoc | `NonAssoc]
type opprec = int * fixity

(* -------------------------------------------------------------------- *)
(* precondition: fst inner_left <= fst inner *)
let maybe_paren_gen (onm, (outer, side)) (inm, inner, inner_left) pp =
  let noparens ((pi : int), fi) (pil, fil) (po, fo) side =
    pil > po ||  (* pi > po is too strong *)
      match fi, side with
      | `Postfix     , `Left     -> true
      | `Prefix      , `Right    -> true
      | `Infix `Left , `Left     -> pil = po && fo = `Infix `Left
      | `Infix `Right, `Right    -> pi > po || pi = po && fo = `Infix `Right
      | _            , `Right    -> pi > po
      | `Infix `Left , `ILeft    -> pi > po || pi = po && fo = `Infix `Left
      | `Infix `Right, `IRight   -> pi > po || pi = po && fo = `Infix `Right
      | _            , `NonAssoc -> pi > po || pi = po && fi = fo
      | _            , _         -> false
  in
    match inm <> [] && inm <> onm with
    | false -> pp_maybe_paren (not (noparens inner inner_left outer side)) pp
    | true  ->
        let inm = if inm = [EcCoreLib.i_top] then ["top"] else inm in
          fun fmt x ->
            Format.fprintf fmt "(%a)%%%s" pp x (String.concat "." inm)

(* use inner for inner_left: *)
let maybe_paren (onm, (outer, side)) (inm, inner) pp =
  maybe_paren_gen (onm, (outer, side)) (inm, inner, inner) pp

let maybe_paren_nosc outer inner pp =
  maybe_paren ([], outer) ([], inner) pp

(* -------------------------------------------------------------------- *)
let t_prio_fun  = (10, `Infix `Right)
let t_prio_tpl  = (20, `NonAssoc)
let t_prio_name = (30, `Postfix)

(* -------------------------------------------------------------------- *)
let e_bin_prio_lambda = ( 5, `Prefix)
let e_bin_prio_if     = ( 5, `Prefix)
let e_bin_prio_letin  = ( 5, `Prefix)
let e_bin_prio_impl   = (10, `Infix `Right)
let e_bin_prio_iff    = (12, `NonAssoc)
(* don't need, as closed with end:
let e_bin_prio_match  = (15, `Prefix)
*)
let e_bin_prio_nop    = (19, `Infix `Left)
let e_bin_prio_or     = (20, `Infix `Right)
let e_bin_prio_and    = (25, `Infix `Right)
let e_bin_prio_eq     = (27, `Infix `NonAssoc)
let e_bin_prio_order  = (29, `NonAssoc)
let e_bin_prio_lop1   = (30, `Infix `Left )
let e_bin_prio_rop1   = (31, `Infix `Right)
let e_bin_prio_lop2   = (40, `Infix `Left )
let e_bin_prio_rop2   = (41, `Infix `Right)
let e_bin_prio_lop3   = (50, `Infix `Left )
let e_bin_prio_rop3   = (51, `Infix `Right)
let e_bin_prio_lop4   = (60, `Infix `Left )
let e_bin_prio_rop4   = (61, `Infix `Right)
let e_bin_prio_if3    = e_bin_prio_lop2

let e_uni_prio_not    = 26
let e_uni_prio_lsless = 10000
let e_uni_prio_uminus = fst e_bin_prio_lop2
let e_app_prio        = (10000, `Infix `Left)
let e_get_prio        = (20000, `Infix `Left)
let e_uni_prio_rint   = (15000, `Postfix)

let min_op_prec = (-1     , `Infix `NonAssoc)
let max_op_prec = (max_int, `Infix `NonAssoc)

(* -------------------------------------------------------------------- *)
let priority_of_binop name =
  match EcIo.lex_single_token name with
  | Some EP.IMPL      -> Some e_bin_prio_impl
  | Some EP.IFF       -> Some e_bin_prio_iff
  | Some EP.ORA       -> Some e_bin_prio_or
  | Some EP.OR        -> Some e_bin_prio_or
  | Some EP.ANDA      -> Some e_bin_prio_and
  | Some EP.AND       -> Some e_bin_prio_and
  | Some EP.EQ        -> Some e_bin_prio_eq
  | Some EP.NE        -> Some e_bin_prio_eq
  | Some EP.GT        -> Some e_bin_prio_order
  | Some EP.GE        -> Some e_bin_prio_order
  | Some EP.LT        -> Some e_bin_prio_order
  | Some EP.LE        -> Some e_bin_prio_order
  | Some EP.LOP1 _    -> Some e_bin_prio_lop1
  | Some EP.ROP1 _    -> Some e_bin_prio_rop1
  | Some EP.LOP2 _    -> Some e_bin_prio_lop2
  | Some EP.ROP2 _    -> Some e_bin_prio_rop2
  | Some EP.PLUS      -> Some e_bin_prio_lop2
  | Some EP.MINUS     -> Some e_bin_prio_lop2
  | Some EP.LOP3 _    -> Some e_bin_prio_lop3
  | Some EP.ROP3 _    -> Some e_bin_prio_rop3
  | Some EP.STAR      -> Some e_bin_prio_lop3
  | Some EP.SLASH     -> Some e_bin_prio_lop3
  | Some EP.LOP4 _    -> Some e_bin_prio_lop4
  | Some EP.ROP4 _    -> Some e_bin_prio_rop4
  | Some EP.AT        -> Some e_bin_prio_lop4
  | Some EP.HAT       -> Some e_bin_prio_lop4
  | Some EP.BACKSLASH -> Some e_bin_prio_lop4
  | Some EP.NOP _     -> Some e_bin_prio_nop

  | _ -> None

(* -------------------------------------------------------------------- *)
let priority_of_unop =
  let id_not = EcPath.basename EcCoreLib.CI_Bool.p_not in
    fun name ->
      match EcIo.lex_single_token name with
      | Some EP.NOT ->
          Some e_uni_prio_not
      | Some EP.PUNIOP s when s = id_not ->
          Some e_uni_prio_not
      | Some EP.PUNIOP _ ->
          Some e_uni_prio_uminus
      | _ ->
          None

(* -------------------------------------------------------------------- *)
let is_binop name =
  (priority_of_binop name) <> None

(* -------------------------------------------------------------------- *)
let is_pstop name =
  String.length name > 0 && name.[0] = '%'

(* -------------------------------------------------------------------- *)
let rec pp_type_r ppe outer fmt ty =
  match ty.ty_node with
  | Tglob m -> Format.fprintf fmt "(glob %a)" (pp_topmod ppe) m

  | Tunivar x -> pp_tyunivar ppe fmt x
  | Tvar    x -> pp_tyvar ppe fmt x

  | Ttuple tys ->
      let pp fmt tys =
        pp_list " *@ " (pp_type_r ppe (t_prio_tpl, `Left)) fmt tys
      in
        maybe_paren_nosc outer t_prio_tpl pp fmt tys

  | Tconstr (name, tyargs) -> begin
      let pp fmt (name, tyargs) =
        match tyargs with
        | [] ->
            pp_tyname ppe fmt name

        | [x] ->
            Format.fprintf fmt "%a %a"
              (pp_type_r ppe (t_prio_name, `Left)) x
              (pp_tyname ppe) name

        | xs ->
            let subpp = pp_type_r ppe (min_op_prec, `NonAssoc) in
              Format.fprintf fmt "%a %a"
                (pp_paren (pp_list ",@ " subpp)) xs
                (pp_tyname ppe) name
      in
        maybe_paren_nosc outer t_prio_name pp fmt (name, tyargs)
    end

  | Tfun (t1, t2) ->
      let pp fmt (t1, t2) =
        Format.fprintf fmt "@[%a ->@ %a@]"
          (pp_type_r ppe (t_prio_fun, `Left )) t1
          (pp_type_r ppe (t_prio_fun, `Right)) t2
      in
        maybe_paren_nosc outer t_prio_fun pp fmt (t1, t2)

let pp_type ppe fmt ty =
  pp_type_r ppe (min_op_prec, `NonAssoc) fmt ty

let pp_stype ppe fmt ty =
  pp_type_r ppe ((1 + fst t_prio_tpl, `NonAssoc), `NonAssoc) fmt ty

(* -------------------------------------------------------------------- *)
let pp_mem (ppe : PPEnv.t) fmt x =
  let x = Format.sprintf "%s" (PPEnv.local_symb ppe x) in
  let x =
    if   x <> "" && x.[0] = '&'
    then String.sub x 1 (String.length x - 1)
    else x
  in
    Format.fprintf fmt "%s" x

let pp_memtype ppe fmt mt =
  match EcMemory.for_printing mt with
  | None -> Format.fprintf fmt "{}"
  | Some (arg, decl) ->
    match arg with
    | Some arg ->
      let pp_vd fmt v =
        Format.fprintf fmt "@[%s: %a@]"
          (odfl "_" v.ov_name)
          (pp_type ppe) v.ov_type
      in
      Format.fprintf fmt "@[{%s: {@[%a@]}}@]" arg (pp_list ",@ " pp_vd) decl
    | None ->
      let add mty v =
        let ids = Mty.find_def [] v.ov_type mty in
        Mty.add v.ov_type (odfl "_" v.ov_name::ids) mty in
      let mty = List.fold_left add Mty.empty decl in
      let pp_bind fmt (ty, ids) =
        Format.fprintf fmt "@[%a :@ %a@]"
          (pp_list ",@ " (fun fmt s -> Format.fprintf fmt "%s" s))
          (List.rev ids) (pp_type ppe) ty in
      let lty = Mty.bindings mty in
      Format.fprintf fmt "@[{%a}@]" (pp_list ",@ " pp_bind) lty

(* -------------------------------------------------------------------- *)
let pp_opname fmt (nm, op) =
  let op =
    if EcCoreLib.is_mixfix_op op then
      Printf.sprintf "\"%s\"" op
    else if is_binop op then begin
      if op.[0] = '*' || op.[String.length op - 1] = '*'
      then Format.sprintf "( %s )" op
      else Format.sprintf "(%s)" op
    end else if is_pstop op then
      Format.sprintf "(%s)" op
    else op

  in EcSymbols.pp_qsymbol fmt (nm, op)

let pp_opname_with_tvi ppe fmt (nm, op, tvi) =
  match tvi with
  | None ->
      pp_opname fmt (nm, op)

  | Some tvi ->
      Format.fprintf fmt "%a<:%a>"
        pp_opname (nm, op)
        (pp_list "@, " (pp_type ppe)) tvi

(* -------------------------------------------------------------------- *)
(* no longer used, as printed as if ... then ... else
let pp_if3 (ppe : PPEnv.t) pp_sub outer fmt (b, e1, e2) =
  let pp fmt (b, e1, e2)=
    Format.fprintf fmt "@[<hov 2>%a@ ? %a@ : %a@]"
      (pp_sub ppe (fst outer, (e_bin_prio_if3, `Left    ))) b
      (pp_sub ppe (fst outer, (min_op_prec   , `NonAssoc))) e1
      (pp_sub ppe (fst outer, (e_bin_prio_if3, `Right   ))) e2
  in
    maybe_paren outer ([], e_bin_prio_if3) pp fmt (b, e1, e2)
*)

let pp_if_form (ppe : PPEnv.t) pp_sub outer fmt (b, e1, e2) =
  let pp fmt (b, e1, e2) =
    Format.fprintf fmt "@[@[<hov 2>if %a@ then@ %a@]@ @[<hov 2>else@ %a@]@]"
      (pp_sub ppe (fst outer, (min_op_prec, `NonAssoc))) b
      (pp_sub ppe (fst outer, (min_op_prec, `NonAssoc))) e1
      (pp_sub ppe (fst outer, (min_op_prec, `NonAssoc))) e2
(*
is there a reason to instead do it this way?
      (pp_sub ppe (fst outer, (e_bin_prio_if, `Right   ))) e2 (* FIXME *)
*)
  in
    maybe_paren outer ([], e_bin_prio_if) pp fmt (b, e1, e2)

(* -------------------------------------------------------------------- *)
let pp_match_form (ppe : PPEnv.t) pp_sub outer fmt (b, bs) =
  let pp fmt (b, bs) =
    let env = ppe.PPEnv.ppe_env in
    let dt  = proj3_2 (oget (EcEnv.Ty.get_top_decl b.f_ty env)) in
    let dt  = oget (EcDecl.tydecl_as_datatype dt) in
    let bs  = List.combine dt.tydt_ctors bs in

    let pp_branch fmt ((name, argsty), br) =
      let xs, br = EcFol.decompose_lambda br in
      let xs, br =
        let (xs1, xs2), rem =
          try  (List.split_at (List.length argsty) xs, [])
          with Invalid_argument _ ->
            let rem =
              List.map
                (fun ty -> (EcIdent.create (symbol_of_ty ty), ty))
                (List.drop (List.length xs) argsty) in
              (xs, []), rem in

        (List.fst xs1 @ List.fst rem,
         f_ty_app ppe.PPEnv.ppe_env
           (f_lambda xs2 br) (List.map (curry f_local) rem)) in

      begin match xs with
      | [] ->
          Format.fprintf fmt "| %a" pp_opname ([], name)

      | [x] ->
          Format.fprintf fmt "| %a %a"
            pp_opname ([], name) (pp_local ppe) x

      | _ ->
          Format.fprintf fmt "| %a (%a)" pp_opname ([], name)
            (pp_list ", " (pp_local ppe)) xs
      end;

      Format.fprintf fmt " => %a"
        (pp_sub ppe (fst outer, (min_op_prec, `NonAssoc))) br in

    Format.fprintf fmt "@[@[<hov 2>match %a@ with %t end@]@]"
      (pp_sub ppe (fst outer, (min_op_prec, `NonAssoc))) b
      (fun fmt -> pp_list "@ " pp_branch fmt bs)

  in pp fmt (b, bs)  (* has end, so don't need maybe_paren *)

(* -------------------------------------------------------------------- *)
let pp_tuple mode (ppe : PPEnv.t) pp_sub osc fmt es =
  let prth =
    match mode, es with
    | `ForBinding, [_] -> false
    | `ForBinding, _   -> true
    | `ForTuple  , _   -> true
  in

  let pp fmt = pp_list ",@ " (pp_sub ppe (osc, (min_op_prec, `NonAssoc))) fmt es in
  let pp fmt = Format.fprintf fmt "@[<hov 0>%t@]" pp in

    pp_maybe_paren prth (fun fmt () -> pp fmt) fmt ()

let pp_proji ppe pp_sub osc fmt (e,i) =
  Format.fprintf fmt "%a.`%i"
    (pp_sub ppe (osc, (max_op_prec, `NonAssoc))) e
    (i+1)

(* -------------------------------------------------------------------- *)
let pp_let ?fv (ppe : PPEnv.t) pp_sub outer fmt (pt, e1, e2) =
  let pp fmt (pt, e1, e2) =
    let ids    = lp_ids pt in
    let subppe = PPEnv.add_locals ppe ids in
      Format.fprintf fmt "@[<hov 0>let %a =@;<1 2>@[%a@]@ in@ %a@]"
        (pp_tuple `ForBinding subppe
           (fun ppe _ -> pp_local ?fv ppe) (fst outer)) ids
        (pp_sub ppe    (fst outer, (e_bin_prio_letin, `NonAssoc))) e1
        (pp_sub subppe (fst outer, (e_bin_prio_letin, `NonAssoc))) e2
  in
    maybe_paren outer ([], e_bin_prio_letin) pp fmt (pt, e1, e2)

(* -------------------------------------------------------------------- *)
let pp_app (ppe : PPEnv.t) (pp_first, pp_sub) outer fmt (e, args) =
  match args with
  | [] ->
      pp_first ppe outer fmt e

  | _ ->
    let rec doit fmt args =
      match args with
      | [] ->
          pp_first ppe (fst outer, (e_app_prio, `ILeft)) fmt e

      | a :: args ->
          Format.fprintf fmt "%a@ %a"
            doit args (pp_sub ppe (fst outer, (e_app_prio, `IRight))) a
    in

    let pp fmt () =
      Format.fprintf fmt "@[<hov 2>%a@]" doit (List.rev args)
    in
      maybe_paren outer ([], e_app_prio) pp fmt ()

(* -------------------------------------------------------------------- *)
let pp_opapp
     (ppe      : PPEnv.t)
     (t_ty     : 'a -> EcTypes.ty)
    ((dt_sub   : 'a -> (EcPath.path * _ * 'a list) option),
     (pp_sub   : PPEnv.t -> _ * (opprec * iassoc) -> _ -> 'a -> unit),
     (is_trm   : 'a -> bool),
     (is_tuple : 'a -> 'a list option),
     (is_proj  : EcPath.path -> 'a -> (EcIdent.t * int) option))
     (lwr_left : PPEnv.t -> ('a -> EcTypes.ty) -> 'a ->
                 EcSymbols.symbol list -> opprec -> int option)
     (outer    : symbol list * ((_ * fixity) * iassoc))
     (fmt      : Format.formatter)
     ((pred    : [`Expr | `Form]),
      (op      : EcPath.path),
      (tvi     : EcTypes.ty list),
      (es      : 'a list))
=
  let (nm, opname) =
    PPEnv.op_symb ppe op (Some (pred, tvi, List.map t_ty es)) in

  let inm = if nm = [] then fst outer else nm in

  let pp_tuple_sub ppe prec fmt e =
    match is_tuple e with
    | None    -> pp_sub ppe prec fmt e
    | Some es -> pp_list ", " (pp_sub ppe prec) fmt es in

  let pp_as_std_op fmt =
    let module E = struct exception PrintAsPlain end in

    try
      let (pp, prio, es) =
        match opname, es with
        | x, _ when x = EcCoreLib.s_nil ->
            ((fun fmt -> pp_string fmt "[]"), max_op_prec, es)

        | x, e :: es when x = EcCoreLib.s_abs ->
            let pp fmt =
              Format.fprintf fmt "`|%a|"
                (pp_sub ppe (inm, (min_op_prec, `NonAssoc))) e
            in
              (pp, e_app_prio, es)

        | x, e1 :: e2 :: es when x = EcCoreLib.s_get ->
            let pp fmt =
              Format.fprintf fmt "@[%a.[%a]@]"
                (pp_sub       ppe (inm, (e_get_prio , `Left    ))) e1
                (pp_tuple_sub ppe (inm, (min_op_prec, `NonAssoc))) e2
            in
              (pp, e_get_prio, es)

        | x, e1 :: e2 :: e3 :: es when x = EcCoreLib.s_set ->
            let pp fmt =
              Format.fprintf fmt "@[<hov 2>%a.[%a <-@ %a]@]"
                (pp_sub       ppe (inm, (e_get_prio , `Left    ))) e1
                (pp_tuple_sub ppe (inm, (min_op_prec, `NonAssoc))) e2
                (pp_sub       ppe (inm, (min_op_prec, `NonAssoc))) e3
            in
              (pp, e_get_prio, es)

        | _ ->
            raise E.PrintAsPlain
      in
      let rec doit fmt args =
        match args with
        | [] ->
           maybe_paren outer (inm, prio) (fun fmt () -> pp fmt) fmt ()

        | a :: args ->
           Format.fprintf fmt "%a@ %a"
             doit args (pp_sub ppe (fst outer, (e_app_prio, `IRight))) a

      in fun () -> doit fmt es

    with E.PrintAsPlain ->
      fun () ->
        match es with
        | [] ->
            pp_opname fmt (nm, opname)

        | _  ->
            let pp_subs = ((fun _ _ -> pp_opname), pp_sub) in
            let pp fmt () = pp_app ppe pp_subs outer fmt (([], opname), es) in
            maybe_paren outer (inm, max_op_prec) pp fmt ()

  and try_pp_as_uniop () =
    match es with
    | [e] -> begin
      match priority_of_unop opname with
      | None -> None
      | Some bopprio ->
          let opprio = (bopprio, `Prefix) in
          let opname =
            EcRegexp.exec (`S "^\\[(.+)\\]$") opname
              |> omap (fun m -> oget (EcRegexp.Match.group m 1))
              |> odfl opname in
          let pp fmt =
            Format.fprintf fmt "@[%s%s%a@]" opname
              (if is_trm e then "" else " ")
              (pp_sub ppe (inm, (opprio, `NonAssoc))) e in
          let pp fmt =
            maybe_paren outer (inm, opprio) (fun fmt () -> pp fmt) fmt
          in
            Some pp
    end

    | _ -> None

  and try_pp_as_binop () =
    match es with
    | [e1; e2] when opname = EcCoreLib.s_cons -> begin
      let module E = struct exception NotAListLiteral end in

      try
        let aslist =
          let rec destruct e =
            match dt_sub e with
            | Some (op, _tvi, [e1; e2])
                when EcPath.basename op = EcCoreLib.s_cons
                -> e1 :: destruct e2

            | Some (op, _tvi, [])
                when EcPath.basename op = EcCoreLib.s_nil
                -> []

            | _ -> raise E.NotAListLiteral

          in e1 :: (destruct e2) in

        let pp_sub = pp_sub ppe (inm, (min_op_prec, `NonAssoc)) in
        let pp fmt = fun () ->
          Format.fprintf fmt "[@[<hov 2>%a@]]"
            (pp_list ";@ " pp_sub) aslist
        in
          Some pp

      with E.NotAListLiteral ->
        let pp fmt =
          Format.fprintf fmt "%a :: %a"
            (pp_sub ppe (inm, (e_bin_prio_rop4, `Left ))) e1
            (pp_sub ppe (inm, (e_bin_prio_rop4, `Right))) e2 in
        let opprio_left =
          match lwr_left ppe t_ty e2 inm e_bin_prio_rop4 with
          | None   -> e_bin_prio_rop4
          | Some n ->
              if n <= fst e_bin_prio_rop4
              then (n, snd e_bin_prio_rop4)
              else e_bin_prio_rop4 in
        let pp fmt =
          maybe_paren_gen outer (inm, e_bin_prio_rop4, opprio_left)
          (fun fmt () -> pp fmt) fmt in
        Some pp
      end

    | [e1; e2] -> begin
      match priority_of_binop opname with
      | None -> None
      | Some opprio ->
          let pp fmt =
            Format.fprintf fmt "@[%a %s@ %a@]"
              (pp_sub ppe (inm, (opprio, `Left))) e1
              opname
              (pp_sub ppe (inm, (opprio, `Right))) e2 in
          let opprio_left =
            match lwr_left ppe t_ty e2 inm opprio with
            | None   -> opprio
            | Some n ->
                if n <= fst opprio then (n, snd opprio) else opprio in
          let pp fmt =
            maybe_paren_gen outer (inm, opprio, opprio_left)
            (fun fmt () -> pp fmt) fmt
          in
            Some pp

    end

    | _ -> None

  and try_pp_as_post () =
    match es with
    | e :: es when is_pstop opname -> begin
        let pp_head _ _ fmt opname =
          let subpp = pp_sub ppe (fst outer, (e_uni_prio_rint, `NonAssoc)) in
          Format.fprintf fmt "%a%s" subpp e opname in

        let pp_subs = (pp_head, pp_sub) in
        let pp fmt () = pp_app ppe pp_subs outer fmt (opname, es) in
        Some (maybe_paren outer (inm, max_op_prec) pp)
      end

    | _ ->
       None

  and try_pp_special () =
    let qs = P.toqsymbol op in
    match es with
    | [] when qs = EcCoreLib.s_dbool ->
        Some (fun fmt () -> pp_string fmt "{0,1}")

    | [e] when qs = EcCoreLib.s_dbitstring ->
        let pp fmt () =
          Format.fprintf fmt "{0,1}~%a"
            (pp_sub ppe (fst outer, (max_op_prec, `NonAssoc))) e
        in
          Some pp

    | [e1; e2] when qs = EcCoreLib.s_dinter ->
        let pp fmt () =
          Format.fprintf fmt "[%a..%a]"
            (pp_sub ppe (fst outer, (min_op_prec, `NonAssoc))) e1
            (pp_sub ppe (fst outer, (min_op_prec, `NonAssoc))) e2
        in
          Some pp

    | _ -> None

  and try_pp_record () =
    let env = ppe.PPEnv.ppe_env in

    match EcEnv.Op.by_path_opt op env with
    | Some op when EcDecl.is_rcrd op -> begin

      let recp = EcDecl.operator_as_rcrd op in

      match EcEnv.Ty.by_path_opt recp env with
      | Some { tyd_type = `Record (_, fields) }
          when List.length fields = List.length es
        -> begin
          let wmap =
            List.fold_left (fun m e ->
              match is_proj recp e with
              | None -> m
              | Some (var, idx) ->
                  Mid.change
                    (fun x -> Some (Sint.add idx (odfl Sint.empty x)))
                    var m
            ) Mid.empty es in

          let wmap =
            List.sort
              (fun (_, x) (_, y) ->
                compare (Sint.cardinal x) (Sint.cardinal y))
              (Mid.bindings wmap) in

          let wmap =
            let n = List.length fields in
            List.filter (fun (_, x) -> Sint.cardinal x <> n) wmap in

          match List.Exceptionless.hd wmap with
          | None ->
              let pp fmt () =
                let pp_field fmt ((name, _), e) =
                  Format.fprintf fmt "%s =@ %a" name
                    (pp_sub ppe (fst outer, (min_op_prec, `NonAssoc))) e
                in
                  Format.fprintf fmt "{|@[<hov 2> %a;@ @]|}"
                    (pp_list ";@ " pp_field) (List.combine fields es)
              in Some pp

          | Some (x, idxs) ->
              let fields = List.combine fields es in
              let fields = List.pmapi
                (fun i x -> if Sint.mem i idxs then None else Some x)
                fields in

              let pp fmt () =
                let pp_field fmt ((name, _), e) =
                  Format.fprintf fmt "%s =@ %a" name
                    (pp_sub ppe (fst outer, (min_op_prec, `NonAssoc))) e
                in
                  Format.fprintf fmt "{| %a with @[<hov 2> %a;@ @]|}"
                    (pp_local ppe) x
                    (pp_list ";@ " pp_field) fields
              in Some pp
      end

      | _ -> None

    end

    | _ -> None

  and try_pp_proj () =
    let env = ppe.PPEnv.ppe_env in
      match es, EcEnv.Op.by_path_opt op env with
      | [arg], Some op when EcDecl.is_proj op ->
          let pp fmt () =
            Format.fprintf fmt "%a.`%a"
              (pp_sub ppe (fst outer, (max_op_prec, `NonAssoc))) arg
              pp_opname (nm, opname)
          in
            Some pp
      | arg :: args, Some op when EcDecl.is_proj op ->
          let pp fmt =
            Format.fprintf fmt "%a.`%a%(%)%a"
              (pp_sub ppe (fst outer, (max_op_prec, `NonAssoc))) arg
              pp_opname (nm, opname)
              (if List.is_empty args then "" else "@ ")
              (pp_list "@ " (pp_sub ppe (fst outer, (max_op_prec, `NonAssoc))))
              args in
          let pp fmt =
            maybe_paren outer (inm, e_app_prio) (fun fmt () -> pp fmt) fmt
          in
            Some pp
      | _ -> None

  in
    (odfl
       pp_as_std_op
       (List.fpick [try_pp_special ;
                    try_pp_as_uniop;
                    try_pp_as_binop;
                    try_pp_as_post ;
                    try_pp_record  ;
                    try_pp_proj    ;])) fmt ()

(* -------------------------------------------------------------------- *)
let pp_chained_orderings (ppe : PPEnv.t) t_ty pp_sub outer fmt (f, fs) =
  match fs with
  | [] -> pp_sub ppe outer fmt f
  | _  ->
    Format.fprintf fmt "@[%t%t@]"
      (fun fmt -> pp_sub ppe (fst outer, (e_bin_prio_order, `Left)) fmt f)
      (fun fmt ->
        ignore (List.fold_left
          (fun fe (op, tvi, f) ->
            let (nm, opname) =
              PPEnv.op_symb ppe op (Some (`Form, tvi, [t_ty fe; t_ty f]))
            in
              Format.fprintf fmt " %t@ %a"
                (fun fmt ->
                  match nm with
                  | [] -> Format.fprintf fmt "%s" opname
                  | _  -> pp_opname fmt (nm, opname))
                (pp_sub ppe (fst outer, (e_bin_prio_order, `Right))) f;
              f)
          f fs))

(* -------------------------------------------------------------------- *)
let pp_locbind (ppe : PPEnv.t) ?fv (xs, ty) =
  let tenv1 = PPEnv.add_locals ppe xs in
  let pp fmt =
    Format.fprintf fmt "(%a : %a)"
    (pp_list "@ " (pp_local ?fv tenv1)) xs (pp_type  ppe) ty
  in
    (tenv1, pp)

(* -------------------------------------------------------------------- *)
let rec pp_locbinds_blocks ppe ?fv vs =
  match vs with
  | [] ->
      (ppe, fun _ -> ())

  | [v] ->
      let ppe, pp = pp_locbind ppe ?fv v in
      (ppe, fun fmt -> Format.fprintf fmt "%t" pp)

  | v :: vs ->
      let ppe, pp1 = pp_locbind ppe ?fv v in
      let ppe, pp2 = pp_locbinds_blocks ppe ?fv vs in
      (ppe, fun fmt -> Format.fprintf fmt "%t@ %t" pp1 pp2)

(* -------------------------------------------------------------------- *)
let pp_locbinds ppe ?fv vs =
  let rec merge_r (xs, ty) vs =
    match vs with
    | [] ->
        [List.rev xs, ty]
    | (x, ty') :: vs when EcTypes.ty_equal ty ty' ->
        merge_r (x :: xs, ty) vs
    | (x, ty') :: vs ->
       (List.rev xs, ty) :: (merge_r ([x], ty') vs)

  and merge = function
    | [] -> [] | (x, ty) :: vs -> merge_r ([x], ty) vs in

  pp_locbinds_blocks ppe ?fv (merge vs)

(* -------------------------------------------------------------------- *)
let string_of_quant = function
  | Lforall -> "forall"
  | Lexists -> "exists"
  | Llambda -> "fun"

(* -------------------------------------------------------------------- *)
let string_of_hcmp = function
  | FHle -> "<="
  | FHeq -> "="
  | FHge -> ">="

(* -------------------------------------------------------------------- *)
let string_of_locality = function
  | `Global  -> None
  | `Local   -> Some "local "
  | `Declare -> Some "declare "

let pp_locality fmt lc =
  Format.fprintf fmt "%s" (odfl "" (string_of_locality lc))

(* -------------------------------------------------------------------- *)
let string_of_cpos1 ((off, cp) : EcParsetree.codepos1) =
  let s =
    match cp with
    | `ByPos i ->
        string_of_int i

    | `ByMatch (i, k) ->
        let s =
          let k =
            match k with
            | `If     -> "if"
            | `While  -> "while"
            | `Assign -> "<-"
            | `Sample -> "<$"
            | `Call   -> "<@"
          in Printf.sprintf "^%s" k in

        match i with
        | None | Some 1 -> s
        | Some i -> Printf.sprintf "%s{%d}" s i
  in

  if off = 0 then s else

  Printf.sprintf "%s%s%d" s (if off < 0 then "-" else "+") (abs off)

(* -------------------------------------------------------------------- *)
(* suppose g is a formula consisting of the application of a binary
   operator op with scope onm and precedence opprec to formula
   arguments [_; f]. Because f may end with an implication,
   if-then-else or let expression (which are not guarded by ends, and
   which the pretty printing algorithm won't guard with a close
   parenthesis - see maybe_paren), when deciding whether to
   parenthesize g when it appears to the *left* of an infix operator,
   we may need to decrease the precedence of op, as implemented by
   this function. see maybe_paren_gen for how this precedence is
   used *)

let lower_left (ppe : PPEnv.t) (t_ty : form -> EcTypes.ty) (f : form)
               (onm : EcSymbols.symbol list) (opprec : opprec)
      : int option =
  let rec l_l f onm opprec =
    match f.f_node with
    | Fquant _ -> Some (fst e_bin_prio_lambda)
    | Fif _    -> Some (fst e_bin_prio_if)
    | Flet _   -> Some (fst e_bin_prio_letin)
    | Fapp ({f_node = Fop (op, _)}, [f1; f2])
        when EcPath.basename op = EcCoreLib.s_cons ->
        if fst e_bin_prio_rop4 < fst opprec
        then None
        else l_l f2 onm e_bin_prio_rop4
    | Fapp ({f_node = Fop (op, tys)}, [f1; f2]) ->
        (let (inm, opname) =
           PPEnv.op_symb ppe op (Some (`Form, tys, List.map t_ty [f1; f2])) in
         if inm <> [] && inm <> onm
         then None
         else match priority_of_binop opname with
              | None         -> None
              | Some opprec' ->
                  if fst opprec' < fst opprec || snd opprec = `Infix `Left
                  then None
                  else l_l f2 inm opprec')
    | _ -> None in
  l_l f onm opprec

(* -------------------------------------------------------------------- *)
let rec pp_lvalue (ppe : PPEnv.t) fmt lv =
  match lv with
  | LvVar (p, _) ->
      pp_pv ppe fmt p

  | LvTuple ps ->
      Format.fprintf fmt "@[<hov 2>%a@]"
        (pp_paren (pp_list ",@ " (pp_pv ppe))) (List.map fst ps)

(* -------------------------------------------------------------------- *)
and pp_instr_for_form (ppe : PPEnv.t) fmt i =
  match i.i_node with
  | Sasgn (lv, e) -> begin
      match lv, EcTypes.split_args e with
      | LvVar (x, _), ({ e_node = Eop (op, _) }, [ { e_node = Evar y }; k; v])
          when (EcPath.basename op = EcCoreLib.s_set) && (EcTypes.pv_equal x y) ->

        Format.fprintf fmt "%a.[%a] <-@;<1 2>%a"
          (pp_pv ppe) x (pp_tuple_expr ppe) k (pp_expr ppe) v

      | _, _ ->
        Format.fprintf fmt "%a <-@;<1 2>%a"
          (pp_lvalue ppe) lv (pp_expr ppe) e
    end

  | Srnd (lv, e) ->
      Format.fprintf fmt "%a <$@;<1 2>$%a"
        (pp_lvalue ppe) lv (pp_expr ppe) e

  | Scall (None, xp, args) ->
      Format.fprintf fmt "%a(@[<hov 0>%a@]);"
        (pp_funname ppe) xp
        (pp_list ",@ " (pp_expr ppe)) args

  | Scall (Some lv, xp, args) ->
      Format.fprintf fmt "%a <@@@;<1 2>@[%a(@[<hov 0>%a@]);@]"
        (pp_lvalue ppe) lv
        (pp_funname ppe) xp
        (pp_list ",@ " (pp_expr ppe)) args

  | Sassert e ->
      Format.fprintf fmt "assert %a;"
        (pp_expr ppe) e

  | Swhile (e, _) ->
      Format.fprintf fmt "while (%a) {...}"
        (pp_expr ppe) e

  | Smatch (e, _) ->
      Format.fprintf fmt "match (%a) {...}"
        (pp_expr ppe) e

  | Sif (e, _, _) ->
      Format.fprintf fmt "if (%a) {...}"
        (pp_expr ppe) e

  | Sabstract id -> (* FIXME *)
      Format.fprintf fmt "%s" (EcIdent.name id)

(* -------------------------------------------------------------------- *)
and pp_stmt_for_form (ppe : PPEnv.t) fmt (s : stmt) =
  match s.s_node with
  | [] ->
      pp_string fmt "<skip>"

  | [i] ->
      pp_instr_for_form ppe fmt i

  | [i1; i2] ->
      Format.fprintf fmt "%a;@ %a"
        (pp_instr_for_form ppe) i1
        (pp_instr_for_form ppe) i2

  | _ ->
      let i1 = List.hd s.s_node in
      let i2 = List.hd (List.rev s.s_node) in
        Format.fprintf fmt "%a;@ ...;@ %a"
          (pp_instr_for_form ppe) i1
          (pp_instr_for_form ppe) i2

(* -------------------------------------------------------------------- *)
and try_pp_form_eqveq (ppe : PPEnv.t) _outer fmt f =
  let rec collect1 f =
    match sform_of_form f with
    | SFeq ({ f_node = Fpvar (x1, me1) },
            { f_node = Fpvar (x2, me2) })
        when (EcMemory.mem_equal me1 EcFol.mleft )
          && (EcMemory.mem_equal me2 EcFol.mright)
        ->

      let pv1 = msymbol_of_pv (PPEnv.enter_by_memid ppe EcFol.mleft ) x1 in
      let pv2 = msymbol_of_pv (PPEnv.enter_by_memid ppe EcFol.mright) x2 in

      if pv1 = pv2 then Some (`Var pv1) else None

    | SFeq ({ f_node = Fglob (x1, me1) },
            { f_node = Fglob (x2, me2) })
        when (EcMemory.mem_equal me1 EcFol.mleft )
          && (EcMemory.mem_equal me2 EcFol.mright)
        ->

      let pv1 = (PPEnv.mod_symb ppe x1) in
      let pv2 = (PPEnv.mod_symb ppe x2) in

      if pv1 = pv2 then Some (`Glob pv1) else None

    | SFeq ({ f_node = Fproj (f1, i1); f_ty = ty1 },
            { f_node = Fproj (f2, i2); f_ty = ty2 }) -> begin
      try
        let x1 = get_f_projarg ppe f1 i1 ty1 in
        let x2 = get_f_projarg ppe f2 i2 ty2 in
        collect1 (f_eq x1 x2)
       with NoProjArg -> None
    end

    | _ -> None

  and collect acc f =
    match collect1 f with
    | Some pv -> Some (List.rev (pv :: acc))
    | None    ->
      if EcFol.is_and f then
        let (f1, f2) = EcFol.destr_and f in
          match collect1 f1 with
          | None    -> None
          | Some pv -> collect (pv :: acc) f2
      else
        None
  in

  match collect [] f with
  | None     -> false
  | Some pvs ->
    let pp_msymbol fmt = function
      | `Var  ms -> pp_msymbol fmt ms
      | `Glob ms -> Format.fprintf fmt "glob %a" pp_msymbol ms in
    Format.fprintf fmt "={@[<hov 2>%a@]}" (pp_list ",@ " pp_msymbol) pvs;
    true

and try_pp_chained_orderings (ppe : PPEnv.t) outer fmt f =
  let isordering op =
    match EcIo.lex_single_token (EcPath.basename op) with
    | Some (EP.LE | EP.LT | EP.GE | EP.GT) -> true
    | _ -> false
  in

  let rec collect acc le f =
    match sform_of_form f with
    | SFand (`Asym, (f1, f2)) -> begin
        match f2.f_node with
        | Fapp ({ f_node = Fop (op, tvi) }, [i1; i2])
            when isordering op
          -> begin
            match le with
            | None ->
                collect ((op, tvi, i2) :: acc) (Some i1) f1
            | Some le when EcFol.f_equal i2 le ->
                collect ((op, tvi, i2) :: acc) (Some i1) f1
            | _ -> None
          end

        | _ -> None
    end

    | SFop ((op, tvi), [i1; i2]) when isordering op -> begin
        match le with
        | None ->
            Some (i1, ((op, tvi, i2) :: acc))
        | Some le when EcFol.f_equal i2 le ->
            Some (i1, ((op, tvi, i2) :: acc))
        | _ -> None
      end

    | _ -> None
  in
    match collect [] None f with
    | None | Some (_, ([] | [_])) -> false
    | Some (f, fs) ->
        pp_chained_orderings ppe f_ty pp_form_r outer fmt (f, fs);
        true

and try_pp_lossless (ppe : PPEnv.t) outer fmt f =
  match EcFol.is_bdHoareF f with
  | false -> false
  | true  ->
      let hbd  = EcFol.destr_bdHoareF f in
      let isls =
           EcFol.f_equal EcFol.f_true hbd.bhf_pr
        && EcFol.f_equal EcFol.f_true hbd.bhf_po
        && EcFol.f_equal EcFol.f_r1   hbd.bhf_bd
        && hbd.bhf_cmp = EcFol.FHeq
      in
        match isls with
        | false -> false
        | true  ->
            let prio = (e_uni_prio_lsless, `Prefix) in
            let pp fmt () =
              Format.fprintf fmt "islossless %a" (pp_funname ppe) hbd.bhf_f
            in
              maybe_paren outer (fst outer, prio) pp fmt (); true

and try_pp_notations (ppe : PPEnv.t) outer fmt f =
  let open EcMatching in

  let try_notation (p, (tv, nt)) =
    if not (Sp.mem p ppe.PPEnv.ppe_fb) then begin
      let na   =
          List.length nt.ont_args
        + List.length (snd (EcTypes.split_args nt.ont_body)) in
      let oty  = f.f_ty in
      let f, a = split_args f in
      let f, a =
        if na < List.length a then
          let a1, a2 = List.split_at na a in
          f_app f a1 (toarrow (List.map f_ty a2) oty), a2
        else f_app f a oty, [] in
      let ev   = MEV.of_idents (List.map fst nt.ont_args) `Form in
      let ue   = EcUnify.UniEnv.create None in
      let ov   = EcUnify.UniEnv.opentvi ue tv None in
      let ti   = Tvar.subst ov in
      let hy   = EcEnv.LDecl.init ppe.PPEnv.ppe_env [] in
      let mr   = odfl mhr (EcEnv.Memory.get_active ppe.PPEnv.ppe_env) in
      let bd   = form_of_expr mr nt.ont_body in
      let bd   = Fsubst.subst_tvar ov bd in

      try
        let (ue, ev) =
          EcMatching.f_match_core fmnotation hy (ue, ev) ~ptn:bd f
        in

        if not (EcMatching.can_concretize ev ue) then
          raise EcMatching.MatchFailure;

        let rty  = ti nt.ont_resty in
        let tv   = List.map (ti |- tvar |- fst) tv in
        let args = List.map (curry f_local |- snd_map ti) nt.ont_args in
        let f    = f_op p tv (toarrow tv rty) in
        let f    = f_app f args rty in
        let f    = Fsubst.f_subst (EcMatching.MEV.assubst ue ev) f in
        let f    = f_app f a oty in
        pp_form_core_r ppe outer fmt f; true

      with EcMatching.MatchFailure ->
        false
    end else false

  in let try_notation ((_, (_, nt)) as args) =
     not nt.ont_ponly && try_notation args
  in

  let nts = EcEnv.Op.get_notations ppe.PPEnv.ppe_env in

  List.exists try_notation nts

and pp_form_core_r (ppe : PPEnv.t) outer fmt f =
  let pp_opapp ppe outer fmt (op, tys, es) =
    let rec dt_sub f =
      match destr_app f with
      | ({ f_node = Fop (p, tvi) }, args) -> Some (p, tvi, args)
      | _ -> None

    and is_trm f =
      match f.f_node with
      | Ftuple [f] -> is_trm f
      | Fint _ | Flocal _ | Fpvar _ | Fop _ | Ftuple _ -> true
      | _ -> false

    and is_tuple f =
      match f.f_node with
      | Ftuple ((_ :: _ :: _) as xs) -> Some xs
      | _ -> None

    and is_proj (rc : EcPath.path) (f : form) =
      match f.f_node with
      | Fapp ({ f_node = Fop (p, _) }, [{ f_node = Flocal x }]) -> begin
          match (EcEnv.Op.by_path p ppe.PPEnv.ppe_env).op_kind with
          | OB_oper (Some (OP_Proj (rc', i, _))) when EcPath.p_equal rc rc' ->
              Some (x, i)
          | _ -> None
      end
      | _ -> None

    in
      pp_opapp ppe f_ty
        (dt_sub, pp_form_r, is_trm, is_tuple, is_proj)
        lower_left outer fmt (`Form, op, tys, es)
  in

  match f.f_node with
  | Fint n ->
      Format.fprintf fmt "%a" BI.pp_print n

  | Flocal id ->
      pp_local ppe fmt id

  | Fpvar (x, i) -> begin
    match EcEnv.Memory.get_active ppe.PPEnv.ppe_env with
    | Some i' when EcMemory.mem_equal i i' ->
        Format.fprintf fmt "%a" (pp_pv ppe) x
    | _ ->
        let ppe = PPEnv.enter_by_memid ppe i in
        Format.fprintf fmt "%a{%a}" (pp_pv ppe) x (pp_mem ppe) i
    end

  | Fglob (mp, i) -> begin
    match EcEnv.Memory.get_active ppe.PPEnv.ppe_env with
    | Some i' when EcMemory.mem_equal i i' ->
        Format.fprintf fmt "(glob %a)" (pp_topmod ppe) mp
    | _ ->
        let ppe = PPEnv.enter_by_memid ppe i in
        Format.fprintf fmt "(glob %a){%a}" (pp_topmod ppe) mp (pp_mem ppe) i
    end

  | Fquant (q, bd, f) ->
      let (subppe, pp) = pp_bindings ppe ~fv:f.f_fv bd in
      let pp fmt () =
        match q with
        | Llambda ->
          Format.fprintf fmt "@[<hov 2>%s %t =>@ %a@]"
            (string_of_quant q) pp
            (pp_form subppe) f
        | _ ->
          Format.fprintf fmt "@[<hov 2>%s %t,@ %a@]"
            (string_of_quant q) pp
            (pp_form subppe) f in
      maybe_paren outer (fst outer, e_bin_prio_lambda) pp fmt ()

  | Fif (b, f1, f2) ->
      pp_if_form ppe pp_form_r outer fmt (b, f1, f2)

  | Fmatch (b, bs, _) ->
      pp_match_form ppe pp_form_r outer fmt (b, bs)

  | Flet (lp, f1, f2) ->
      pp_let ~fv:f2.f_fv ppe pp_form_r outer fmt (lp, f1, f2)

  | Fop (op, tvi) ->
      pp_opapp ppe outer fmt (op, tvi, [])

  | Fapp ({f_node = Fop (op, _)},
            [{f_node = Fapp ({f_node = Fop (op', tys)}, [f1; f2])}])
      when EcPath.p_equal op  EcCoreLib.CI_Bool.p_not
        && EcPath.p_equal op' EcCoreLib.CI_Bool.p_eq
    ->
      let negop = EcPath.pqoname (EcPath.prefix op') "<>" in
      pp_opapp ppe outer fmt (negop, tys, [f1; f2])

  | Fapp ({f_node = Fop (p, tys)}, args) ->
      pp_opapp ppe outer fmt (p, tys, args)

  | Fapp (e, args) ->
      pp_app ppe (pp_form_r, pp_form_r) outer fmt (e, args)

  | Ftuple args ->
      pp_tuple `ForTuple ppe pp_form_r (fst outer) fmt args

  | Fproj (e1, i) -> begin
      try
        let v = get_f_projarg ppe e1 i f.f_ty in
        pp_form_core_r ppe outer fmt v
      with NoProjArg ->
        pp_proji ppe pp_form_r (fst outer) fmt (e1,i)
    end

  | FhoareF hf ->
      let mepr, mepo = EcEnv.Fun.hoareF_memenv hf.hf_f ppe.PPEnv.ppe_env in
      let ppepr = PPEnv.create_and_push_mem ppe ~active:true mepr in
      let ppepo = PPEnv.create_and_push_mem ppe ~active:true mepo in
      Format.fprintf fmt "hoare[@[<hov 2>@ %a :@ @[%a ==>@ %a@]@]]"
        (pp_funname ppe) hf.hf_f
        (pp_form ppepr) hf.hf_pr
        (pp_form ppepo) hf.hf_po

  | FhoareS hs ->
      let ppe = PPEnv.push_mem ppe ~active:true hs.hs_m in
      Format.fprintf fmt "hoare[@[<hov 2>@ %a :@ @[%a ==>@ %a@]@]]"
        (pp_stmt_for_form ppe) hs.hs_s
        (pp_form ppe) hs.hs_pr
        (pp_form ppe) hs.hs_po

  | FequivF eqv ->
      let (meprl, meprr), (mepol,mepor) =
        EcEnv.Fun.equivF_memenv eqv.ef_fl eqv.ef_fr ppe.PPEnv.ppe_env in
      let ppepr = PPEnv.create_and_push_mems ppe [meprl; meprr] in
      let ppepo = PPEnv.create_and_push_mems ppe [mepol; mepor] in
      Format.fprintf fmt "equiv[@[<hov 2>@ %a ~@ %a :@ @[%a ==>@ %a@]@]]"
        (pp_funname ppe) eqv.ef_fl
        (pp_funname ppe) eqv.ef_fr
        (pp_form ppepr) eqv.ef_pr
        (pp_form ppepo) eqv.ef_po

  | FequivS es ->
      let ppef = PPEnv.push_mems ppe [es.es_ml; es.es_mr] in
      let ppel = PPEnv.push_mem ppe ~active:true es.es_ml in
      let pper = PPEnv.push_mem ppe ~active:true es.es_mr in
      Format.fprintf fmt "equiv[@[<hov 2>@ %a ~@ %a :@ @[%a ==>@ %a@]@]]"
        (pp_stmt_for_form ppel) es.es_sl
        (pp_stmt_for_form pper) es.es_sr
        (pp_form ppef) es.es_pr
        (pp_form ppef) es.es_po

  | FeagerF eg ->
      let (meprl, meprr), (mepol,mepor) =
        EcEnv.Fun.equivF_memenv eg.eg_fl eg.eg_fr ppe.PPEnv.ppe_env in
      let ppepr = PPEnv.create_and_push_mems ppe [meprl; meprr] in
      let ppepo = PPEnv.create_and_push_mems ppe [mepol; mepor] in
      Format.fprintf fmt "eager[@[<hov 2>@ %a,@ %a ~@ %a,@ %a :@ @[%a ==>@ %a@]@]]"
        (pp_stmt_for_form ppe) eg.eg_sl
        (pp_funname ppe) eg.eg_fl
        (pp_funname ppe) eg.eg_fr
        (pp_stmt_for_form ppe) eg.eg_sr

        (pp_form ppepr) eg.eg_pr
        (pp_form ppepo) eg.eg_po

  | FcHoareF chf ->
    let mepr, mepo = EcEnv.Fun.hoareF_memenv chf.chf_f ppe.PPEnv.ppe_env in
    let ppepr = PPEnv.create_and_push_mem ppe ~active:true mepr in
    let ppepo = PPEnv.create_and_push_mem ppe ~active:true mepo in
    if f_equal chf.chf_pr f_true && f_equal chf.chf_po f_true then
      Format.fprintf fmt "@[<hov 2>choare[@[<hov 2>%a@]]@ time %a@]"
        (pp_funname ppe) chf.chf_f
        (pp_cost ppe) chf.chf_co
    else
      Format.fprintf fmt "@[<hov 2>choare[@[<hov 2>@ %a :@ @[%a ==>@ %a@]@]]\
                          @ time %a@]"
        (pp_funname ppe) chf.chf_f
        (pp_form ppepr) chf.chf_pr
        (pp_form ppepo) chf.chf_po
        (pp_cost ppe) chf.chf_co

  | FcHoareS chs ->
      let ppe = PPEnv.push_mem ppe ~active:true chs.chs_m in
      Format.fprintf fmt "@[<hov 2>choare[@[<hov 2>@ %a :@ @[%a ==>@ %a@]@]]\
                          @ time %a@]"
        (pp_stmt_for_form ppe) chs.chs_s
        (pp_form ppe) chs.chs_pr
        (pp_form ppe) chs.chs_po
        (pp_cost ppe) chs.chs_co

  | FbdHoareF hf ->
      let mepr, mepo = EcEnv.Fun.hoareF_memenv hf.bhf_f ppe.PPEnv.ppe_env in
      let ppepr = PPEnv.create_and_push_mem ppe ~active:true mepr in
      let ppepo = PPEnv.create_and_push_mem ppe ~active:true mepo in
      Format.fprintf fmt "phoare[@[<hov 2>@ %a :@ @[%a ==>@ %a@]@]] %s %a"
        (pp_funname ppe) hf.bhf_f
        (pp_form ppepr) hf.bhf_pr
        (pp_form ppepo) hf.bhf_po
        (string_of_hcmp hf.bhf_cmp)
        (pp_form_r ppepr (fst outer, (max_op_prec,`NonAssoc))) hf.bhf_bd

  | FbdHoareS hs ->
      let ppef = PPEnv.push_mem ppe ~active:true hs.bhs_m in
      Format.fprintf fmt "phoare[@[<hov 2>@ %a :@ @[%a ==>@ %a@]@]] %s %a"
        (pp_stmt_for_form ppef) hs.bhs_s
        (pp_form ppef) hs.bhs_pr
        (pp_form ppef) hs.bhs_po
        (string_of_hcmp hs.bhs_cmp)
        (pp_form_r ppef (fst outer, (max_op_prec,`NonAssoc))) hs.bhs_bd

  | Fcoe coe ->
      let ppe = PPEnv.push_mem ppe ~active:true coe.coe_mem in
      let m, mt = coe.coe_mem in
      let ppe = PPEnv.add_local ppe m in
      let pp fmt =
        if EcMemory.is_schema mt
        then ()
        else if EcMemory.for_printing mt = None
        then Format.fprintf fmt "%a" (pp_local ppe) m
        else
          Format.fprintf fmt "(%a: %a)"
            (pp_local ~fv:coe.coe_pre.f_fv ppe) m
            (pp_memtype ppe) mt in

      Format.fprintf fmt "@[<hv 2>cost@[%t@]@,[@[<hov 2>@[%a@] :@ @[%a@]@]]@]"
        pp
        (pp_form ppe) coe.coe_pre
        (pp_expr ppe) coe.coe_e

  | Fpr pr->
      let me = EcEnv.Fun.prF_memenv EcFol.mhr pr.pr_fun ppe.PPEnv.ppe_env in

      let ppep = PPEnv.create_and_push_mem ppe ~active:true me in
      Format.fprintf fmt "Pr[@[%a@[%t@] @@ %a :@ %a@]]"
        (pp_funname ppe) pr.pr_fun
        (match pr.pr_args.f_node with
         | Ftuple _ ->
             (fun fmt -> pp_form ppe fmt pr.pr_args)
         | _ when EcFol.f_equal f_tt pr.pr_args ->
             (fun fmt -> pp_string fmt "()")
         | _ ->
             (fun fmt -> Format.fprintf fmt "(%a)" (pp_form ppe) pr.pr_args))
        (pp_local ppe) pr.pr_mem
        (pp_form ppep) pr.pr_event

and pp_form_r (ppe : PPEnv.t) outer fmt f =
  let printers =
    [try_pp_notations;
     try_pp_form_eqveq;
     try_pp_chained_orderings;
     try_pp_lossless]
  in

  match List.ofind (fun pp -> pp ppe outer fmt f) printers with
  | Some _ -> ()
  | None   -> pp_form_core_r ppe outer fmt f

and pp_form ppe fmt f =
  pp_form_r ppe ([], (min_op_prec, `NonAssoc)) fmt f

and pp_expr ppe fmt e =
  let mr = odfl mhr (EcEnv.Memory.get_active ppe.PPEnv.ppe_env) in
  pp_form ppe fmt (form_of_expr mr e)

and pp_tuple_expr ppe fmt e =
  match e.e_node with
  | Etuple ((_ :: _ :: _) as es) ->
    pp_list ", " (pp_expr ppe) fmt es
  | _ -> pp_expr ppe fmt e

(* -------------------------------------------------------------------- *)
and pp_cost ppe fmt c =
  let pp_el fmt (f,c) = match f with
    | None ->
      pp_form ppe fmt c
    | Some (f, _f_cost) ->
      Format.fprintf fmt "%a : %a"
        (pp_funname ppe) f
        (pp_form ppe) c
      (* We can print_f_cost here, for debugging purposes. *)
      (* Format.fprintf fmt "%a `{%a} : %a"
       *   (pp_funname ppe) f
       *   (pp_form ppe) _f_cost
       *   (pp_form ppe) c  *)
  in

  Format.fprintf fmt "@[<hv 1>[%a]@]"
    (pp_list ";@ " pp_el)
    (   (None,c.c_self)
     :: (EcPath.Mx.bindings c.c_calls
         |> List.map (fun (x,y) -> (Some (x, y.cb_cost), y.cb_called))))

(* -------------------------------------------------------------------- *)
and pp_allowed_orcl ppe fmt orcls =
  if orcls = [] then Format.fprintf fmt ""
  else
    Format.fprintf fmt "{@[<hov>%a@]}@ "
      (pp_list ",@ " (pp_funname ppe)) orcls

and pp_costs ppe fmt costs = match costs with
  | `Unbounded ->
    Format.fprintf fmt ""
  | `Bounded (self,calls) ->
    let pp_cost fmt (f,c) =
      Format.fprintf fmt "@[%a : %a@]"
        (pp_funname ppe) f
        (pp_form ppe) c in

    let bindings = (EcPath.Mx.bindings calls) in
    Format.fprintf fmt "`{@[<hv>%a%t%a@]}@ "
      (pp_form ppe) self
      (fun fmt -> Format.fprintf fmt (if bindings = [] then "" else ",@ "))
      (pp_list ",@ " pp_cost) bindings

and pp_orclinfo_bare ppe fmt oi =
  let orcls = OI.allowed oi
  and costs = OI.costs oi in
  Format.fprintf fmt "%a%a"
    (pp_allowed_orcl ppe) orcls
    (pp_costs ppe) costs

and pp_orclinfo ppe fmt (sym, oi) =
  Format.fprintf fmt "@[<hv>%a : %a@]"
    pp_symbol sym
    (pp_orclinfo_bare ppe) oi

and pp_orclinfos ppe fmt mr =
  if not (EcModules.mr_is_empty mr) then
    Format.fprintf fmt "[@[<hv>%a@]]"
      (pp_list ",@ " (pp_orclinfo ppe)) (Msym.bindings mr.mr_oinfos)

(* -------------------------------------------------------------------- *)
and pp_mem_restr ppe fmt mr =
  let pp_rx sign fmt rx =
    let pp_x fmt x =
      Format.fprintf fmt "%a%a" pp_restr_s sign (pp_pv ppe) (pv_glob x) in
    pp_list ",@ " pp_x fmt (EcPath.Sx.elements rx) in
  let pp_r sign fmt r =
    let pp_m fmt m =
      Format.fprintf fmt "%a%a" pp_restr_s sign (pp_topmod ppe) m in
    pp_list ",@ " pp_m fmt (EcPath.Sm.elements r) in
  let pp_top fmt b =
    if b then Format.fprintf fmt "%s" all_mem_sym else () in

  let xpos_emp =
    EcPath.Sx.is_empty (odfl EcPath.Sx.empty mr.mr_xpaths.ur_pos) in
  let mpos_emp =
    (EcPath.Sm.is_empty (odfl EcPath.Sm.empty mr.mr_mpaths.ur_pos)) in
  let all_mem =
    mr.mr_xpaths.ur_pos = None || mr.mr_mpaths.ur_pos = None in

  let printed = ref (all_mem) in
  let pp_sep fmt b =
    let b' = (not b) && !printed in
    printed := !printed || not b;
    if b' then Format.fprintf fmt ",@ " else () in

  if all_mem &&
     EcPath.Sm.is_empty mr.mr_mpaths.ur_neg &&
     EcPath.Sx.is_empty mr.mr_xpaths.ur_neg
  then ()
  else Format.fprintf fmt "@[<h>{%a%a%a%a%a%a%a%a%a}@]@ "
      pp_top (all_mem)
      pp_sep xpos_emp
      (pp_rx true) (odfl EcPath.Sx.empty mr.mr_xpaths.ur_pos)
      pp_sep mpos_emp
      (pp_r true) (odfl EcPath.Sm.empty mr.mr_mpaths.ur_pos)
      pp_sep (EcPath.Sx.is_empty mr.mr_xpaths.ur_neg)
      (pp_rx false) mr.mr_xpaths.ur_neg
      pp_sep (EcPath.Sm.is_empty mr.mr_mpaths.ur_neg)
      (pp_r false) mr.mr_mpaths.ur_neg

(* -------------------------------------------------------------------- *)
(* Use in an hv box. *)
and pp_restr ppe fmt mr =
  Format.fprintf fmt "%a%a"
    (pp_mem_restr ppe) mr
    (pp_orclinfos ppe) mr

(* -------------------------------------------------------------------- *)
and pp_modtype (ppe : PPEnv.t) fmt (mty : module_type) =
  Format.fprintf fmt "@[<hv 2>%a%a@]"
    (pp_modtype1 ppe) mty (pp_restr ppe) mty.mt_restr

(* -------------------------------------------------------------------- *)
and pp_binding ?(break = true) ?fv (ppe : PPEnv.t) (xs, ty) =
  let pp_local = pp_local ?fv in
  let pp_sep : _ format6 = if break then "@ " else " " in

  match ty with
  | GTty ty ->
      let tenv1  = PPEnv.add_locals ppe xs in
      let pp fmt =
        Format.fprintf fmt "(%a : %a)"
          (pp_list pp_sep (pp_local tenv1)) xs (pp_type ppe) ty
      in
        (tenv1, pp)

  | GTmem m ->
      let tenv1 = PPEnv.add_locals ppe xs in
      let tenv1 =
        PPEnv.create_and_push_mems tenv1 (List.map (fun x -> (x,m)) xs) in
      let pp fmt =
        (* if EcMemory.for_printing m = None then *)
          Format.fprintf fmt "%a" (pp_list pp_sep (pp_local tenv1)) xs
        (* else
         *   Format.fprintf fmt "(%a: %a)" (pp_list pp_sep (pp_local tenv1)) xs
         *     (pp_memtype ppe) m *)
      in
        (tenv1, pp)

  | GTmodty mt ->
      let tenv1  = PPEnv.add_mods ppe xs mt in
      let pp fmt =
        let (ppe, pp_params) = pp_mod_params ppe mt.mt_params in
        Format.fprintf fmt "@[<hv>(%a%t <:@;<1 2>%a)@]"
          (pp_list pp_sep (pp_local tenv1)) xs
          pp_params
          (pp_modtype ppe) mt
      in
        (tenv1, pp)

(* -------------------------------------------------------------------- *)
and pp_mod_params ppe bms =
  let pp_mp ppe (id,mt) =
    let ppe1 = PPEnv.add_local ppe id in
    let pp fmt =
      Format.fprintf fmt "%a : %a" (pp_local ppe1) id
        EcSymbols.pp_msymbol (PPEnv.modtype_symb ppe mt) in
    ppe1, pp
  in
  let rec aux ppe bms =
    match bms with
    | [] -> (ppe, fun _ -> ())
    | [bm] ->
      let ppe, pp = pp_mp ppe bm in
      (ppe, fun fmt -> Format.fprintf fmt "%t" pp)
    | bm::bms ->
      let ppe, pp1 = pp_mp ppe bm in
      let ppe, pp2 = aux ppe bms in
      (ppe, fun fmt -> Format.fprintf fmt "%t,@, %t" pp1 pp2) in

  let (ppe, pp) = aux ppe bms in
  let pp fmt =
    if not (List.is_empty bms) then Format.fprintf fmt "@[(%t)@]" pp
  in (ppe, pp)

(* -------------------------------------------------------------------- *)
and pp_bindings_blocks ppe ?(break = true) bds =
  let pp_sep : _ format6 = if break then "@ " else " " in

  match bds with
  | [] ->
      (ppe, fun _ -> ())
  | [(fv,xs,gty)] ->
      let ppe, pp = pp_binding ppe ~break ?fv (xs,gty) in
      (ppe, fun fmt -> Format.fprintf fmt "%t" pp)
  | (fv,xs,gty) :: bds ->
      let ppe, pp1 = pp_binding ppe ~break ?fv (xs,gty) in
      let ppe, pp2 = pp_bindings_blocks ppe bds in
      (ppe, fun fmt -> Format.fprintf fmt "%t%(%)%t" pp1 pp_sep pp2)

and pp_bindings ppe ?break ?fv bds =
  let rec merge_r (xs, gty) bds =
    match bds with
    | [] ->
       [List.rev xs, gty]
    | (x, gty') :: bds when EcFol.gty_equal gty gty' ->
       merge_r (x :: xs, gty) bds
    | (x, gty') :: bds ->
       (List.rev xs, gty) :: merge_r ([x], gty') bds

  and merge =
    function [] -> [] | (x, gty) :: bds -> merge_r ([x], gty) bds in

  let bds = merge bds in

  (* Variables appearing in the quantified types are free, and must be added
     when printing. *)
  let _, bds = List.fold_right (fun (xs, gty) (fv, bds) ->
      let fv = omap (fun fv -> EcIdent.fv_union (EcFol.gty_fv gty) fv) fv in
      (fv, (fv, xs, gty) :: bds)
    ) bds (fv, []) in

  pp_bindings_blocks ppe ?break bds

(* -------------------------------------------------------------------- *)
let pp_sform ppe fmt f =
  pp_form_r ppe ([], ((100, `Infix `NonAssoc), `NonAssoc)) fmt f

(* -------------------------------------------------------------------- *)
let pp_typedecl (ppe : PPEnv.t) fmt (x, tyd) =
  let ppe = PPEnv.add_locals ppe (List.map fst tyd.tyd_params) in
  let name = P.basename x in

  let pp_prelude fmt =
    match List.map fst tyd.tyd_params with
    | [] ->
        Format.fprintf fmt "type %s" name

    | [tx] ->
        Format.fprintf fmt "type %a %s" (pp_tyvar ppe) tx name

    | txs ->
        Format.fprintf fmt "type %a %s"
          (pp_paren (pp_list ",@ " (pp_tyvar ppe))) txs name

  and pp_body fmt =
    match tyd.tyd_type with
    | `Abstract _ -> ()                (* FIXME: TC HOOK *)

    | `Concrete ty ->
        Format.fprintf fmt " =@ %a" (pp_type ppe) ty

    | `Datatype { tydt_ctors = cs } ->
        let pp_ctor fmt (c, cty) =
          match cty with
          | [] ->
            Format.fprintf fmt "%a" pp_opname ([], c)
          | _  ->
            Format.fprintf fmt "%a of @[<hov 2>%a@]"
              pp_opname ([], c) (pp_list " &@ " (pp_stype ppe)) cty
        in
          Format.fprintf fmt " =@ [@[<hov 2>%a@]]" (pp_list " |@ " pp_ctor) cs

    | `Record (_, fields) ->
        let pp_field fmt (f, fty) =
          Format.fprintf fmt "%s: @[<hov 2>%a@]" f (pp_type ppe) fty
        in
          Format.fprintf fmt " = {@ @[<hov 2>%a;@]@ }"
            (pp_list ";@ " pp_field) fields
  in
    Format.fprintf fmt "@[%a%t%t.@]" pp_locality tyd.tyd_loca pp_prelude pp_body

(* -------------------------------------------------------------------- *)
let pp_tyvar_ctt (ppe : PPEnv.t) fmt (tvar, ctt) =
  match EcPath.Sp.elements ctt with
  | []  -> pp_tyvar ppe fmt tvar
  | ctt ->
      Format.fprintf fmt "%a <: %a"
        (pp_tyvar ppe) tvar
        (pp_list " &@ " (pp_tcname ppe)) ctt

(* -------------------------------------------------------------------- *)
let pp_tyvarannot (ppe : PPEnv.t) fmt ids =
  match ids with
  | []  -> ()
  | ids -> Format.fprintf fmt "[%a]" (pp_list ",@ " (pp_tyvar_ctt ppe)) ids

let pp_pvar (ppe : PPEnv.t) fmt ids =
  match ids with
  | []  -> ()
  | ids -> Format.fprintf fmt "'{%a}" (pp_list "@ " (pp_tyvar ppe)) ids

let pp_scvar ppe fmt vs =
  let rec grp_vs acc l = match l, acc with
    | [],_ -> List.rev_map (fun (l,ty) -> List.rev l, ty) acc
    | (a,ty) :: l, (l',cty) :: acc ->
      if EcTypes.ty_equal ty cty
      then grp_vs ((a :: l', cty) :: acc) l
      else grp_vs (([a],ty) :: (l', cty) :: acc) l
    | (a,ty) :: l, [] -> grp_vs [[a],ty] l in

  let vs = grp_vs [] vs in

  let pp_grp fmt (l,ty) =
    Format.fprintf fmt "{%a :@ %a}"
      (pp_list "@ " (pp_tyvar ppe)) l (pp_type ppe) ty in

  pp_list "@ " pp_grp fmt vs

(* -------------------------------------------------------------------- *)
let pp_opdecl_pr (ppe : PPEnv.t) fmt (basename, ts, ty, op) =
  let ppe = PPEnv.add_locals ppe (List.map fst ts) in

  let pp_body fmt =
    match op with
    | None -> begin
        match fst (tyfun_flat ty) with
        | [] ->
           Format.fprintf fmt ""
        | [ty] ->
           Format.fprintf fmt " : %a" (pp_type ppe) ty
        | dom ->
            Format.fprintf fmt " : %a"
              (pp_list " &@ " (pp_stype ppe)) dom
    end

    | Some (PR_Plain f) ->
        let ((subppe, pp_vds), f) =
          let (vds, f) =
            match f.f_node with
            | Fquant (Llambda, vds, f) -> (vds, f)
            | _ -> ([], f) in

          let vds = List.map (snd_map EcFol.gty_as_ty) vds in
          (pp_locbinds ppe ~fv:f.f_fv vds, f)
        in
          Format.fprintf fmt "%t =@ %a" pp_vds (pp_form subppe) f

    | Some (PR_Ind pri) ->
       let (subppe, pp_vds) = pp_locbinds ppe pri.pri_args in

       let pp_ctor fmt ctor =
         let (specppe, pp_bds) = pp_bindings subppe ctor.prc_bds in

         if List.is_empty ctor.prc_spec then
           Format.fprintf fmt "| %s %t" ctor.prc_ctor pp_bds
         else
           Format.fprintf fmt "| %s %t of %a" ctor.prc_ctor pp_bds
             (pp_list " &@ " (pp_sform specppe)) ctor.prc_spec
       in

       if List.is_empty pri.pri_ctors then
         Format.fprintf fmt "%t = " pp_vds
       else
         Format.fprintf fmt "%t =@\n%a"
           pp_vds (pp_list "@\n" pp_ctor) pri.pri_ctors
  in

  if List.is_empty ts then
    Format.fprintf fmt "@[<hov 2>pred %a %t.@]"
      pp_opname ([], basename) pp_body
  else
    Format.fprintf fmt "@[<hov 2>pred %a %a %t.@]"
      pp_opname ([], basename) (pp_tyvarannot ppe) ts pp_body

(* -------------------------------------------------------------------- *)
let pp_opdecl_op (ppe : PPEnv.t) fmt (basename, ts, ty, op) =
  let ppe = PPEnv.add_locals ppe (List.map fst ts) in

  let pp_nosmt fmt =
    let b =
      match op with
      | None -> false
      | Some (OP_Plain (_, b)) -> b
      | Some (OP_Fix { opf_nosmt = b }) -> b
      | _ -> false
    in if b then Format.fprintf fmt "@ nosmt" else () in

  let pp_body fmt =
    match op with
    | None ->
        Format.fprintf fmt ": %a" (pp_type ppe) ty

    | Some (OP_Plain (e, _)) ->
        let ((subppe, pp_vds), e, has_vds) =
          let (vds, e) =
            match e.e_node with
            | Equant (`ELambda, vds, e) -> (vds, e)
            | _ -> ([], e) in
          (pp_locbinds ppe ~fv:e.e_fv vds, e,
           match vds with [] -> false | _ -> true)
        in
          if has_vds then
            Format.fprintf fmt "%t :@ %a =@ %a" pp_vds
              (pp_type ppe) e.e_ty (pp_expr subppe) e
          else
            Format.fprintf fmt ":@ %a =@ %a"
              (pp_type ppe) e.e_ty (pp_expr subppe) e
    | Some (OP_Constr (indp, i)) ->
        Format.fprintf fmt
          ": %a =@ < %d-th constructor of %a >"
          (pp_type ppe) ty
          (i+1) (pp_tyname ppe) indp

    | Some (OP_Record recp) ->
        Format.fprintf fmt
          ": %a =@ < record constructor of %a >"
          (pp_type ppe) ty
          (pp_tyname ppe) recp

    | Some (OP_Proj (rp, i, _)) ->
        Format.fprintf fmt
          ": %a =@ < %d-th projection of %a >"
          (pp_type ppe) ty
          (i+1) (pp_tyname ppe) rp

    | Some (OP_Fix fix) ->
        let (subppe, pp_vds) = pp_locbinds ppe fix.opf_args in

        let pp_branch fmt br =
          Format.fprintf fmt "with ";
          let brppe =
            List.fold_left (fun brppe br1 ->
              let ctor  = br1.EI.br1_case.EI.cs1_ctor in
              let vars  = List.map fst br1.EI.br1_case.EI.cs1_vars in
              let brppe = List.fold_left PPEnv.add_local brppe vars in

              (match vars with
              | [] ->
                  Format.fprintf fmt "%a = %a"
                    (pp_local subppe) br1.EI.br1_target
                    pp_opname (PPEnv.op_symb ppe ctor None)

              | _ ->
                  Format.fprintf fmt "%a = %a %a"
                    (pp_local subppe) br1.EI.br1_target
                    pp_opname (PPEnv.op_symb ppe ctor None)
                    (pp_list " " (pp_local ppe)) vars);
              brppe)
              subppe br.EI.br_branches
          in
          Format.fprintf fmt " => @[%a@]" (pp_expr brppe) br.EI.br_body in

        let cfix = EcInductive.collate_matchfix fix in

        Format.fprintf fmt "%t : %a = @\n%a" pp_vds
          (pp_type ppe) fix.opf_resty
          (pp_list "@\n" pp_branch) cfix

    | Some (OP_TC) ->
        Format.fprintf fmt "= < type-class-operator >"
  in

  match ts with
  | [] -> Format.fprintf fmt "@[<hov 2>op%t %a %t.@]"
      pp_nosmt pp_opname ([], basename) pp_body
  | _  ->
      Format.fprintf fmt "@[<hov 2>op%t %a %a %t.@]"
        pp_nosmt pp_opname ([], basename) (pp_tyvarannot ppe) ts pp_body

(* -------------------------------------------------------------------- *)
let pp_opdecl_nt (ppe : PPEnv.t) fmt (basename, ts, _ty, nt) =
  let ppe = PPEnv.add_locals ppe (List.map fst ts) in

  let pp_body fmt =
    let subppe, pplocs =
      pp_locbinds ppe ~fv:nt.ont_body.e_fv nt.ont_args
    in
      Format.fprintf fmt "%t :@ %a =@ %a"
        pplocs (pp_type ppe) nt.ont_resty
        (pp_expr subppe) nt.ont_body
  in

  match ts with
  | [] -> Format.fprintf fmt "@[<hov 2>abbrev %a %t.@]"
      pp_opname ([], basename) pp_body
  | _  ->
      Format.fprintf fmt "@[<hov 2>abbrev %a %a %t.@]"
        pp_opname ([], basename) (pp_tyvarannot ppe) ts pp_body

(* -------------------------------------------------------------------- *)
let pp_opdecl ?(long = false) (ppe : PPEnv.t) fmt (x, op) =
  let pp_name fmt x =
    if long then
      let qs = PPEnv.op_symb ppe x None in
      if not (List.is_empty (fst qs)) then
        Format.fprintf fmt "(* %a *)@ " pp_opname qs
  in

  let pp_decl fmt op =
    match op.op_kind with
    | OB_oper i ->
      pp_opdecl_op ppe fmt (P.basename x, op.op_tparams, op_ty op, i)
    | OB_pred i ->
      pp_opdecl_pr ppe fmt (P.basename x, op.op_tparams, op_ty op, i)
    | OB_nott i ->
      let ppe = { ppe with PPEnv.ppe_fb = Sp.add x ppe.PPEnv.ppe_fb } in
      pp_opdecl_nt ppe fmt (P.basename x, op.op_tparams, op_ty op, i)

  in Format.fprintf fmt "@[<v>%a%a%a@]" pp_locality op.op_loca pp_name x pp_decl op

let pp_added_op (ppe : PPEnv.t) fmt op =
  let ppe = PPEnv.add_locals ppe (List.map fst op.op_tparams) in
  match op.op_tparams with
  | [] -> Format.fprintf fmt ": @[<hov 2>%a@]"
    (pp_type ppe) op.op_ty
  | ts  ->
    Format.fprintf fmt "@[<hov 2>%a :@ %a.@]"
      (pp_tyvarannot ppe) ts (pp_type ppe) op.op_ty

(* -------------------------------------------------------------------- *)
let pp_opname (ppe : PPEnv.t) fmt (p : EcPath.path) =
  pp_opname fmt (PPEnv.op_symb ppe p None)


(* -------------------------------------------------------------------- *)
let string_of_axkind = function
  | `Axiom _ -> "axiom"
  | `Lemma   -> "lemma"

let tags_of_axkind = function
  | `Axiom (x, _) -> List.sort sym_compare (Ssym.elements x)
  | `Lemma -> []

let pp_axiom ?(long=false) (ppe : PPEnv.t) fmt (x, ax) =
  let ppe = PPEnv.add_locals ppe (List.map fst ax.ax_tparams) in
  let basename = P.basename x in

  let pp_spec fmt =
    pp_form ppe fmt ax.ax_spec

  and pp_name fmt =
    match ax.ax_tparams with
    | [] -> Format.fprintf fmt "%s"    basename
    | ts -> Format.fprintf fmt "%s %a" basename (pp_tyvarannot ppe) ts

  and pp_tags fmt =
    let tags = tags_of_axkind ax.ax_kind in
    if not (List.is_empty tags) then
      Format.fprintf fmt "[@[%a@]] " (pp_list "@ " pp_symbol) tags
  in

  let pp_long fmt x =
     if long then
       let qs = PPEnv.ax_symb ppe x in
       if fst qs <> [] then
         Format.fprintf fmt "(* %a *)@ " EcSymbols.pp_qsymbol qs in

  let pp_decl fmt () =
    let vs =
      match ax.ax_visibility with
      | `Visible -> []
      | `NoSmt   -> ["nosmt"]
      | `Hidden  -> ["(* hidden *)"] in


    Format.fprintf fmt "@[<hov 2>%a %t%t:@ %t.@]"
      (pp_list " " pp_string)
      (  (otolist (string_of_locality ax.ax_loca))
       @ [string_of_axkind ax.ax_kind]
       @ vs)
      pp_tags pp_name pp_spec in

  Format.fprintf fmt "@[<v>%a%a@]" pp_long x pp_decl ()

let pp_schema ?(long=false) (ppe : PPEnv.t) fmt (x, sc) =
  let ppe = PPEnv.add_locals ppe (List.map fst sc.axs_tparams) in
  let ppe = PPEnv.add_locals ppe sc.axs_pparams in
  let ppe = PPEnv.add_locals ppe (List.map fst sc.axs_params) in
  let basename = P.basename x in

  let pp_spec fmt =
    pp_form ppe fmt sc.axs_spec in

  let pp_w_space pp fmt args = match args with
    | [] -> ()
    | _ -> Format.fprintf fmt " %a" pp args in

  let pp_name fmt =
    Format.fprintf fmt "%s%a%a%a" basename
      (pp_w_space @@ pp_tyvarannot ppe) sc.axs_tparams
      (pp_w_space @@ pp_pvar ppe) sc.axs_pparams
      (pp_w_space @@ pp_scvar ppe) sc.axs_params  in

  let pp_long fmt x =
    if long then
      let qs = PPEnv.sc_symb ppe x in
      if fst qs <> [] then
        Format.fprintf fmt "(* %a *)@ " EcSymbols.pp_qsymbol qs in

  let pp_decl fmt () =
    Format.fprintf fmt "@[<hov 2>schema %t:@ %t.@]"
      pp_name pp_spec in

  Format.fprintf fmt "@[<v>%a%a@]" pp_long x pp_decl ()

(* -------------------------------------------------------------------- *)
type ppnode1 = [
  | `Asgn     of (EcModules.lvalue * EcTypes.expr)
  | `Assert   of (EcTypes.expr)
  | `Call     of (EcModules.lvalue option * P.xpath * EcTypes.expr list)
  | `Rnd      of (EcModules.lvalue * EcTypes.expr)
  | `Abstract of EcIdent.t
  | `If       of EcTypes.expr
  | `Else
  | `While    of EcTypes.expr
  | `Match    of EcTypes.expr
  | `Branch   of (symbol * (EcIdent.t * ty) list)
  | `None
  | `EBlk
]

type ppnode = ppnode1 * ppnode1 * [`P | `Q | `S | `B] * ppnode list list

type cppnode1 = string list
type cppnode  = cppnode1 * cppnode1 * char * cppnode list list

let at (ppe : PPEnv.t) n i =
  match i, n with
  | Sasgn (lv, e)    , 0 -> Some (`Asgn (lv, e)    , `P, [])
  | Srnd  (lv, e)    , 0 -> Some (`Rnd  (lv, e)    , `P, [])
  | Scall (lv, f, es), 0 -> Some (`Call (lv, f, es), `P, [])
  | Sassert e        , 0 -> Some (`Assert e        , `P, [])
  | Sabstract id     , 0 -> Some (`Abstract id     , `P, [])
  | Swhile (e, s), 0 -> Some (`While e, `P, s.s_node)
  | Swhile _     , 1 -> Some (`EBlk   , `B, [])

  | Sif (e, s, _ ), 0 -> Some (`If e, `P, s.s_node)
  | Sif (_, _, s ), 1 -> begin
      match s.s_node with
      | [] -> Some (`EBlk, `B, [])
      | _  -> Some (`Else, `Q, s.s_node)
    end

  | Sif (_, _, s), 2 -> begin
      match s.s_node with
      | [] -> None
      | _  -> Some (`EBlk, `B, [])
    end

  | Smatch (e, _), 0 -> Some (`Match e, `P, [])

  | Smatch (e, s), i when i <= 2 * (List.length s) ->
      if i mod 2 = 1 then
        let env = ppe.PPEnv.ppe_env in
        let tyd = proj3_2 (oget (EcEnv.Ty.get_top_decl e.e_ty env)) in
        let tyd = oget (EcDecl.tydecl_as_datatype tyd) in
        let tyd = List.combine s tyd.EcDecl.tydt_ctors in
        let br, ctor = List.nth tyd ((i-1)/2) in
        Some (`Branch (fst ctor, fst br), `S, (snd br).s_node)
      else Some (`EBlk, `B, [])

  | _, _ -> None

let rec collect2_i ppe i1 i2 : ppnode list =
  let rec doit n =
    match i1 |> obind (at ppe n), i2 |> obind (at ppe n) with
    | None, None -> []

    | Some (p1, c1, s1), None -> collect1_i ppe `Left  p1 s1 c1 :: doit (n+1)
    | None, Some (p2, c2, s2) -> collect1_i ppe `Right p2 s2 c2 :: doit (n+1)

    | Some (p1, c1, s1), Some (p2, c2, s2) ->
        let sub_p = collect2_s ppe s1 s2 in
        let c =
          match c1, c2 with
          | `B,  c |  c, `B -> c
          | `P, `P | `Q, `Q | `S, `S -> c1
          | `P, `Q | `Q, `P -> `Q
          | `P, `S | `S, `P -> `S
          | `Q, `S | `S, `Q -> `S
        in
          (p1, p2, c, sub_p) :: doit (n+1)
  in
    doit 0

and collect2_s ppe s1 s2 : ppnode list list =
  match s1, s2 with
  | [], [] -> []

  | i1::s1, [] -> collect2_i ppe (Some i1.i_node) None :: collect2_s ppe s1 []
  | [], i2::s2 -> collect2_i ppe None (Some i2.i_node) :: collect2_s ppe [] s2

  | i1::s1, i2::s2 ->
         collect2_i ppe (Some i1.i_node) (Some i2.i_node)
      :: collect2_s ppe s1 s2

and collect1_i ppe side p s c =
  let (p1, p2), (s1, s2) =
    match side with
    | `Left  -> (p, `None), (s, [])
    | `Right -> (`None, p), ([], s)
  in
    (p1, p2, c, collect2_s ppe s1 s2)

(* -------------------------------------------------------------------- *)
let c_split ?width pp x =
  let buf = Buffer.create 127 in
    begin
      let fmt = Format.formatter_of_buffer buf in
        width |> oiter (Format.pp_set_margin fmt);
        Format.fprintf fmt "@[<hov 2>%a@]@." pp x
    end;
    EcRegexp.split0 (`S "(?:\r?\n)+") (Buffer.contents buf)

let pp_i_asgn (ppe : PPEnv.t) fmt (lv, e) =
  Format.fprintf fmt "%a <-@ %a"
    (pp_lvalue ppe) lv (pp_expr ppe) e

let pp_i_assert (ppe : PPEnv.t) fmt e =
  Format.fprintf fmt "assert (%a)" (pp_expr ppe) e

let pp_i_call (ppe : PPEnv.t) fmt (lv, xp, args) =
  match lv with
  | None ->
      Format.fprintf fmt "%a(%a)"
        (pp_funname ppe) xp
        (pp_list ",@ " (pp_expr ppe)) args

  | Some lv ->
      Format.fprintf fmt "@[<hov 2>%a <@@@ %a(%a)@]"
        (pp_lvalue ppe) lv
        (pp_funname ppe) xp
        (pp_list ",@ " (pp_expr ppe)) args

let pp_i_rnd (ppe : PPEnv.t) fmt (lv, e) =
  Format.fprintf fmt "%a <$@ @[<hov 2>%a@]"
    (pp_lvalue ppe) lv (pp_expr ppe) e

let pp_i_if (ppe : PPEnv.t) fmt e =
  Format.fprintf fmt "if (%a) {" (pp_expr ppe) e

let pp_i_else (_ppe : PPEnv.t) fmt _ =
  Format.fprintf fmt "} else {"

let pp_i_while (ppe : PPEnv.t) fmt e =
  Format.fprintf fmt "while (%a) {" (pp_expr ppe) e

let pp_i_match (ppe : PPEnv.t) fmt e =
  Format.fprintf fmt "match (%a) with" (pp_expr ppe) e

let pp_i_branch (ppe : PPEnv.t) fmt (x, args) =
  (* FIXME: add local variables (propagate to branch's body) *)
  Format.fprintf fmt "| %s%a => {" x
    (pp_list "" (fun fmt x -> Format.fprintf fmt " %a" (pp_local ppe) x))
    (List. fst args)

let pp_i_blk (_ppe : PPEnv.t) fmt _ =
  Format.fprintf fmt "}"

let pp_i_abstract (_ppe : PPEnv.t) fmt id =
  Format.fprintf fmt "%s" (EcIdent.name id)

(* -------------------------------------------------------------------- *)
let c_ppnode1 ~width ppe (pp1 : ppnode1) =
  match pp1 with
  | `Asgn     x -> c_split ~width (pp_i_asgn     ppe) x
  | `Assert   x -> c_split ~width (pp_i_assert   ppe) x
  | `Call     x -> c_split ~width (pp_i_call     ppe) x
  | `Rnd      x -> c_split ~width (pp_i_rnd      ppe) x
  | `Abstract x -> c_split ~width (pp_i_abstract ppe) x
  | `If       x -> c_split ~width (pp_i_if       ppe) x
  | `Else       -> c_split ~width (pp_i_else     ppe) ()
  | `While    x -> c_split ~width (pp_i_while    ppe) x
  | `Match    x -> c_split ~width (pp_i_match    ppe) x
  | `Branch   x -> c_split ~width (pp_i_branch   ppe) x
  | `EBlk       -> c_split ~width (pp_i_blk      ppe) ()
  | `None       -> []

let rec c_ppnode ~width ?mem ppe (pps : ppnode list list) =
  let do1 ((p1, p2, c, subs) : ppnode) : cppnode =
    let p1   = c_ppnode1 ~width (mem |> omap fst |> ofold ((^~) PPEnv.enter_by_memid) ppe) p1 in
    let p2   = c_ppnode1 ~width (mem |> omap snd |> ofold ((^~) PPEnv.enter_by_memid) ppe) p2 in
    let subs = c_ppnode  ~width ?mem ppe subs in
    let c    = match c with `B -> ' ' | `P -> '.' | `Q -> '?' | `S -> '#' in
      (p1, p2, c, subs)
  in
    List.map (List.map do1) pps

(* -------------------------------------------------------------------- *)
let rec get_ppnode_stats (pps : cppnode list list) : (int * int) * int list =
  (* Top-level instruction strings (left/right) *)
  let ls = List.map (List.map (fun (l, _, _, _) -> l)) pps
  and rs = List.map (List.map (fun (_, r, _, _) -> r)) pps in

  (* Sub printing commands *)
  let subs = List.map (List.map (fun (_, _, _, pps) -> pps)) pps in
  let subs = List.flatten subs in

  (* Sub stats *)
  let stats = List.split (List.map get_ppnode_stats subs) in

  (* Max line length *)
  let maxl, maxr =
    List.fold_left
      (fun (maxl, maxr) (l1, r1) -> (max maxl l1, max maxr r1))
      (0, 0) (fst stats)
  in

  let maxl, maxr =
    let max1 b lines =
      let for1 m s = max m (String.length s) in
        List.fold_left (List.fold_left (List.fold_left for1)) b lines
    in
      (max1 (2+maxl) ls, max1 (2+maxr) rs)
  in

  (* Maximum length for sub-blocks *)
  let maxsublen =
    match List.length pps, snd stats with
    | 0, []      -> []
    | n, []      -> [n]
    | n, st1::st -> n :: (List.fold_left (List.fusion max) st1 st)

  in
    ((maxl, maxr), maxsublen)

let get_ppnode_stats pps =
  let ndigits n = int_of_float (ceil (log10 (float_of_int (n+1)))) in
  let ((maxl, maxr), mb) = get_ppnode_stats pps in

    ((max maxl 25, max maxr 25), List.map ndigits mb)

(* -------------------------------------------------------------------- *)
let pp_depth mode =
  let rec pp_depth fmt (s, d) =
    match s, d with
    | [], []   -> ()
    | [], _::_ -> assert false

    | s1::s, [] ->
        let sp = match s with [] -> "" | _ -> "-" in
        Format.fprintf fmt "%s%s" (String.make s1 '-') sp;
        Format.fprintf fmt "%a" pp_depth (s, [])

    | s1::s, d1::d -> begin
        let (d1, c1) = ((snd d1) + 1, fst d1) in

        match mode with
        | `Plain -> begin
          let sp = match s with [] -> "" | _ -> "-" in
            match d with
            | [] -> Format.fprintf fmt "%*d%s" s1 d1 sp
            | _  -> Format.fprintf fmt "%*d%c" s1 d1 c1
        end
        | `Blank ->
          let sp = match s with [] -> "" | _ -> " " in
            Format.fprintf fmt "%*s%s" s1 "" sp
      end;
      Format.fprintf fmt "%a" pp_depth (s, d)
  in
    fun stats d fmt -> ignore (pp_depth fmt (stats, List.rev d))

let pp_node_r side ((maxl, maxr), stats) =
  let rec pp_node_r idt depth fmt node =
    let fori offset (node1 : cppnode list) =
      let do1 ((ls, rs, pc, sub) : cppnode) =
        let forline mode l r =
          let l = odfl "" l and r = odfl "" r in
            match side with
            | `Both ->
                Format.fprintf fmt "%-*s  (%t)  %-*s@\n%!"
                  maxl (Printf.sprintf "%*s%s" (2*idt) "" l)
                  (pp_depth mode stats ((pc, offset) :: depth))
                  maxr (Printf.sprintf "%*s%s" (2*idt) "" r)

            | `Left ->
                Format.fprintf fmt "(%t)  %-*s@\n%!"
                  (pp_depth mode stats ((pc, offset) :: depth))
                  maxl (Printf.sprintf "%*s%s" (2*idt) "" l)
        in

        let (l , r ) = (List.ohead ls, List.ohead rs) in
        let (ls, rs) = (List.otail ls, List.otail rs) in

          forline `Plain l r;
          List.iter2o(forline `Blank) (odfl [] ls) (odfl [] rs);
          pp_node_r (idt+1) ((pc, offset) :: depth) fmt sub
      in
        List.iter do1 node1

    in
      List.iteri fori node
  in
    fun idt depth fmt node -> pp_node_r idt depth fmt node

let pp_node mode fmt node =
  let stats = get_ppnode_stats node in
    pp_node_r mode stats 0 [] fmt node

(* -------------------------------------------------------------------- *)
let rec pp_prpo (ppe : PPEnv.t) tag mode fmt f =
  if mode then
    let fs = EcFol.destr_ands ~deep:false f in
    let ns = List.length fs in

    if ns <= 1 then pp_prpo ppe tag false fmt f else

    let ws = max 0. (log10 (float_of_int ((List.length fs - 1)))) in
    let ws = int_of_float (ceil ws) in

    Format.fprintf fmt "%s:\n%!" tag;
    List.iteri (fun i f ->
      Format.fprintf fmt "  [%.*d]: @[<hov 2>%a@]\n%!"
        ws (i + 1) (pp_form ppe) f) fs;
  else
    Format.fprintf fmt "@[<hov 2>%s =@ %a@]\n%!" tag (pp_form ppe) f

(* -------------------------------------------------------------------- *)
let pp_pre (ppe : PPEnv.t) ?prpo fmt pre =
  pp_prpo ppe "pre"
    (omap (fun x -> x.prpo_pr) prpo |> odfl false)
    fmt pre

(* -------------------------------------------------------------------- *)
let pp_post (ppe : PPEnv.t) ?prpo fmt post =
  pp_prpo ppe "post"
    (omap (fun x -> x.prpo_po) prpo |> odfl false)
    fmt post

(* -------------------------------------------------------------------- *)
let pp_hoareF (ppe : PPEnv.t) ?prpo fmt hf =
  let mepr, mepo = EcEnv.Fun.hoareF_memenv hf.hf_f ppe.PPEnv.ppe_env in
  let ppepr = PPEnv.create_and_push_mem ppe ~active:true mepr in
  let ppepo = PPEnv.create_and_push_mem ppe ~active:true mepo in

  Format.fprintf fmt "%a@\n%!" (pp_pre ppepr ?prpo) hf.hf_pr;
  Format.fprintf fmt "    %a@\n%!" (pp_funname ppe) hf.hf_f;
  Format.fprintf fmt "@\n%a%!" (pp_post ppepo ?prpo) hf.hf_po

(* -------------------------------------------------------------------- *)
let pp_hoareS (ppe : PPEnv.t) ?prpo fmt hs =
  let ppef = PPEnv.push_mem ppe ~active:true hs.hs_m in
  let ppnode = collect2_s ppef hs.hs_s.s_node [] in
  let ppnode = c_ppnode ~width:ppe.PPEnv.ppe_width ppef ppnode
  in
    Format.fprintf fmt "Context : %a@\n%!" (pp_memtype ppe) (snd hs.hs_m);
    Format.fprintf fmt "@\n%!";
    Format.fprintf fmt "%a%!" (pp_pre ppef ?prpo) hs.hs_pr;
    Format.fprintf fmt "@\n%!";
    Format.fprintf fmt "%a" (pp_node `Left) ppnode;
    Format.fprintf fmt "@\n%!";
    Format.fprintf fmt "%a%!" (pp_post ppef ?prpo) hs.hs_po

(* -------------------------------------------------------------------- *)
let pp_choareF (ppe : PPEnv.t) ?prpo fmt chf =
  let mepr, mepo = EcEnv.Fun.hoareF_memenv chf.chf_f ppe.PPEnv.ppe_env in
  let ppepr = PPEnv.create_and_push_mem ppe ~active:true mepr in
  let ppepo = PPEnv.create_and_push_mem ppe ~active:true mepo in

  Format.fprintf fmt "%a@\n%!" (pp_pre ppepr ?prpo) chf.chf_pr;
  Format.fprintf fmt "    %a@\n%!" (pp_funname ppe) chf.chf_f;
  Format.fprintf fmt "    time %a@\n%!" (pp_cost ppe) chf.chf_co;
  Format.fprintf fmt "@\n%a%!" (pp_post ppepo ?prpo) chf.chf_po

(* -------------------------------------------------------------------- *)
let pp_choareS (ppe : PPEnv.t) ?prpo fmt chs =
  let ppef = PPEnv.push_mem ppe ~active:true chs.chs_m in
  let ppnode = collect2_s ppef chs.chs_s.s_node [] in
  let ppnode = c_ppnode ~width:ppe.PPEnv.ppe_width ppef ppnode in


  Format.fprintf fmt "Context : %a@\n%!"
     (pp_memtype ppe) (snd chs.chs_m);
  Format.fprintf fmt "Time : %a@\n%!" (pp_cost ppe) chs.chs_co;
  Format.fprintf fmt "@\n%!";
  Format.fprintf fmt "%a%!" (pp_pre ppef ?prpo) chs.chs_pr;
  Format.fprintf fmt "@\n%!";
  Format.fprintf fmt "%a" (pp_node `Left) ppnode;
  Format.fprintf fmt "@\n%!";
  Format.fprintf fmt "%a%!" (pp_post ppef ?prpo) chs.chs_po

(* -------------------------------------------------------------------- *)
let string_of_hrcmp = function
  | FHle -> "[<=]"
  | FHeq -> "[=]"
  | FHge -> "[>=]"

(* -------------------------------------------------------------------- *)
let pp_bdhoareF (ppe : PPEnv.t) ?prpo fmt hf =
  let mepr, mepo = EcEnv.Fun.hoareF_memenv hf.bhf_f ppe.PPEnv.ppe_env in
  let ppepr = PPEnv.create_and_push_mem ppe ~active:true mepr in
  let ppepo = PPEnv.create_and_push_mem ppe ~active:true mepo in

  let scmp = string_of_hrcmp hf.bhf_cmp in

  Format.fprintf fmt "%a@\n%!" (pp_pre ppepr ?prpo) hf.bhf_pr;
  Format.fprintf fmt "    %a@\n%!" (pp_funname ppe) hf.bhf_f;
  Format.fprintf fmt "    %s @[<hov 2>%a@]@\n%!" scmp (pp_form ppepr) hf.bhf_bd;
  Format.fprintf fmt "@\n%a%!" (pp_post ppepo ?prpo) hf.bhf_po

(* -------------------------------------------------------------------- *)
let pp_bdhoareS (ppe : PPEnv.t) ?prpo fmt hs =
  let ppef = PPEnv.push_mem ppe ~active:true hs.bhs_m in
  let ppnode = collect2_s ppef hs.bhs_s.s_node [] in
  let ppnode = c_ppnode ~width:ppe.PPEnv.ppe_width ppef ppnode
  in

  let scmp = string_of_hrcmp hs.bhs_cmp in

    Format.fprintf fmt "Context : %a@\n%!" (pp_memtype ppe) (snd hs.bhs_m);
    Format.fprintf fmt "Bound   : @[<hov 2>%s %a@]@\n%!" scmp (pp_form ppef) hs.bhs_bd;
    Format.fprintf fmt "@\n%!";
    Format.fprintf fmt "%a%!" (pp_pre ppef ?prpo) hs.bhs_pr;
    Format.fprintf fmt "@\n%!";
    Format.fprintf fmt "%a" (pp_node `Left) ppnode;
    Format.fprintf fmt "@\n%!";
    Format.fprintf fmt "%a%!" (pp_post ppef ?prpo) hs.bhs_po

(* -------------------------------------------------------------------- *)
let pp_equivF (ppe : PPEnv.t) ?prpo fmt ef =
  let (meprl, meprr), (mepol,mepor) =
    EcEnv.Fun.equivF_memenv ef.ef_fl ef.ef_fr ppe.PPEnv.ppe_env in
  let ppepr = PPEnv.create_and_push_mems ppe [meprl; meprr] in
  let ppepo = PPEnv.create_and_push_mems ppe [mepol; mepor] in
  Format.fprintf fmt "%a@\n%!" (pp_pre ppepr ?prpo) ef.ef_pr;
  Format.fprintf fmt "    %a ~ %a@\n%!"
    (pp_funname ppe) ef.ef_fl
    (pp_funname ppe) ef.ef_fr;
  Format.fprintf fmt "@\n%a%!" (pp_post ppepo ?prpo) ef.ef_po

(* -------------------------------------------------------------------- *)
let pp_equivS (ppe : PPEnv.t) ?prpo fmt es =
  let ppef = PPEnv.push_mems ppe [es.es_ml; es.es_mr] in
  let ppel = PPEnv.push_mem ppe ~active:true es.es_ml in

  let insync =
       EcMemory.mt_equal (snd es.es_ml) (snd es.es_mr)
    && EcReduction.EqTest.for_stmt
         ppe.PPEnv.ppe_env ~norm:false es.es_sl es.es_sr in

  let ppnode =
    if insync then begin
      let ppe    = ppel in
      let ppnode = collect2_s ppe es.es_sl.s_node [] in
      let ppnode = c_ppnode ~width:ppe.PPEnv.ppe_width ppe ppnode in
      fun fmt -> pp_node `Left fmt ppnode
    end else begin
      let ppnode = collect2_s ppe es.es_sl.s_node es.es_sr.s_node in
      let ppnode =
        c_ppnode
          ~width:(ppe.PPEnv.ppe_width / 2)
          ~mem:(fst es.es_ml, fst es.es_mr)
          ppef ppnode
      in fun fmt -> pp_node `Both fmt ppnode
    end in

  Format.fprintf fmt "&1 (left ) : %a%s@\n%!"
    (pp_memtype ppe) (snd es.es_ml)
    (if insync then " [programs are in sync]" else "");
  Format.fprintf fmt "&2 (right) : %a@\n%!"
    (pp_memtype ppe) (snd es.es_mr);
  Format.fprintf fmt "@\n%!";
  Format.fprintf fmt "%a%!" (pp_pre ppef ?prpo) es.es_pr;
  Format.fprintf fmt "@\n%!";
  Format.fprintf fmt "%t" ppnode;
  Format.fprintf fmt "@\n%!";
  Format.fprintf fmt "%a%!" (pp_post ppef ?prpo) es.es_po

(* -------------------------------------------------------------------- *)
let pp_rwbase ppe fmt (p, rws) =
  Format.fprintf fmt "%a = %a@\n%!"
    (pp_rwname ppe) p (pp_list ", " (pp_axname ppe)) (Sp.elements rws)

(* -------------------------------------------------------------------- *)
let pp_solvedb ppe fmt db =
  List.iter (fun (lvl, ps) ->
    Format.fprintf fmt "[%3d] %a\n%!"
      lvl (pp_list ", " (pp_axname ppe)) ps)
  db;

  let lemmas = List.flatten (List.map snd db) in
  let lemmas = List.pmap (fun p ->
      let ax = EcEnv.Ax.by_path_opt p ppe.PPEnv.ppe_env in
      (omap (fun ax -> (p, ax)) ax))
    lemmas
  in

  if not (List.is_empty lemmas) then begin
    Format.fprintf fmt "\n%!";
    List.iter
      (fun ax -> Format.fprintf fmt "%a\n\n%!" (pp_axiom ppe) ax)
      lemmas
  end

(* -------------------------------------------------------------------- *)
type ppgoal = (EcBaseLogic.hyps * EcFol.form) * [
  | `One of int
  | `All of (EcBaseLogic.hyps * EcFol.form) list
]

module PPGoal = struct
  let goalline i = String.make i '-'

  let pre_pp_hyp ppe (id, k) =
    let ppe =
      match k with
      | EcBaseLogic.LD_mem m ->
          let ppe = PPEnv.add_local ~force:true ppe id in
          PPEnv.create_and_push_mem ppe (id, m)

      | EcBaseLogic.LD_modty p ->
          PPEnv.add_mods ~force:true ppe [id] p

      | EcBaseLogic.LD_var _ when EcIdent.name id = "_" ->
          PPEnv.add_local
            ~gen:(fun d -> Printf.sprintf "_~%d" (d+1))
            ~force:false ppe id

      | _ -> PPEnv.add_local ~force:true ppe id

    and pdk =
        match k with
        | EcBaseLogic.LD_var (ty, None) ->
            (None, fun fmt -> pp_type ppe fmt ty)

        | EcBaseLogic.LD_var (ty, Some body) -> begin
            let ty, bds, body =
              match split_fun body with
              | ([], _) -> (ty, [], body)
              | (bds, body) -> (body.f_ty, bds, body)
            in

            let (subppe, pp) = pp_bindings ppe ~break:false ~fv:body.f_fv bds in

            let dk fmt =
              Format.fprintf fmt "%a@ := %a"
                (pp_type ppe) ty (pp_form subppe) body
            in ((if List.is_empty bds then None else Some pp), dk)
          end

        | EcBaseLogic.LD_mem m ->
            (None, fun fmt -> pp_memtype ppe fmt m)

        | EcBaseLogic.LD_modty p ->
          let (ppe, pp) = pp_mod_params ppe p.mt_params in
          (Some pp, fun fmt -> pp_modtype ppe fmt p)

        | EcBaseLogic.LD_hyp f ->
            (None, fun fmt -> pp_form ppe fmt f)

        | EcBaseLogic.LD_abs_st _ ->
            (None, fun fmt -> Format.fprintf fmt "statement") (* FIXME *)

    in (ppe, (id, pdk))

  let pp_goal1 ?(pphyps = true) ?prpo ?(idx) (ppe : PPEnv.t) fmt (hyps, concl) =
    let ppe = PPEnv.add_locals ppe (List.map fst hyps.EcBaseLogic.h_tvar) in
    let ppe, pps = List.map_fold pre_pp_hyp ppe (List.rev hyps.EcBaseLogic.h_local) in

    idx |> oiter (Format.fprintf fmt "Goal #%d@\n");

    if pphyps then begin
      begin
        match hyps.EcBaseLogic.h_tvar with
        | [] -> Format.fprintf fmt "Type variables: <none>@\n\n%!"
        | tv ->
            Format.fprintf fmt "Type variables: %a@\n\n%!"
              (pp_list ", " (pp_tyvar_ctt ppe)) tv
      end;
      List.iter (fun (id, (pk, dk)) ->
        let pk fmt =
          match pk with
          | None    -> ()
          | Some pk -> Format.fprintf fmt "%t " pk in

        Format.fprintf fmt
          "%s%t: @[<hov 2>%t@]@\n%!"
          (PPEnv.local_symb ppe id) pk dk)
        pps
    end;

    let glsz = (Format.pp_get_margin fmt ()) - 6 in
    let glsz = max glsz 2 in

    Format.fprintf fmt "%s@\n%!" (goalline glsz);

    match concl.f_node with
    | FbdHoareF hf -> pp_bdhoareF ppe fmt hf
    | FbdHoareS hs -> pp_bdhoareS ?prpo ppe fmt hs
    | FcHoareF hf  -> pp_choareF   ppe fmt hf
    | FcHoareS hs  -> pp_choareS  ?prpo ppe fmt hs
    | FhoareF hf   -> pp_hoareF   ppe fmt hf
    | FhoareS hs   -> pp_hoareS   ?prpo ppe fmt hs
    | FequivF ef   -> pp_equivF   ppe fmt ef
    | FequivS es   -> pp_equivS   ?prpo ppe fmt es
    | _ -> Format.fprintf fmt "%a@\n%!" (pp_form ppe) concl
end

(* -------------------------------------------------------------------- *)
let pp_hyps (ppe : PPEnv.t) fmt hyps =
  let hyps = EcEnv.LDecl.tohyps hyps in
  let ppe = PPEnv.add_locals ppe (List.map fst hyps.EcBaseLogic.h_tvar) in
  let ppe, pps =
    List.map_fold PPGoal.pre_pp_hyp ppe
                  (List.rev hyps.EcBaseLogic.h_local) in

  begin match hyps.EcBaseLogic.h_tvar with
  | [] -> Format.fprintf fmt "Type variables: <none>@\n\n%!"
  | tv ->
      Format.fprintf fmt "Type variables: %a@\n\n%!"
        (pp_list ", " (pp_tyvar_ctt ppe)) tv
  end;
  List.iter (fun (id, (pk, dk)) ->
    let pk fmt =
      match pk with
      | None    -> ()
      | Some pk -> Format.fprintf fmt "%t" pk in

    Format.fprintf fmt
      "%s%t: @[<hov 2>%t@]@\n%!"
      (PPEnv.local_symb ppe id) pk dk)
    pps

(* -------------------------------------------------------------------- *)
let pp_goal (ppe : PPEnv.t) (prpo : prpo_display) fmt (g, extra) =
  let n =
    match extra with
    | `One n  -> n
    | `All gs -> 1 + List.length gs
  in

  begin
    match n with
    | _ when n < 0 -> ()
    | 1 -> Format.fprintf fmt "Current goal@\n@\n%!"
    | _ -> Format.fprintf fmt "Current goal (remaining: %d)@\n@\n%!" n
  end;

  Format.fprintf fmt "%a@?" (PPGoal.pp_goal1 ~prpo ppe) g;

  match extra with
  | `One _  -> ()
  | `All gs ->
      Format.fprintf fmt "@\n";
      List.iteri (fun i g ->
        Format.fprintf fmt "@\n@[<hov 2>@\n%a@]@?"
          (PPGoal.pp_goal1 ~pphyps:false ~prpo ~idx:(i+2) ppe) g)
        gs

(* -------------------------------------------------------------------- *)
let pp_ovdecl ppe fmt ov =
  Format.fprintf fmt "%s : %a" (odfl "_" ov.ov_name) (pp_type ppe) ov.ov_type

let pp_pvdecl ppe fmt v =
  Format.fprintf fmt "%s : %a" v.v_name (pp_type ppe) v.v_type

let pp_funsig ppe fmt fs =
  Format.fprintf fmt "@[<hov 2>proc %s(%a) :@ %a@]"
    fs.fs_name
    (pp_list ", " (pp_ovdecl ppe)) fs.fs_anames
    (pp_type ppe) fs.fs_ret

let pp_sigitem moi_opt ppe fmt (Tys_function fs) =
  Format.fprintf fmt "@[<hov 2>%a@ %t@]"
    (pp_funsig ppe) fs
    (fun fmt -> match moi_opt with
       | None ->
         Format.fprintf fmt ""
       | Some moi ->
         let oi = Msym.find fs.fs_name moi in
         pp_orclinfo_bare ppe fmt oi)

let pp_modsig ?(long=false) ppe fmt (p,ms) =
  let (ppe,pp) = pp_mod_params ppe ms.mis_params in

  let pp_long fmt p =
    if long then
      let qs = EcPath.toqsymbol p in
      if fst qs <> [] then
        Format.fprintf fmt "(* %a *)@ " EcSymbols.pp_qsymbol qs in

  Format.fprintf fmt "@[<v>@[<hv 2>%amodule type %s%t @,%a@;<0 -2>@] = \
                      {@,  @[<v>%a@]@,}@]"
    pp_long p
    (EcPath.basename p) pp
    (pp_mem_restr ppe) ms.mis_restr
    (pp_list "@,@," (pp_sigitem (Some ms.mis_restr.mr_oinfos) ppe)) ms.mis_body

(* Printing of a module signature with no restrictions. *)
let pp_modsig_smpl ppe fmt (p,ms) =
  let (ppe,pp) = pp_mod_params ppe ms.miss_params in
  Format.fprintf fmt "@[<v>module type %s%t = {@,  @[<v>%a@]@,}@]"
    (EcPath.basename p) pp
    (pp_list "@,@," (pp_sigitem None ppe)) ms.miss_body

let pp_top_modsig ppe fmt (p,ms) =
  Format.fprintf fmt "%a%a" pp_locality ms.tms_loca (pp_modsig ppe) (p,ms.tms_sig)

let rec pp_instr_r (ppe : PPEnv.t) fmt i =
  match i.i_node with
  | Sasgn (lv, e) -> begin
      match lv, EcTypes.split_args e with
      | LvVar (x, _), ({ e_node = Eop (op, _) }, [ { e_node = Evar y }; k; v])
          when (EcPath.basename op = EcCoreLib.s_set) && (EcTypes.pv_equal x y) ->

        Format.fprintf fmt "@[<hov 2>%a.[%a] <-@ @[%a@]@];"
          (pp_pv ppe) x (pp_tuple_expr ppe) k (pp_expr ppe) v

      | _, _ ->
        Format.fprintf fmt "@[<hov 2>%a <-@ @[%a@]@];"
          (pp_lvalue ppe) lv (pp_expr ppe) e
    end

  | Srnd (lv, e) ->
    Format.fprintf fmt "@[<hov 2>%a <$@ @[%a@]@];"
      (pp_lvalue ppe) lv (pp_expr ppe) e

  | Scall (None, xp, args) ->
    Format.fprintf fmt "%a(@[%a@]);"
      (pp_funname ppe) xp
      (pp_list ",@ " (pp_expr ppe)) args

  | Scall (Some lv, xp, args) ->
    Format.fprintf fmt "@[<hov 2>%a <@@@ %a(@[%a@])@];"
      (pp_lvalue ppe) lv
      (pp_funname ppe) xp
      (pp_list ",@ " (pp_expr ppe)) args

  | Sassert e ->
    Format.fprintf fmt "@[<hov 2>assert %a@];"
      (pp_expr ppe) e

  | Swhile (e, s) ->
    Format.fprintf fmt "@[<v>while (@[%a@])%a@]"
      (pp_expr ppe) e (pp_block ppe) s

  | Sif (e, s1, s2) ->
    let pp_else ppe fmt s =
      match s.s_node with
      | []  -> ()
      | [_] -> Format.fprintf fmt "@,else %a" (pp_block ppe) s
      | _   -> Format.fprintf fmt "@ else %a" (pp_block ppe) s
    in
      Format.fprintf fmt "@[<v>if (@[%a@]) %a%a@]"
      (pp_expr ppe) e (pp_block ppe) s1 (pp_else ppe) s2

  | Smatch (e, ps) ->
    let p, tyd, typ = oget (EcEnv.Ty.get_top_decl e.e_ty ppe.PPEnv.ppe_env) in
    let tyd = oget (EcDecl.tydecl_as_datatype tyd) in
    let ps  = List.combine ps tyd.EcDecl.tydt_ctors in

    let pp_branch fmt ((vars, s), (cname, _)) =
      let ptn = EcTypes.toarrow (List.snd vars) e.e_ty in
      let ptn = f_op (EcPath.pqoname (EcPath.prefix p) cname) typ ptn in
      let ptn = f_app ptn (List.map (fun (x, ty) -> f_local x ty) vars) e.e_ty in

      Format.fprintf fmt "| %a => @[<hov 2>%a@]@ "
        (pp_form ppe) ptn (pp_block ppe) s
    in

    Format.fprintf fmt "@[<v>match (@[%a@]) with@ %aend@]"
      (pp_expr ppe) e (pp_list "" pp_branch) ps

  | Sabstract id ->
    Format.fprintf fmt "%s" (EcIdent.name id)

and pp_instr ppe fmt i =
  Format.fprintf fmt "%a" (pp_instr_r ppe) i

and pp_block ppe fmt s =
  match s.s_node with
  | []  -> Format.fprintf fmt "{}"
  | [i] -> Format.fprintf fmt "@;<1 2>%a" (pp_instr ppe) i
  | _   -> Format.fprintf fmt "{@,  @[<v>%a@]@,}" (pp_stmt ppe) s

and pp_stmt ppe fmt s =
  pp_list "@," (pp_instr ppe) fmt s.s_node

let rec pp_modexp ppe fmt (p, me) =
  let params =
    match me.me_body with
    | ME_Alias (i,_) -> List.take i me.me_params
    | _              -> me.me_params in
  let (ppe, pp) = pp_mod_params ppe params in
  Format.fprintf fmt "@[<v>module %s%t = %a@]"
    me.me_name pp
    (pp_modbody ppe) (p, me.me_body)

and pp_modbody ppe fmt (p, body) =
  match body with
  | ME_Alias (_, mp) ->
    Format.fprintf fmt "%a" (pp_topmod ppe) mp

  | ME_Structure ms ->
      Format.fprintf fmt "{@,  @[<v>%a@]@,}"
        (pp_list "@,@," (fun fmt i -> pp_moditem ppe fmt (p, i))) ms.ms_body

  | ME_Decl mt ->
      Format.fprintf fmt "[Abstract :@;<1 2> %a@,]" (pp_modtype ppe) mt

and pp_moditem ppe fmt (p, i) =
  match i with
  | MI_Module me ->
      pp_modexp ppe fmt (EcPath.mqname p me.me_name, me)

  | MI_Variable v ->
      Format.fprintf fmt "@[<hov 2>var %a@]" (pp_pvdecl ppe) v

  | MI_Function f ->
    let pp_item ppe fmt = function
      | `Var pv ->
          Format.fprintf fmt "@[<hov 2>var %a;@]" (pp_pvdecl ppe) pv
      | `Instr i ->
          Format.fprintf fmt "%a" (pp_instr ppe) i
      | `Return e ->
          Format.fprintf fmt "@[<hov 2>return@ @[%a@];@]" (pp_expr ppe) e
    in

    let pp_fundef ppe fmt fun_ =
      match fun_.f_def with
      | (FBdef def) ->
        let _, me = EcEnv.Fun.actmem_body mhr fun_ in
        let ppe  = PPEnv.push_mem ppe ~active:true me in
        let vars = List.map (fun x -> `Var    x) def.f_locals in
        let stmt = List.map (fun x -> `Instr  x) def.f_body.s_node in
        let ret  = List.map (fun x -> `Return x) (otolist def.f_ret) in
        let all  = List.filter (fun x -> not (List.is_empty x)) [vars; stmt; ret] in

        if List.is_empty all then Format.fprintf fmt "{}" else
          Format.fprintf fmt "{@,  @[<v>%a@]@,}"
            (pp_list "@,@," (pp_list "@," (pp_item ppe))) all;

      | FBalias g ->
          Format.fprintf fmt "%a" (pp_funname ppe) g

      | FBabs _ ->
          Format.fprintf fmt "?ABSTRACT?"
    in

    Format.fprintf fmt "@[<v>%a = %a@]"
      (pp_funsig ppe) f.f_sig
      (pp_fundef ppe) f

let pp_modexp ppe fmt (mp, me) =
  Format.fprintf fmt "%a." (pp_modexp ppe) (mp, me)

let pp_modexp_lc ppe fmt (mp, (me, olc)) =
  let lc = odfl `Global olc in
 Format.fprintf fmt "%a%a" pp_locality lc (pp_modexp ppe) (mp, me)

let pp_top_modexp ppe fmt (p, me) =
  let mp = EcPath.mpath_crt p [] (Some (EcPath.psymbol me.tme_expr.me_name)) in
  pp_modexp_lc ppe fmt (mp, (me.tme_expr, Some me.tme_loca))

let rec pp_theory ppe (fmt : Format.formatter) (path, cth) =
  let basename = EcPath.basename path in
  let pp_clone fmt thsrc =
    thsrc |> oiter (fun EcTheory.{ ths_base } ->
      Format.fprintf fmt "(* clone %a as %s *)@,"
        (pp_thname ppe) ths_base basename) in

  let thkw =
    match cth.EcTheory.cth_mode with
    | `Abstract -> "abstract theory"
    | `Concrete -> "theory"
  in

  Format.fprintf fmt "@[<v>%a%s %s.@,  @[<v>%a@]@,end %s.@]"
    pp_clone cth.EcTheory.cth_source
    thkw basename
    (pp_list "@,@," (pp_th_item ppe path)) cth.cth_items
    basename

 and pp_th_item ppe p fmt item =
  match item.ti_item with
  | EcTheory.Th_type (id, ty) ->
      pp_typedecl ppe fmt (EcPath.pqname p id,ty)

  | EcTheory.Th_operator (id, op) ->
      pp_opdecl ppe fmt (EcPath.pqname p id, op)

  | EcTheory.Th_axiom (id, ax) ->
      pp_axiom ppe fmt (EcPath.pqname p id, ax)

  | EcTheory.Th_schema (id, schema) ->
      pp_schema ppe fmt (EcPath.pqname p id, schema)

  | EcTheory.Th_modtype (id, ms) ->
      pp_top_modsig ppe fmt (EcPath.pqname p id, ms)

  | EcTheory.Th_module me ->
      pp_top_modexp ppe fmt (p, me)

  | EcTheory.Th_theory (id, cth) ->
      pp_theory ppe fmt (EcPath.pqname p id, cth)

  | EcTheory.Th_export (p, _) ->
      (* Fixme should not use a pp_list, it should be a fold *)
      Format.fprintf fmt "export %a."
        EcSymbols.pp_qsymbol (PPEnv.th_symb ppe p)

  | EcTheory.Th_typeclass _ ->
      Format.fprintf fmt "typeclass <FIXME>."

  | EcTheory.Th_instance ((typ, ty), tc, lc) -> begin
      let ppe = PPEnv.add_locals ppe (List.map fst typ) in (* FIXME *)

      match tc with
      | (`Ring _ | `Field _) as tc -> begin
          let (name, ops) =
            let rec ops_of_ring cr =
              let embedp =
                match cr.r_embed with
                | `Direct | `Default -> None
                | `Embed p -> Some p
              in
                [("rzero", Some cr.r_zero);
                 ("rone" , Some cr.r_one );
                 ("add"  , Some cr.r_add );
                 ("opp"  ,      cr.r_opp );
                 ("mul"  , Some cr.r_mul );
                 ("expr" ,      cr.r_exp );
                 ("sub"  ,      cr.r_sub );
                 ("ofint",      embedp   )]
            and ops_of_field cr =
              ops_of_ring cr.f_ring @
                [("inv", Some cr.f_inv);
                 ("div",      cr.f_div)]
            in
              match tc with
              | `Ring  cr when cr.r_kind = `Boolean ->
                  ("boolean_ring", ops_of_ring cr)
                (* FIXME: modulus rings *)
              | `Ring  cr -> ("ring", ops_of_ring cr)
              | `Field cr -> ("field", ops_of_field cr)
          in

          let ops = List.pmap
            (function (_, None) -> None | (x, Some y) -> Some (x, y))
            ops
          in
            Format.fprintf fmt
              "%ainstance %s with [%a] %a@\n@[<hov 2>  %a@]"
              pp_locality lc
              name
              (pp_paren (pp_list ",@ " (pp_tyvar ppe))) (List.map fst typ)
              (pp_type ppe) ty
              (pp_list "@\n"
                 (fun fmt (name, op) ->
                   Format.fprintf fmt "op %s = %s"
                     name (EcPath.tostring op)))
              ops
      end

      | `General p ->
          Format.fprintf fmt "%ainstance %a with %a."
            pp_locality lc (pp_type ppe) ty pp_path p
  end

  | EcTheory.Th_baserw (name, _lc) ->
      (* FIXME: section lc + syntax *)
      Format.fprintf fmt "declare rewrite %s." name

  | EcTheory.Th_addrw (p, l, lc) ->
      Format.fprintf fmt "%ahint rewrite %a : @[<hov 2>%a@]."
        pp_locality lc
        (pp_rwname ppe) p (pp_list "@ " (pp_axname ppe)) l

  | EcTheory.Th_reduction _ ->
      (* FIXME: section we should add the lemma in the reduction *)
      Format.fprintf fmt "hint simplify."

  | EcTheory.Th_auto (lvl, base, p, lc) ->
      Format.fprintf fmt "%ahint solve %d %s : %a."
        pp_locality lc
        lvl (odfl "" base)
        (pp_list "@ " (pp_axname ppe)) p

(* -------------------------------------------------------------------- *)
let pp_stmt_with_nums (ppe : PPEnv.t) fmt stmt =
  let ppnode = collect2_s ppe stmt.s_node [] in
  let ppnode = c_ppnode ~width:ppe.PPEnv.ppe_width ppe ppnode in
  Format.fprintf fmt "%a" (pp_node `Left) ppnode

(* -------------------------------------------------------------------- *)
let pp_stmt ?(lineno = false) =
  if lineno then pp_stmt_with_nums else pp_stmt

(* -------------------------------------------------------------------- *)
module ObjectInfo = struct
  exception NoObject

  type db = [`Rewrite of qsymbol | `Solve of symbol]

  (* ------------------------------------------------------------------ *)
  type 'a objdump = {
    od_name    : string;
    od_lookup  : qsymbol -> EcEnv.env -> 'a;
    od_printer : PPEnv.t -> Format.formatter -> 'a -> unit;
  }

  (* -------------------------------------------------------------------- *)
  let pr_gen_r ?(prcat = false) dumper = fun fmt env qs ->
    let ppe = PPEnv.ofenv env in
    let obj =
      try dumper.od_lookup qs env
      with EcEnv.LookupFailure _ -> raise NoObject in
    if prcat then
      Format.fprintf fmt "* In [%s]:@\n@." dumper.od_name;
    Format.fprintf fmt "%a@\n@." (dumper.od_printer ppe) obj

  (* -------------------------------------------------------------------- *)
  let pr_gen dumper =
    let theprinter = pr_gen_r dumper in

    fun fmt env qs ->
      try
        theprinter fmt env qs
      with NoObject ->
        Format.fprintf fmt
          "no such object in the category [%s]@." dumper.od_name

  (* ------------------------------------------------------------------ *)
  let pr_ty_r =
    { od_name    = "type declarations";
      od_lookup  = EcEnv.Ty.lookup;
      od_printer = pp_typedecl; }

  let pr_ty = pr_gen pr_ty_r

  (* ------------------------------------------------------------------ *)
  let pr_op_r =
    let get_ops qs env =
      let l = EcEnv.Op.all ~name:qs env in
      if l = [] then raise NoObject;
      l in
    { od_name    = "operators or predicates";
      od_lookup  = get_ops;
      od_printer =
        fun ppe fmt l ->
          Format.fprintf fmt "@[<v>%a@]"
            (pp_list "@ " (pp_opdecl ~long:true ppe)) l; }

  let pr_op = pr_gen pr_op_r

  (* ------------------------------------------------------------------ *)
  let pr_th_r =
    { od_name    = "theories";
      od_lookup  = EcEnv.Theory.lookup ~mode:`All;
      od_printer = pp_theory; }

  let pr_th = pr_gen pr_th_r

  (* ------------------------------------------------------------------ *)
  let pr_ax_r =
    let get_ops qs env =
      let l = EcEnv.Ax.all ~name:qs env in
      if l = [] then raise NoObject;
      l in
    { od_name    = "lemmas or axioms";
      od_lookup  = get_ops;
      od_printer =
        fun ppe fmt l ->
          Format.fprintf fmt "@[<v>%a@]"
            (pp_list "@ " (pp_axiom ~long:true ppe)) l; }

  let pr_ax = pr_gen pr_ax_r

  (* ------------------------------------------------------------------ *)
  let pr_sc_r =
    let get_scs qs env =
      let l = EcEnv.Schema.all ~name:qs env in
      if l = [] then raise NoObject;
      l in
    { od_name    = "schemas";
      od_lookup  = get_scs;
      od_printer =
        fun ppe fmt l ->
          Format.fprintf fmt "@[<v>%a@]"
            (pp_list "@ " (pp_schema ~long:true ppe)) l; }

  let pr_sc = pr_gen pr_sc_r

  (* ------------------------------------------------------------------ *)
  let pr_mod_r =
    { od_name    = "modules";
      od_lookup  = EcEnv.Mod.lookup;
      od_printer = pp_modexp_lc; }

  let pr_mod = pr_gen pr_mod_r

  (* ------------------------------------------------------------------ *)
  let pr_mty_r =
    { od_name    = "module types";
      od_lookup  = EcEnv.ModTy.lookup;
      od_printer = pp_top_modsig; }

  let pr_mty = pr_gen pr_mty_r

  (* ------------------------------------------------------------------ *)
  let pr_rw_r =
    { od_name    = "rewrite database";
      od_lookup  = EcEnv.BaseRw.lookup;
      od_printer = pp_rwbase; }

  let pr_rw = pr_gen pr_rw_r

  (* ------------------------------------------------------------------ *)
  let pr_at_r =
    let lookup q env =
      match q with
      | ([], q) -> begin
          match EcEnv.Auto.getx q env with
          | [] -> raise NoObject | reds -> reds
        end
      | _ -> raise NoObject in

    { od_name    = "solve database";
      od_lookup  = lookup;
      od_printer = pp_solvedb; }

  let pr_at fmt env x = pr_gen pr_at_r fmt env ([], x)

  (* ------------------------------------------------------------------ *)
  let pr_db fmt env db =
    match db with
    | `Rewrite name -> pr_rw fmt env name
    | `Solve   name -> pr_at fmt env name

  (* ------------------------------------------------------------------ *)
  let pr_any fmt env qs =
    let printers = [pr_gen_r ~prcat:true pr_ty_r ;
                    pr_gen_r ~prcat:true pr_op_r ;
                    pr_gen_r ~prcat:true pr_th_r ;
                    pr_gen_r ~prcat:true pr_ax_r ;
                    pr_gen_r ~prcat:true pr_sc_r ;
                    pr_gen_r ~prcat:true pr_mod_r;
                    pr_gen_r ~prcat:true pr_mty_r;
                    pr_gen_r ~prcat:true pr_rw_r ;
                    pr_gen_r ~prcat:true pr_at_r ; ] in

    let ok = ref (List.length printers) in

    List.iter
      (fun f -> try f fmt env qs with NoObject -> decr ok)
      printers;
    if !ok = 0 then
      Format.fprintf fmt "%s@." "no such object in any category"
end

(* ------------------------------------------------------------------ *)
type ppsign = SNone | SPlus | SMinus

let pp_sign fmt = function
  | SNone  -> ()
  | SPlus  -> pp_restr_s fmt true
  | SMinus -> pp_restr_s fmt false

let pp_v ~sign ppe fmt xp =
  Format.fprintf fmt "%a%a"
    pp_sign sign
    (pp_pv ppe) (pv_glob xp)

let pp_m ~sign ppe fmt m =
  Format.fprintf fmt "%a%a"
    pp_sign sign
    (pp_topmod ppe) m

let pp_m_xt ~print_abstract ~sign env fmt m =
  let ppe = PPEnv.ofenv env in
  if print_abstract then
    let r = EcEnv.NormMp.get_restr env m in
    Format.fprintf fmt "@[<hv>%a{@;<0 2>%a@,}@]"
      (pp_m ~sign ppe) m
      (pp_restr ppe) r
  else pp_m ~sign ppe fmt m

let sm_of_mid mid =
  EcIdent.Mid.fold (fun x _ sm ->
      EcPath.Sm.add (EcPath.mident x) sm
    ) mid EcPath.Sm.empty

let pp_use ppe fmt us =
  let open EcEnv in
  let sm = sm_of_mid us.us_gl in

  Format.fprintf fmt "@[<v 0>Abstract modules [# = %d]:@ @[<h>%a@]@;"
    (Sid.cardinal us.us_gl)
    (pp_list "@ " (pp_m ~sign:SNone ppe))
    (EcPath.Sm.ntr_elements sm);
  Format.fprintf fmt "Variables [# = %d]:@ @[<h>%a@]@;@]"
    (EcPath.Mx.cardinal us.us_pv)
    (pp_list "@ " (pp_v ~sign:SNone ppe))
    (EcPath.Sx.ntr_elements (EcPath.Mx.map (fun _ -> ()) us.us_pv))

let pp_use_restr env ~print_abstract fmt ur =
  let open EcEnv in
  let ppe = PPEnv.ofenv env in

  let sm_p = omap (fun x -> sm_of_mid x.us_gl) ur.EcModules.ur_pos
  and sm_n = sm_of_mid ur.EcModules.ur_neg.us_gl in

  let sx_p =
    omap (fun x -> EcPath.Mx.map (fun _ -> ())x.us_pv) ur.EcModules.ur_pos
  and sx_n =
    EcPath.Mx.map (fun _ -> ()) ur.EcModules.ur_neg.us_pv in

  Format.fprintf fmt "@[<v 0>Abstract modules:@ @[<h>%a@]@ @[<h>%a@]@;"
    (fun fmt opt -> match opt with
       | None      ->
         Format.fprintf fmt "%s" all_mem_sym
      | Some sm_p ->
        pp_list "@ " (pp_m_xt ~print_abstract ~sign:SPlus env) fmt sm_p)
    (omap EcPath.Sm.ntr_elements sm_p)
    (pp_list "@ " (pp_m_xt ~print_abstract ~sign:SMinus env))
    (EcPath.Sm.ntr_elements sm_n);

  Format.fprintf fmt "Variables:@ @[<h>%a@]@ @[<h>%a@]@;@]"
    (fun fmt opt -> match opt with
      | None      -> Format.fprintf fmt "%s" all_mem_sym
      | Some sm_p -> pp_list "@ " (pp_v ~sign:SPlus ppe) fmt sm_p)
    (omap EcPath.Sx.ntr_elements sx_p)
    (pp_list "@ " (pp_v ~sign:SMinus ppe))
    (EcPath.Sx.ntr_elements sx_n)

let () =
  EcEnv.pp_debug_form :=
    (fun env fmt f ->
       let ppe = PPEnv.ofenv env in
       pp_form ppe fmt f)
