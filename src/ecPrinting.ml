(* -------------------------------------------------------------------- *)
open EcUtils
open EcFormat
open EcTypes
open EcTypesmod
open EcDecl
open EcParsetree
open EcEnv

module NameGen = EcUidgen.NameGen

module IM  = EcIdent.Map
module Mid = EcIdent.Mid

(* -------------------------------------------------------------------- *)
let (~$) = format_of_string

(* -------------------------------------------------------------------- *)
let pp_located loc pp_elt fmt x =
  Format.fprintf fmt "%s: %a" (Location.tostring loc) pp_elt x

(* -------------------------------------------------------------------- *)
let rec pp_qsymbol fmt = function
  | ([]    , x) -> Format.fprintf fmt "%s" x
  | (n :: p, x) -> Format.fprintf fmt "%s.%a" n pp_qsymbol (p, x)

(* -------------------------------------------------------------------- *)
let rec pp_path fmt = function
  | EcPath.Pident x      -> Format.fprintf fmt "%s" (EcIdent.name x)
  | EcPath.Pqname (p, x) -> Format.fprintf fmt "%a.%s" pp_path p (EcIdent.name x)

(* -------------------------------------------------------------------- *)
let pp_ident fmt id = 
  Format.fprintf fmt "%s" (EcIdent.name id)

(* -------------------------------------------------------------------- *)
let pp_path_in_env _env fmt id =       (* FIXME *)
  Format.fprintf fmt "%s" (EcIdent.name id)

(* -------------------------------------------------------------------- *)
let pp_type (uidmap : NameGen.t) =
  let rec pp_type btuple fmt = function
    | Ttuple tys ->
        let pp = if btuple then pp_paren else pp_id in
          pp (pp_list ~sep:(~$"*") (pp_type true))
            fmt tys

    | Tconstr (name, tyargs) -> begin
        match tyargs with
        | []     -> Format.fprintf fmt "%a" pp_path name
        | [t]    -> Format.fprintf fmt "%a %a" (pp_type true) t pp_path name
        | tyargs -> Format.fprintf fmt "(%a) %a"
                      (pp_list ~sep:(~$", ") (pp_type false)) tyargs
                      pp_path name
    end

    | Tvar id -> (* FIXME *)
        Format.fprintf fmt "%s" (EcIdent.name id)

    | Tunivar id ->
        Format.fprintf fmt "#%s" (NameGen.get uidmap id)

  in
    pp_type

(* -------------------------------------------------------------------- *)
let pp_type ?(vmap : _ option) =
  let uidmap =
    match vmap with
    | None        -> NameGen.create ()
    | Some uidmap -> uidmap
  in
    pp_type uidmap false

(* -------------------------------------------------------------------- *)
let pp_tydecl _env fmt (p, td) =
  let vmap = EcUidgen.NameGen.create () in

  let pp_params fmt = function
    | []   -> ()
    | [id] -> pp_ident fmt id
    | lid  -> Format.fprintf fmt "(%a)" (pp_list ~sep:(", ") pp_ident) lid  in

  let pp_body fmt ty =
    pp_option ~pre:" = " (pp_type ~vmap) fmt ty in

  Format.fprintf fmt "type %a%a%a."
    pp_params td.tyd_params pp_ident (EcPath.basename p) pp_body td.tyd_type

(* -------------------------------------------------------------------- *)
let pp_optyparams fmt lid = 
  match lid with
  | [] -> ()
  | _  -> Format.fprintf fmt "[%a]" (pp_list ~sep:(", ") pp_ident) lid

(* -------------------------------------------------------------------- *)
let pp_dom fmt =
  let vmap = NameGen.create () in
    function
    | []  -> Format.fprintf fmt "()"
    | [t] -> pp_type fmt t
    | lt  -> Format.fprintf fmt "(%a)" (pp_list ~sep:(", ") (pp_type ~vmap)) lt

(* -------------------------------------------------------------------- *)
let pp_opdecl fmt (p, d) =
  let _vmap = EcUidgen.NameGen.create () in

  let str_kind op =
    if is_pred op then "pred" else
    if is_prob op then "pop" else
    if is_ctnt op then "cnst" else "op" in

  let pp_decl _fmt _d = () in           (* FIXME *)
  Format.fprintf fmt "%s %a%a %a."
    (str_kind d) pp_optyparams d.op_params pp_path p
    pp_decl d
