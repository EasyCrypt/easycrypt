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
let pp_tydecl env fmt (p, td) =
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
    let x = if (op_ctnt op) then "cnst" else "op" in
    let x = if op.op_prob then "p"^x else x in
      x
  in

  let pp_decl fmt d = ()
(*
    match d.op_body with
    | None ->
        if d.op_ctnt then 
          Format.fprintf fmt ": %a" (pp_type ~vmap) (snd d.op_sig)
        else 
          Format.fprintf fmt ": %a -> %a" 
            pp_tparams (fst d.op_sig) (pp_type ~vmap) (snd d.op_sig)
    | Some (id,e) ->
      if d.op_ctnt then
        Format.fprintf fmt ": %a = %a" (pp_type ~vmap) (snd d.op_sig) pp
      else
        assert false
*)
  in
    Format.fprintf fmt "%s %a%a %a."
      (str_kind d) pp_optyparams d.op_params pp_path p
      pp_decl d

(* -------------------------------------------------------------------- *)
let rec pp_env fmt (env : EcEnv.env) =
  let env = EcEnv.preenv env in
  let pp_premc fmt mc =
    Format.fprintf fmt "@,@[<v 4>  { %a@]}" pp_premc mc
  in
    Format.fprintf fmt "scope = %a@." pp_path env.env_scope;
    Format.fprintf fmt "root  = %a@." pp_premc env.env_root;
    Format.fprintf fmt "comps = %a@."
      (Mid.pp EcIdent.pp_ident (pp_pair pp_path pp_premc))
      env.EcEnv.env_comps

and pp_premc fmt (mc : EcEnv.premc) =
  Format.fprintf fmt "variables  = %a@," (IM.pp ~align:true (pp_pair pp_path pp_void)) mc.mc_variables ;
  Format.fprintf fmt "functions  = %a@," (IM.pp ~align:true (pp_pair pp_path pp_void)) mc.mc_functions ;
  Format.fprintf fmt "modules    = %a@," (IM.pp ~align:true (pp_pair pp_path pp_void)) mc.mc_modules   ;
  Format.fprintf fmt "modtypes   = %a@," (IM.pp ~align:true (pp_pair pp_path pp_void)) mc.mc_modtypes  ;
  Format.fprintf fmt "typedecls  = %a@," (IM.pp ~align:true (pp_pair pp_path pp_void)) mc.mc_typedecls ;
  Format.fprintf fmt "operators  = %a@," (IM.pp ~align:true (pp_pair pp_path pp_void)) mc.mc_operators ;
  Format.fprintf fmt "axioms     = %a@," (IM.pp ~align:true (pp_pair pp_path pp_void)) mc.mc_axioms    ;
  Format.fprintf fmt "theories   = %a@," (IM.pp ~align:true (pp_pair pp_path pp_void)) mc.mc_theories  ;
  Format.fprintf fmt "components = %a@," (IM.pp ~align:true pp_unit)                   mc.mc_components;
