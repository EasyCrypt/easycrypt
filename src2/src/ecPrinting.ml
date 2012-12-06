(* -------------------------------------------------------------------- *)
open EcUtils
open EcTypes
open EcParsetree

module NameGen = EcUidgen.NameGen

(* -------------------------------------------------------------------- *)
let (~$) = format_of_string

(* -------------------------------------------------------------------- *)
let err pp_elt x =
  Format.fprintf Format.err_formatter "%a" pp_elt x

(* -------------------------------------------------------------------- *)
let pp_located loc pp_elt fmt x =
  Format.fprintf fmt "%s: %a" (Location.tostring loc) pp_elt x

(* -------------------------------------------------------------------- *)
let pp_id pp_elt fmt x =
  Format.fprintf fmt "%a" pp_elt x

(* -------------------------------------------------------------------- *)
let pp_paren pp_elt fmt x =
  Format.fprintf fmt "(%a)" pp_elt x

(* -------------------------------------------------------------------- *)
let pp_list_pre  () = format_of_string "@["
let pp_list_post () = format_of_string "@]"
let pp_list_sep  () = format_of_string ""

let pp_list
    ?(pre=pp_list_pre ())
    ?(sep=pp_list_sep ())
    ?(post=pp_list_post ()) pp_elt =

  let rec pp_list fmt = function
    | []      -> ()
    | x :: xs -> Format.fprintf fmt "%(%)%a%a" sep pp_elt x pp_list xs
  in
    fun fmt xs ->
      match xs with
      | []      -> ()
      | x :: xs -> Format.fprintf fmt "%(%)%a%a%(%)" pre pp_elt x pp_list xs post

(* -------------------------------------------------------------------- *)
let rec pp_qsymbol fmt = function
  | ([]    , x) -> Format.fprintf fmt "%s" x
  | (n :: p, x) -> Format.fprintf fmt "%s:>%a" n pp_qsymbol (p, x)

(* -------------------------------------------------------------------- *)
let rec pp_path fmt = function
  | EcPath.Pident x      -> Format.fprintf fmt "%s" (EcIdent.name x)
  | EcPath.Pqname (p, x) -> Format.fprintf fmt "%a:>%s" pp_path p (EcIdent.name x)

(* -------------------------------------------------------------------- *)
let pp_type (uidmap : NameGen.t) =
  let rec pp_type btuple fmt = function
    | Tbase Tunit      -> Format.fprintf fmt "unit"
    | Tbase Tbool      -> Format.fprintf fmt "bool"
    | Tbase Tint       -> Format.fprintf fmt "int"
    | Tbase Treal      -> Format.fprintf fmt "real"
    | Tbase Tbitstring -> Format.fprintf fmt "bitstring"

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

let pp_type ?(vmap : _ option) =
  let uidmap =
    match vmap with
    | None        -> NameGen.create ()
    | Some uidmap -> uidmap
  in
    pp_type uidmap false

let pp_dom fmt = 
  Format.fprintf fmt "(%a)" (pp_list ~sep:(~$", ") pp_type) 
