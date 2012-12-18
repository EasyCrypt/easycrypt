(* -------------------------------------------------------------------- *)
open EcUtils

(* -------------------------------------------------------------------- *)
type formatter = Format.formatter
type 'a pp = formatter -> 'a -> unit

(* -------------------------------------------------------------------- *)
let pp_err pp_elt x =
  Format.fprintf Format.err_formatter "@[%a@]@." pp_elt x

(* -------------------------------------------------------------------- *)
let pp_void (fmt : formatter) (_ : 'a) =
  Format.fprintf fmt "<abs>"

let pp_unit   (fmt : formatter) () = Format.fprintf fmt "()"
let pp_int    (fmt : formatter) i  = Format.fprintf fmt "%d" i
let pp_string (fmt : formatter) s  = Format.fprintf fmt "%s" s

(* -------------------------------------------------------------------- *)
let pp_id pp_elt fmt x =
  Format.fprintf fmt "%a" pp_elt x

(* -------------------------------------------------------------------- *)
let pp_pair pp1 pp2 fmt (x, y) =
  Format.fprintf fmt "(%a, %a)" pp1 x pp2 y

(* -------------------------------------------------------------------- *)
let pp_paren pp_elt fmt x =
  Format.fprintf fmt "(%a)" pp_elt x

(* --------------------------------------------------------------------  *)
let pp_opt_pre () = format_of_string ""
let pp_opt_pst () = format_of_string ""

let pp_option
    ?(pre=pp_opt_pre ())
    ?(pst=pp_opt_pst ()) pp_elt fmt x =

  oiter x
    (fun x ->
      Format.fprintf fmt "%(%)%a%(%)" pre pp_elt x pst)

(* -------------------------------------------------------------------- *)
let pp_list_pre () = format_of_string "@["
let pp_list_pst () = format_of_string "@]"
let pp_list_sep () = format_of_string ""

let pp_list
    ?(pre=pp_list_pre ())
    ?(sep=pp_list_sep ())
    ?(pst=pp_list_pst ()) pp_elt =

  let rec pp_list fmt = function
    | []      -> ()
    | x :: xs -> Format.fprintf fmt "%(%)%a%a" sep pp_elt x pp_list xs
  in
    fun fmt xs ->
      match xs with
      | []      -> ()
      | x :: xs -> Format.fprintf fmt "%(%)%a%a%(%)" pre pp_elt x pp_list xs pst
