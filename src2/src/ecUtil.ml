(** Useful functions to print messages and raise errors. *)
open Format

(*TODO: Use this flags to change how to print errors for emacs*)
let emacs_mode = ref false

let set_emacs_mode b = 
  Format.set_tags true;
  Format.set_mark_tags false;
  let olds = Format.get_formatter_tag_functions () in
  let open_tags = function
    | "info"  -> Format.printf "[info]"
    | "error" -> Format.printf "[error]"
    | x       -> olds.print_open_tag x
  in 
  Format.set_formatter_tag_functions {olds with print_open_tag = open_tags};
  emacs_mode := b


let print_prompt gnum pdepth withproof timeout rhl_cntr =
  if !emacs_mode then 
    Format.printf "@\n[%d|%d|%s|%d|%d]> @?" 
      gnum pdepth withproof
      timeout rhl_cntr
  else
    Format.printf "@\n>@?"

let debug_level = ref 1

let set_debug n =
  (* Format.printf "set debug %d -> %d@." !debug_level n; *)
  debug_level := n

let debug n format =
  if !debug_level >= n
  then Format.printf format
  else Format.ifprintf Format.std_formatter format

let verbose fmt =
  let f _ = debug 1 "@{<info> %s@}@." (Format.flush_str_formatter ()) in
  Format.kfprintf f Format.str_formatter fmt

let warning fmt =
  let f _ = Format.printf "[warning] %s@." (Format.flush_str_formatter ()) in
  Format.kfprintf f Format.str_formatter fmt

type point = int * int * int (* char * line * col *)
type pos = string * point * point

let dummy_pos = ("", (0,0,0), (0,0,0))

let pp_line fmt (l1,l2) = 
  if l1 = l2 then Format.fprintf fmt "%i" l1 
  else Format.fprintf fmt "%i-%i" l1 l2 

let pp_pos fmt (fname, (a1,l1,c1), (a2,l2,c2) as pos) =
  if pos <> dummy_pos then 
    if fname = "<stdin>" || !emacs_mode || fname = "" then
      Format.fprintf fmt "Toplevel input, characters %d-%d" a1 a2
    else
      Format.fprintf fmt "File %s, line %a, characters %d-%d" fname 
        pp_line (l1,l2) c1 c2  
 
let pp_list
    ?(pre=format_of_string "@[")
    ?(sep=format_of_string "")
    ?(suf=format_of_string "@]")
    pp_elt f l =
  let rec aux f l =
    match l with
        [] -> ()
      | e::l -> Format.fprintf f "%(%)%a%a" sep pp_elt e aux l
  in match l with
      [] -> ()
    | e::l -> Format.fprintf f "%(%)%a%a%(%)" pre pp_elt e aux l suf

let pp_string_list ~sep fmt l =
  pp_list ~sep Format.pp_print_string fmt l

let pp_pos_string_list ~sep fmt l =
  pp_list ~sep (fun fmt (_, s) -> Format.pp_print_string fmt s) fmt l


exception LexicalError of pos * string
exception ParseError of pos * string
exception StopParsing

exception PosError of pos * string
exception EcError of string
exception NotImplementedYet of string
exception Bug of string

exception CannotApply of string * string

let _ = Format.pp_set_margin Format.str_formatter 80
(* let _ = Format.pp_set_max_indent Format.str_formatter 2 *)

let not_implemented fmt =
  let f _ =
    let msg = Format.flush_str_formatter () in raise (NotImplementedYet msg)
  in Format.kfprintf f Format.str_formatter fmt

let bug fmt =
  let f _ = let msg = Format.flush_str_formatter () in raise (Bug msg)
  in Format.kfprintf f Format.str_formatter fmt

let assert_bug c fmt =
  if c then Format.ifprintf Format.std_formatter fmt
  else bug fmt

let user_error fmt =
  let f _ = let msg = Format.flush_str_formatter () in raise (EcError msg)
  in Format.kfprintf f Format.str_formatter fmt

let cannot_apply cmd fmt =
  let f _ =
    let msg = Format.flush_str_formatter () in
    raise (CannotApply (cmd, msg)) in
  Format.kfprintf f Format.str_formatter fmt


let pos_error pos fmt =
  let f _ = let msg = Format.flush_str_formatter () in
            raise (PosError (pos,msg))
  in Format.kfprintf f Format.str_formatter fmt

let pos_of_lex_pos pos1 pos2 =
  let col p = p.Lexing.pos_cnum - p.Lexing.pos_bol in
  let line p = p.Lexing.pos_lnum in
  let pt1 = (pos1.Lexing.pos_cnum, line pos1, col pos1) in
  let pt2 = (pos2.Lexing.pos_cnum, line pos2, col pos2) in
  let pos = (pos1.Lexing.pos_fname, pt1, pt2) in
  pos

type op_token =
  | TK_AND | TK_OR | TK_IMPL | TK_IFF | TK_XOR
  | TK_PLUS | TK_STAR | TK_MINUS | TK_DIV | TK_MOD
  | TK_HAT | TK_TILD | TK_CONS | TK_APP | TK_NOT
  | TK_LT | TK_LE | TK_GT | TK_GE | TK_EQ | TK_NEQ

let get_tk_name tk = match tk with
  | TK_AND   -> "&&"
  | TK_OR    -> "||"
  | TK_IMPL  -> "=>"
  | TK_IFF  -> "<=>"
  | TK_XOR   -> "^^"
  | TK_PLUS  -> "+"
  | TK_STAR  -> "*"
  | TK_MINUS -> "-"
  | TK_DIV   -> "/"
  | TK_MOD   -> "%"
  | TK_HAT   -> "^"
  | TK_TILD  -> "~"
  | TK_CONS  -> "::"
  | TK_APP   -> "++"
  | TK_NOT   -> "!"
  | TK_LT    -> "<"
  | TK_LE    -> "<="
  | TK_GT    -> ">"
  | TK_GE    -> ">="
  | TK_EQ    -> "="
  | TK_NEQ    -> "<>"

(** Debug level *)

(* AskB: what is this for ?...*)
let db_count = ref 0
let add_db_level () = incr db_count;!db_count

let db_glob =  add_db_level ()
let db_var =  add_db_level ()
let db_wp = add_db_level ()
let db_add_loc =  add_db_level ()
let db_scope = db_add_loc
let db_type = db_add_loc


(** @raise PosError if the name is already registered in the table. *)
let check_not_in_tbl txt tbl name pos =
  try
    let _ = Hashtbl.find tbl name in
    pos_error pos "cannot redefine '%s'@,\
        this name has already been defined as a '%s'@."
      name txt
  with Not_found -> ()

let check_not_in_list txt l name pos =
  try
    let _ = List.assoc name l in
    pos_error pos "cannot redefine '%s'@,\
        this name has already been defined as a '%s'@."
      name txt
  with Not_found -> ()

(** Function over list *)

let rec list_hdn n l =
  if n <= 0 then []
  else
    match l with
      | [] -> raise (Invalid_argument "list_hdn")
      | hd::tl -> hd::list_hdn (n-1) tl

let list_shop n l =
  let rec aux r n l =
    if n <= 0 then List.rev r, l
    else
      match l with
        | [] -> List.rev r, []
        | a::l -> aux (a::r) (n-1) l
  in aux [] n l

let rec eq_list f l1 l2 =
  match l1, l2 with
    | [], [] -> true
    | x1::l1, x2::l2 -> f x1 x2 && eq_list f l1 l2
    | _, _ -> false

let find_at x l =
  let rec aux k l =
    match l with
      | [] -> raise Not_found
      | a::_ when a = x -> k
      | _::l -> aux (k+1) l in
  aux 0 l

let unopt dfl = function
  | Some x -> x
  | None   -> dfl

module StringSet = Map.Make(struct
  type t = string
  let  compare = (Pervasives.compare : t -> t -> int)
end)

module StringMap = Map.Make(struct
  type t = string
  let  compare = (Pervasives.compare : t -> t -> int)
end)

let rec uniq xs =
  match xs with
    | []      -> true
    | x :: xs -> (not (List.mem x xs)) && (uniq xs)

let try_find p xs =
  try  Some (List.find p xs)
  with Not_found -> None

module Options =
struct
  let bind (f : 'a -> 'b) (x : 'a option) =
    match x with
      | None   -> None
      | Some x -> Some (f x)
end

module UID = struct
  type uid = unit ref
end
