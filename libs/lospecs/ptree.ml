(* -------------------------------------------------------------------- *)
(* Typing hint: env[symbol] *)
type symbol =
  string

type pword =
  W of int

type ptype =
  | Unsigned
  | Signed
  | Word of int

let pp_type (fmt: Format.formatter) (t: ptype) =
    match t with
    | Unsigned -> Format.fprintf fmt "unsigned"
    | Signed -> Format.fprintf fmt "signed"
    | Word x -> Format.fprintf fmt "W%@%d" x

type parg =
  symbol * pword

let pp_arg (fmt: Format.formatter) (arg: parg) = 
    let (name, len) = arg in
    let W len = len in 
    Format.fprintf fmt "@[%s@%d@]" name len 

type pargs =
  parg list

let pp_args (fmt: Format.formatter) (args: pargs) =
    Format.pp_print_list ~pp_sep:(fun out () -> Format.fprintf out ",@ ") pp_arg fmt args

type pfname =
  symbol * pword list option

let pp_fname (fmt: Format.formatter) (fname: pfname) = 
    let name, ns = fname in 
    match ns with 
    | Some ns -> Format.fprintf fmt "@[%s<%a>@]" name (fun out l -> Format.pp_print_list ~pp_sep:(fun out () -> Format.fprintf out ",") (fun fmt w -> let W w = w in Format.fprintf fmt "%d" w) out l) ns
    | None -> Format.fprintf fmt "@[%s@]" name

type pexpr =
  | PEParens of pexpr               (* type: typeof(pexpr) *)
  | PEInt    of int                 (* type: int *)
  | PECast   of ptype * pexpr       (* type: ptype (check if convertible) *)
  | PEFun    of pargs * pexpr       (* type: add ret type to env (calculate on the fly?) *)
  | PELet    of (symbol * pexpr) * pexpr (* typeof: second pexpr with symbol added to env as type of first expr *)
  | PESlice  of pexpr * (pexpr * pexpr * pexpr option) (* type: same type as first expr *)
  | PEApp    of pfname * pexpr list (* if args match fun type then fun ret else type error *)

let rec pp_expr (fmt: Format.formatter) (expr: pexpr) =
    match expr with
    | PEParens e -> Format.fprintf fmt "@[(%a)@]" pp_expr e
    | PEInt n -> Format.fprintf fmt "%d" n
    | PECast (t, e) -> Format.fprintf fmt "@[(%a) %a@]" pp_type t pp_expr e
    | PEFun (a, e) -> Format.fprintf fmt "@[f (%a) -> %a@]" pp_args a pp_expr e 
    | PELet ((s, e1), e2) -> Format.fprintf fmt "@[let %s = %a in @, %a@]" s pp_expr e1 pp_expr e2
    | PESlice (e1, (e2, e3, eo)) -> ( match eo with
                                      | Some e4 -> Format.fprintf fmt "@[%a[%a:%a:%a]@]" pp_expr e1 pp_expr e2 pp_expr e3 pp_expr e4
                                      | None -> Format.fprintf fmt "@[%a[%a:%a]@]" pp_expr e1 pp_expr e2 pp_expr e3 )
    | PEApp (fn, el) -> Format.fprintf fmt "@[%a(%a)@]" pp_fname fn (Format.pp_print_list ~pp_sep:(fun out () -> Format.fprintf out ",@ ") pp_expr) el

type pdef = {
  name : symbol;
  args : pargs;
  rty  : pword;
  body : pexpr;
}

let pp_def (fmt: Format.formatter) (def: pdef) = 
    let W rty = def.rty in
    Format.fprintf fmt "@[%s : (%a) @. rty: %d @. %a @]" def.name pp_args def.args rty pp_expr def.body

type pprogram =
  pdef list

let pp_program (fmt: Format.formatter) (prog: pprogram) = 
    Format.pp_print_list ~pp_sep:(fun out () -> Format.fprintf out "@.") pp_def fmt prog
