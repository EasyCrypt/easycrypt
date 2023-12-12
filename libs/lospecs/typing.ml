(* -------------------------------------------------------------------- *)
open Ptree

(* -------------------------------------------------------------------- *)
module Ident : sig
  type ident

  val create : string -> ident
  val name : ident -> string
  val id : ident -> int
end = struct
  type ident = symbol * int

  let create (x : string) : ident = (x, Oo.id (object end))
  let name ((x, _) : ident) : string = x
  let id ((_, i) : ident) : int = i
end

(* -------------------------------------------------------------------- *)
type ident = Ident.ident

(* -------------------------------------------------------------------- *)
type aword = [ `W of int ] [@@deriving show]

(* -------------------------------------------------------------------- *)
type atype = [ aword | `Signed | `Unsigned ] [@@deriving show]

(* -------------------------------------------------------------------- *)
type aarg = ident * aword

(* -------------------------------------------------------------------- *)
type aargs = aarg list

(* -------------------------------------------------------------------- *)
module Env : sig
  type env

  val empty : env
  val lookup : env -> symbol -> (ident * atype) option
  val push : env -> symbol -> atype -> env * ident
  val export : env -> (symbol, ident * atype) Map.t
end = struct
  type env = { vars : (symbol, ident * atype) Map.t }

  let empty : env = { vars = Map.empty }
  let lookup (env : env) (x : symbol) = Map.find_opt x env.vars

  let push (env : env) (x : symbol) (ty : atype) =
    let idx = Ident.create x in
    let env = { vars = Map.add x (idx, ty) env.vars } in
    (env, idx)

  let export (env : env) : (symbol, ident * atype) Map.t = env.vars
end

(* -------------------------------------------------------------------- *)
type env = Env.env

(* -------------------------------------------------------------------- *)
let tt_pword (_ : env) (`W ty : pword) : atype = `W ty

(* -------------------------------------------------------------------- *)
exception TypingError of string

(* -------------------------------------------------------------------- *)
let tyerror msg =
  let buf  = Buffer.create 0 in
  let fbuf = Format.formatter_of_buffer buf in
  Format.kfprintf
    (fun _ ->
      Format.pp_print_flush fbuf ();
      raise (TypingError (Buffer.contents buf)))
    fbuf msg

(* -------------------------------------------------------------------- *)
(* Get type of expr, fail if different from check (if check is given)   *)
let rec tt_expr (env : env) ?(check : atype option) (e : pexpr) : env * atype =
  match e with
  | PEParens _e -> tt_expr env ?check _e
  (* defaults to unsigned *)
  | PEInt _i -> (env, `Unsigned)
  (* will need to add typecast compatibility check, unnecessary for now *)
  (* TODO: Make types compatible across files*)
  | PECast (t, _e) -> (
      let t =
        match t with
        | `W x -> `W x
        | `Unsigned -> `Unsigned
        | `Signed -> `Signed
      in
      match check with
      | Some _t -> if t = _t then (env, t) else tyerror "Bad typecast"
      | None -> (env, t))
  (* to be changed later when introducing more types, such as function types *)
  (* for now, anonymous functions have type equal to their return type *)
  | PEFun (_args, _e) ->
      let _env, _args = tt_args env _args in
      tt_expr _env ?check _e
  | PEVar _v -> (
      match Env.lookup env _v with
      | Some (_, _t) -> (env, _t)
      | None -> tyerror "Bad reference to variable: %s" _v
      )
  | PELet ((v, _e1), _e2) ->
      let _env, _ =
        let env, _t = tt_expr env _e1 in
        Env.push env v _t
      in
      tt_expr _env ?check _e2
  (* TODO: add bounds checking? maybe change slice notation to allow for easier parsing *)
  (*       when beginning is variable but length is fixed                               *)
  (* slice is also short circuiting all checks right now                                *)
  (* [a:b] = [a:b:1].     [a:b:c] = starting from a, get c bits b times                 *)
  (* If resulting word length is fixed then return Word of that size                    *)
  (* Otherwise return type of thing being sliced                                        *)
  | PESlice (_ev, (_eib, _eic, _eil)) -> (
      let env, _tv = tt_expr env _ev in
      let env, _tib = tt_expr env _eib in
      let env, _tic = tt_expr env _eic in
      match _eil with
      | Some (PEInt m) -> (
          match _eic with PEInt n -> (env, `W (n * m)) | _ -> (env, _tv))
      | Some _eil ->
          let env, _ = tt_expr env _eil in
          (env, _tv)
      | _ -> ( match _eic with PEInt n -> (env, `W n) | _ -> (env, _tv)))
  (* needs function types to actually make sense for now just gets an unsigned integer *)
  (* TODO: Implement function types so this makes sense ? *)
  | PEApp (("add", _wl), _eal) -> (
      match _wl with
      | Some [ `W n ] -> (
          match
            List.map
              (fun a ->
                let _, x = tt_expr env a in
                x)
              _eal
          with
          | [ `W n1; `W n2 ] ->
              if n1 == n2 && n2 == n then (env, `W n)
              else tyerror "bad inputs for add"
          | _ -> (env, `W n) (* automatic conversion of ints to words *))
      | _ -> (env, `Unsigned))
  | PEApp (("and", _wl), _eal) -> (
      match _wl with
      | Some [ `W n ] -> (
          match
            List.map
              (fun a ->
                let _, x = tt_expr env a in
                x)
              _eal
          with
          | [ `W n1; `W n2 ] ->
              if n1 == n2 && n2 == n then (env, `W n)
              else tyerror "bad inputs for and"
          | _ -> (env, `W n) (* automatic conversion of ints to words *))
      | _ -> (env, `Unsigned))
  | PEApp (("concat", _wl), _eal) -> (
      match _wl with
      | Some [ `W n ] -> (
          let _tal =
            List.map
              (fun a ->
                let _, x = tt_expr env a in
                x)
              _eal
          in
          match _tal with
          | [ `W k; `W l ] ->
              if k == l && k == n then (env, `W (k * 2))
              else tyerror "Wrong size args for concat"
          | _ -> (env, `W (n * 2)))
      | _ -> tyerror "width required for concat")
  | PEApp (("mult", _wl), _eal) -> (
      match _wl with
      | Some [ `W n ] -> (
          match
            List.map
              (fun a ->
                let _, x = tt_expr env a in
                x)
              _eal
          with
          | [ `W n1; `W n2 ] ->
              if n1 == n2 && n2 == n then (env, `W (2 * n))
              else tyerror "bad inputs for mult"
          | _ -> (env, `W (2 * n)))
      | _ -> (env, `Unsigned))
  | PEApp (("repeat", _wl), _eal) -> (
      match _wl with
      | Some [ `W n ] -> (
          match _eal with
          | [ _e1; PEInt k ] -> (
              match tt_expr env _e1 with
              | _, `W m ->
                  if n == m then (env, `W (n * k))
                  else tyerror "Wrong length input for repeat"
              | _ -> (env, `W (n * k)))
          | _ -> tyerror "only fixed repeat allowed")
      | _ -> tyerror "width is required for repeat")
  | PEApp (("or", _wl), _eal) -> (
      match _wl with
      | Some [ `W n ] -> (
          match
            List.map
              (fun a ->
                let _, x = tt_expr env a in
                x)
              _eal
          with
          | [ `W n1; `W n2 ] ->
              if n1 == n2 && n2 == n then (env, `W n)
              else tyerror "bad inputs for or"
          | _ -> (env, `W n) (* automatic conversion of ints to words *))
      | _ -> (env, `Unsigned))
  | PEApp (("SatToUW", _wl), _eal) -> (
      match _wl with
      | Some [ `W n ] -> (
          match _eal with
          | [ _e1; PEInt k ] -> (
              match tt_expr env _e1 with
              | _, `W m ->
                  if n == m then (env, `W n)
                  else tyerror "Bad input size to SatToUW"
              | _ -> (env, `W n))
          | _ -> tyerror "Second argument to SatToUW must be constant")
      | _ -> tyerror "SatToUW needs bit length input in <n>")
  | PEApp (("SatToSW", _wl), _eal) -> (
      match _wl with
      | Some [ `W n ] -> (
          match _eal with
          | [ _e1; PEInt k ] -> (
              match tt_expr env _e1 with
              | _, `W m ->
                  if n == m then (env, `W n)
                  else tyerror "Bad input size to SatToUW"
              | _ -> (env, `W n))
          | _ -> tyerror "Second argument to SatToSW must be constant")
      | _ -> tyerror "SatToSW needs bit length input in <n>")
  | PEApp (("sla", _wl), _eal) -> (
      match _wl with
      | Some [ `W n ] -> (
          match
            List.map
              (fun a ->
                let _, x = tt_expr env a in
                x)
              _eal
          with
          | [ `W n1; `W n2 ] ->
              if n1 == n2 && n2 == n then (env, `W n)
              else tyerror "bad inputs for sla"
          | _ -> (env, `W n) (* automatic conversion of ints to words *))
      | _ -> (env, `Unsigned))
  | PEApp (("sra", _wl), _eal) -> (
      match _wl with
      | Some [ `W n ] -> (
          match
            List.map
              (fun a ->
                let _, x = tt_expr env a in
                x)
              _eal
          with
          | [ `W n1; `W n2 ] ->
              if n1 == n2 && n2 == n then (env, `W n)
              else tyerror "bad inputs for sra"
          | _ -> (env, `W n) (* automatic conversion of ints to words *))
      | _ -> (env, `Unsigned))
  | PEApp (("srl", _wl), _eal) -> (
      match _wl with
      | Some [ `W n ] -> (
          match
            List.map
              (fun a ->
                let _, x = tt_expr env a in
                x)
              _eal
          with
          | [ `W n1; `W n2 ] ->
              if n1 == n2 && n2 == n then (env, `W n)
              else tyerror "bad inputs for srl"
          | _ -> (env, `W n) (* automatic conversion of ints to words *))
      | _ -> (env, `Unsigned))
  | PEApp (("sub", _wl), _eal) -> (
      match _wl with
      | Some [ `W n ] -> (
          match
            List.map
              (fun a ->
                let _, x = tt_expr env a in
                x)
              _eal
          with
          | [ `W n1; `W n2 ] ->
              if n1 == n2 && n2 == n then (env, `W n)
              else tyerror "bad inputs for sub"
          | _ -> (env, `W n) (* automatic conversion of ints to words *))
      | _ -> (env, `Unsigned))
  | PEApp (("map", _wl), _eal) -> (
      match _eal with
      | PEFun (_aargs, _abodyexp) :: _eal -> (
          if List.length _eal != List.length _aargs then
            tyerror "Incorrect number of arguments to map"
          else
            let _fbenv, _taargs = tt_args env _aargs in
            let _taargs = List.map (fun (_, x) -> x) _taargs in
            let _tal =
              List.map
                (fun a ->
                  let _, x = (tt_expr env) a in
                  x)
                _eal
            in
            match _wl with
            | Some [ `W n; `W m ] ->
                if
                  true
                  || List.fold_left (* TODO: Fix this and remove ShortCir *)
                       (fun a b -> a && b == `W n)
                       true _taargs
                     && List.fold_left
                          (fun a b -> a && b == `W (n * m))
                          true _tal
                then
                  match tt_expr _fbenv _abodyexp with
                  | _, `W br -> (env, `W (br * m))
                  | _, `Unsigned -> (env, `W (n * m))
                  | _, `Signed -> (env, `W (n * m))
                  | _ -> tyerror "Bad anon function body ret type"
                else tyerror "Bad argument size to map"
            | _ -> tyerror "Map needs mapping size params")
      | _ -> tyerror "First argument to map should be function")
  | PEApp ((n, _), _eal) ->
      tyerror "Unknown combinator: %s" n
  | _ -> assert false

(* -------------------------------------------------------------------- *)
and tt_arg (env : env) ((x, `W ty) : parg) : env * aarg =
  let env, idx = Env.push env x (`W ty) in
  (env, (idx, `W ty))

(* -------------------------------------------------------------------- *)
and tt_args (env : env) (args : pargs) : env * aargs =
  List.fold_left_map tt_arg env args

(* -------------------------------------------------------------------- *)
let tt_def (env : env) (p : pdef) : env * (symbol * atype) =
  let _env, _args = tt_args env p.args in
  let _benv, _btype = tt_expr _env ~check:(tt_pword env p.rty) p.body in
  (_benv, (p.name, _btype))

(* -------------------------------------------------------------------- *)
let tt_program (env : env) (p : pprogram) : env * (symbol * atype) list =
  List.fold_left_map tt_def env p
