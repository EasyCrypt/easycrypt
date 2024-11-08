(* -------------------------------------------------------------------- *)
open Ptree
open Ast

(* -------------------------------------------------------------------- *)
let as_seq1 (type t) (xs : t list) : t =
  match xs with [ x ] -> x | _ -> assert false

(* -------------------------------------------------------------------- *)
let as_seq2 (type t) (xs : t list) : t * t =
  match xs with [ x; y ] -> (x, y) | _ -> assert false

(* -------------------------------------------------------------------- *)
module Env : sig
  type env

  type sig_ = aword list option * atype

  val empty : env
  val lookup : env -> symbol -> (ident * sig_) option
  val push : env -> symbol -> sig_ -> env * ident
  val export : env -> (symbol, ident * sig_) Map.t
end = struct
  type sig_ = aword list option * atype

  type env = { vars : (symbol, ident * sig_) Map.t }

  let empty : env = { vars = Map.empty }

  let lookup (env : env) (x : symbol) = Map.find_opt x env.vars

  let push (env : env) (x : symbol) (sig_ : sig_) =
    let idx = Ident.create x in
    let env = { vars = Map.add x (idx, sig_) env.vars } in
    (env, idx)

  let export (env : env) : (symbol, ident * sig_) Map.t = env.vars
end

(* -------------------------------------------------------------------- *)
type env = Env.env

(* -------------------------------------------------------------------- *)
let tt_pword (_ : env) ({ data = `W ty } : pword) : aword = `W ty

(* -------------------------------------------------------------------- *)
exception TypingError of range * string

(* -------------------------------------------------------------------- *)
let mk_tyerror_r (rg : range) (f : exn -> 'a) msg =
  let buf = Buffer.create 0 in
  let fbuf = Format.formatter_of_buffer buf in
  Format.kfprintf
    (fun _ ->
      Format.pp_print_flush fbuf ();
      f (TypingError (rg, Buffer.contents buf)))
    fbuf msg

(* -------------------------------------------------------------------- *)
let mk_tyerror (range : range) msg =
  mk_tyerror_r range identity msg

(* -------------------------------------------------------------------- *)
let tyerror (range : range) msg =
  mk_tyerror_r range (fun e -> raise e) msg

(* -------------------------------------------------------------------- *)
let tt_type (_ : env) (t : ptype) : atype =
  (t.data :> atype)

(* -------------------------------------------------------------------- *)
let tt_type_parameters
  (env : env)
  (range : range)
  (who : symbol)
  ~(expected : int)
  (tp : pword list option)
=
  match tp with
  | None -> tyerror range "missing type parameters annotation"
  | Some tp ->
      let tplen = List.length tp in
      if expected <> tplen then begin
        tyerror range
          "invalid number of type parameters for `%s': expected %d, got %d"
          who expected tplen
      end;
      (List.map (tt_pword env) tp)

(* -------------------------------------------------------------------- *)
let check_arguments_count (range : range) ~(expected : int) (args : pexpr list) =
  if List.length args <> expected then
    tyerror range "invalid number of arguments";
  args

(* -------------------------------------------------------------------- *)
let check_plain_arg (_ : env) (arg : pexpr option loced) =
  match arg.data with
  | None -> begin
      tyerror
        arg.range
        "this argument cannot be generalized (not in a higher-order context)"
    end
  | Some arg ->
    arg

(* -------------------------------------------------------------------- *)
let as_int_constant (e : pexpr) : int =
  match e.data with
  | PEInt (i, None) -> i
  | _ -> tyerror e.range "integer constant expected"

(* -------------------------------------------------------------------- *)
type sig_ = {
  s_name : string;
  s_ntyparams : int;
  s_argsty : aword list -> aword list;
  s_retty : aword list -> aword;
  s_mk : aword list -> aexpr list -> aexpr_;
}

(* -------------------------------------------------------------------- *)
module Sigs : sig
  val sla : sig_
  val sra : sig_
  val sll : sig_
  val srl : sig_
  val usat : sig_
  val ssat : sig_
  val uextend : sig_
  val sextend : sig_
  val not : sig_
  val incr : sig_
  val add : sig_
  val ssadd : sig_
  val usadd : sig_
  val sub : sig_
  val and_ : sig_
  val or_ : sig_
  val xor_ : sig_
  val umul : sig_
  val umullo : sig_
  val umulhi : sig_
  val smul : sig_
  val smullo : sig_
  val smulhi : sig_
  val usmul : sig_
  val sgt : sig_
  val sge : sig_
  val ugt : sig_
  val uge : sig_
  val popcount : sig_
end = struct
  let mk1 (f : aexpr -> aexpr_) (a : aexpr list) =
    f (as_seq1 a)

  let mk2 (f : aexpr -> aexpr -> aexpr_) (a : aexpr list) =
    let x, y = as_seq2 a in f x y

  let uniop ?(ret = fun x -> x) ~(name : string) mk = {
    s_name = name;
    s_ntyparams = 1;
    s_argsty = (fun ws -> [as_seq1 ws]);
    s_retty = (fun ws -> `W (ret (get_size (as_seq1 ws))));
    s_mk = fun ws -> mk1 (mk ws);
  }
  
  let binop ?(ret = fun x -> x) ~(name : string) mk = {
    s_name = name;
    s_ntyparams = 1;
    s_argsty = (fun ws -> List.make 2 (as_seq1 ws));
    s_retty = (fun ws -> `W (ret (get_size (as_seq1 ws))));
    s_mk = fun ws -> mk2 (mk ws);
  }

  let satop ~(name : string) (k : us) = {
    s_name = name;
    s_ntyparams = 2;
    s_argsty = (fun ws -> [fst (as_seq2 ws)]);
    s_retty = (fun ws -> snd (as_seq2 ws));
    s_mk = (fun ws -> mk1 (fun x -> ESat (k, snd (as_seq2 ws), x)));
  }

  let extendop ~(name : string) (k : us) = {
    s_name = name;
    s_ntyparams = 2;
    s_argsty = (fun ws -> [fst (as_seq2 ws)]);
    s_retty = (fun ws -> snd (as_seq2 ws));
    s_mk = (fun ws -> mk1 (fun x -> EExtend (k, snd (as_seq2 ws), x)));
  }

  let shiftop ~(name : string) (d : lr) (k : la) = {
    s_name = name;
    s_ntyparams = 1;
    s_argsty = (fun ws -> [as_seq1 ws; `W 8]);
    s_retty = (fun ws -> as_seq1 ws);
    s_mk = (fun _ -> mk2 (fun x y -> EShift (d, k, (x, y))));
  }

  let mulop ?ret ~(name : string) (k : mulk) =
    let mk = fun ws x y ->
      let w = as_seq1 ws in
      EMul (k, w, (x, y))
    in
    binop ?ret ~name mk

  let sla : sig_ =
    shiftop ~name:"sla" `L `A

  let sra : sig_ =
    shiftop ~name:"sra" `R `A

  let sll : sig_ =
    shiftop ~name:"sll" `L `L

  let srl : sig_ =
    shiftop ~name:"srl" `R `L
    
  let usat : sig_ =
    satop ~name:"usat" `U

  let ssat : sig_ =
    satop ~name:"ssat" `S

  let uextend : sig_ =
    extendop ~name:"uextend" `U
  
  let sextend : sig_ =
    extendop ~name:"sextend" `S

  let not : sig_ =
    let mk = fun ws x -> ENot (as_seq1 ws, x) in
    uniop ~name:"not" mk

  let incr : sig_ =
    let mk = fun ws x -> EIncr (as_seq1 ws, x) in
    uniop ~name:"incr" mk

  let add : sig_ =
    let mk = fun ws x y -> EAdd (as_seq1 ws, `Word, (x, y)) in
    binop ~name:"add" mk

  let ssadd : sig_ =
    let mk = fun ws x y -> EAdd (as_seq1 ws, `Sat `S, (x, y)) in
    binop ~name:"ssadd" mk

  let usadd : sig_ =
    let mk = fun ws x y -> EAdd (as_seq1 ws, `Sat `U, (x, y)) in
    binop ~name:"usadd" mk

  let sub : sig_ =
    let mk = fun ws x y -> ESub (as_seq1 ws, (x, y)) in
    binop ~name:"sub" mk

  let and_ : sig_ =
    let mk = fun ws x y -> EAnd (as_seq1 ws, (x, y)) in
    binop ~name:"and" mk

  let or_ : sig_ =
    let mk = fun ws x y -> EOr (as_seq1 ws, (x, y)) in
    binop ~name:"or" mk

  let umul : sig_ =
    mulop ~ret:(fun n -> 2 * n) ~name:"umul" (`U `D)

  let umulhi : sig_ =
    mulop ~name:"umulhi" (`U `H)
  
  let umullo : sig_ =
    mulop ~name:"umullo" (`U `L)  

  let smul : sig_ =
    mulop ~ret:(fun n -> 2 * n) ~name:"smul" (`S `D)

  let smulhi : sig_ =
    mulop ~name:"smulhi" (`S `H)

  let smullo : sig_ =
    mulop ~name:"smullo" (`S `L)  

  let usmul : sig_ =
    mulop ~ret:(fun n -> 2 * n) ~name:"usmul" `US

  let sgt : sig_ =
    let mk = fun ws x y -> ECmp (as_seq1 ws, `S, `Gt, (x, y)) in
    binop ~ret:(fun _ -> 1) ~name:"sgt" mk

  let sge : sig_ =
    let mk = fun ws x y -> ECmp (as_seq1 ws, `S, `Ge, (x, y)) in
    binop ~ret:(fun _ -> 1) ~name:"sge" mk

  let ugt : sig_ =
    let mk = fun ws x y -> ECmp (as_seq1 ws, `U, `Gt, (x, y)) in
    binop ~ret:(fun _ -> 1) ~name:"ugt" mk

  let uge : sig_ =
    let mk = fun ws x y -> ECmp (as_seq1 ws, `U, `Ge, (x, y)) in
    binop ~ret:(fun _ -> 1) ~name:"uge" mk

  let xor_ : sig_ =
    let mk = fun ws x y -> EXor (as_seq1 ws, (x, y)) in
    binop ~name:"xor" mk

  let popcount = {
      s_name = "popcount";
      s_ntyparams = 2;
      s_argsty = (fun ws -> [fst (as_seq2 ws)]);
      s_retty = (fun ws -> snd (as_seq2 ws));
      s_mk = (fun ws -> mk1 (fun x -> EPopCount (snd (as_seq2 ws), x)));
    }  
end

(* -------------------------------------------------------------------- *)
let sigs : sig_ list = [
  Sigs.sla;
  Sigs.sra;
  Sigs.sll;
  Sigs.srl;
  Sigs.usat;
  Sigs.ssat;
  Sigs.uextend;
  Sigs.sextend;
  Sigs.not;
  Sigs.incr;
  Sigs.add;
  Sigs.ssadd;
  Sigs.usadd;
  Sigs.sub;
  Sigs.and_;
  Sigs.or_;
  Sigs.xor_;
  Sigs.umul;
  Sigs.umullo;
  Sigs.umulhi;
  Sigs.smul;
  Sigs.smullo;
  Sigs.smulhi;  
  Sigs.usmul;
  Sigs.sgt;
  Sigs.sge;
  Sigs.ugt;
  Sigs.uge;
  Sigs.popcount;
]

(* -------------------------------------------------------------------- *)
let get_sig_of_name (name : string) : sig_ option =
  List.find_opt (fun x -> x.s_name = name) sigs

(* -------------------------------------------------------------------- *)
let ty_compatible ~(src : atype) ~(dst : atype) : bool =
  match src, dst with
  | (`Signed | `Unsigned), `W _ -> true
  | _, _ -> src = dst

(* -------------------------------------------------------------------- *)
let join_types (ty1 : atype loced) (ty2 : atype loced) =
  match ty1.data, ty2.data with
  | `Unsigned, `W n -> `W n
  | `W n, `Unsigned -> `W n
  | _, _ ->
    if ty1.data <> ty2.data then
      tyerror
        (Lc.merge ty1.range ty2.range)
        "the branches of the conditional have incompatible types: %a / %a"
        pp_atype ty1.data pp_atype ty2.data
    else ty1.data

(* -------------------------------------------------------------------- *)
let rec tt_expr_ (env : env) (e : pexpr) : aargs option * aexpr =
  match e.data with
  | PEParens e ->
      (None, tt_expr env e)

  | PEInt (i, w) ->
      let w = Option.map (tt_pword env) w in
      let type_ = Option.default `Unsigned (w :> atype option) in
      let e = { node = EInt i; type_; } in
      (None, e)

  | PEFun (fargs, f) -> 
      let benv, args = tt_args env fargs in
      (Some args, tt_expr benv f)
  
  | PEFName { data = (v, None) } -> begin
    let (vid, (targs, vt)) = Option.get_exn
      (Env.lookup env (Lc.unloc v))
      (mk_tyerror v.range "unknown variable: %s" (Lc.unloc v)) in

    match targs with
    | None ->
      (None, { node = EVar vid; type_ = vt; })

    | Some targs ->
      let ftargs =
        List.map (fun ty -> (Ident.create "_", ty)) targs in
      let args =
        List.map
          (fun (x, ty) -> { node = EVar x; type_ = (ty :> atype) })
          ftargs in
      (Some ftargs, { node = EApp (vid, args); type_ = vt; })
    end

  | PEFName { data = (v, Some ws) } ->
      let sig_ =
        Option.get_exn
          (get_sig_of_name (Lc.unloc v))
          (mk_tyerror v.range "unkown symbol: %s" (Lc.unloc v))
      in

      let ws = List.map (tt_pword env) ws in
      let args = sig_.s_argsty ws in
      let retty = sig_.s_retty ws in
      let args = List.map (fun ty -> (Ident.create "_", ty)) args in

      let eargs =
        List.map (fun (x, ty) ->
          { node = EVar x; type_ = (ty :> atype); }
        ) args
      in
      let node = sig_.s_mk ws eargs in
      (Some args, { node; type_ = (retty :> atype); })

  | PELet ((v, args, e1), e2) ->
      let args, e1 =
        let env, args =
          args
            |> Option.map (tt_args env)
            |> Option.map (fun (e, a) -> (e, Some a))
            |> Option.default (env, None) in
        let e1 = tt_expr env e1 in
        (args, e1)
      in

      let ebody, vid =
        let targs = Option.map (List.map snd) args in
        Env.push env (Lc.unloc v) (targs, e1.type_) in

      let e2 = tt_expr ebody e2 in

      let node = ELet ((vid, args, e1), e2) in
      let type_ = e2.type_ in

      (None, { node; type_; })

  | PECond (c, (pe1, pe2)) -> 
    let c = tt_expr env c in (* FIXME: must be a word *)
    let e1 = tt_expr env pe1 in
    let e2 = tt_expr env pe2 in

    let type_ =
      join_types
        (Lc.mk pe1.range e1.type_)
        (Lc.mk pe2.range e2.type_)
    in

    let e1 = { e1 with type_ } in
    let e2 = { e2 with type_ } in

    let node = ECond (c, (e1, e2)) in

    (None, { node; type_; })

  | PESlice (ev, (start, len, scale)) ->
      let ev = tt_expr env ev in
      let start = tt_expr env start in
      let len = Option.default 1 (Option.map as_int_constant len) in
      let scale = Option.default 1 (Option.map as_int_constant scale) in
      let node = ESlice (ev, (start, len, scale))
      and type_ = `W (len * scale) in
      (None, { node; type_; })

  | PEAssign (ev, (start, len, scale), v) ->
    let ev = tt_expr env ev in
    let start = tt_expr env start in
    let len = Option.default 1 (Option.map as_int_constant len) in
    let scale = Option.default 1 (Option.map as_int_constant scale) in
    let v = tt_expr env ~check:(`W (len * scale)) v in
    let node = EAssign (ev, (start, len, scale), v) in
    (None, { node; type_ = ev.type_; })

  | PEApp ({ data = (f, None) }, args) ->
    let (vid, (targs, vt)) = Option.get_exn
      (Env.lookup env (Lc.unloc f))
      (mk_tyerror f.range "unknown symbol: %s" (Lc.unloc f)) in

    let targs =
      Option.get_exn
        targs
        (mk_tyerror f.range "the symbol `%s' cannot be applied" (Lc.unloc f)) in

    if List.length args <> List.length targs then begin
      tyerror e.range
        "invalid number of arguments: expected %d, got %d"
        (List.length targs) (List.length args)
    end;
  
    let bds, args = List.fold_left_map (fun bds (a, ety) ->
        match a.data with
        | None ->
          let x = Ident.create "_" in
          let a = { node = EVar x; type_ = (ety :> atype); }  in
          ((x, ety) :: bds, a)
        | Some a ->
          (bds, tt_expr env ~check:(ety :> atype) a)
      ) [] (List.combine args targs)
    in
  
    let bds = if List.is_empty bds then None else Some (List.rev bds) in
    let node = EApp (vid, args) in
  
    (bds, { node; type_ = vt; })
    
  | PEApp ({ data = ({ data = "concat" as f }, w) } as fn, args) ->
      let (`W w) = as_seq1 (tt_type_parameters env fn.range f ~expected:1 w) in
      let args = List.map (check_plain_arg env) args in
      let targs = List.map (tt_expr env ~check:(`W w)) args in
      let wsz = `W (w * List.length targs) in
      (None, { node = EConcat (wsz, targs); type_ = wsz; })

  | PEApp ({ data = ({ data = "repeat" as f }, w) } as fn, args) ->
      let (`W w) = as_seq1 (tt_type_parameters env fn.range f ~expected:1 w) in
      let args = List.map (check_plain_arg env) args in
      let e, n = as_seq2 (check_arguments_count e.range ~expected:2 args) in
      let n = as_int_constant n in
      let ne = tt_expr env ~check:(`W w) e in
      (None, { node = ERepeat (`W (w * n), (ne, n)); type_ = `W (w * n); })

  | PEApp ({ data = ({ data = "map" as c }, w) } as cn, args) ->
    let `W w, `W n = as_seq2 (tt_type_parameters env cn.range c ~expected:2 w) in
    let args = List.map (check_plain_arg env) args in

    if List.is_empty args then
      tyerror e.range "the combinator `map' takes at least one argument";

    let f, args = (List.hd args, List.tl args) in
    let nargs = List.map (tt_expr ~check:(`W (w * n)) env) args in

    let ftargs, ftbody = tt_expr_ env f in
  
    let ftype =
      match ftbody.type_ with
      | `W k -> k
      | _ -> tyerror f.range "the mapped function should return a word" in

    let ftargs =
      Option.get_exn
        ftargs
        (mk_tyerror f.range "this expression must be higher-order") in

    let targs = List.map snd ftargs in

    if targs <> List.make (List.length args) (`W w) then begin
      tyerror e.range
        "the mapped function must take exactly %d arguments of type @%d"
        (List.length targs) w
    end;

    let node = EMap ((`W w, `W n), (ftargs, ftbody), nargs)
    and type_ = `W (n * ftype) in
    (None, { node; type_; })

  | PEApp ({ data = (f, Some ws) } as fn, args) ->
      let sig_ =
        Option.get_exn
          (get_sig_of_name (Lc.unloc f))
          (mk_tyerror f.range "unknown symbol: %s" (Lc.unloc f))
      in
      tt_fname_app env e.range sig_ (Lc.mk fn.range ws) args

(* -------------------------------------------------------------------- *)
and tt_fname_app
  (env : env)
  (range : range)
  (sig_ : sig_)
  (ws : pword list loced)
  (args : pexpr option loced list)
=
  let ws =
    tt_type_parameters
      env ws.range sig_.s_name ~expected:sig_.s_ntyparams
      (Some ws.data)
  in

  let targs = sig_.s_argsty ws in

  if List.length args <> List.length targs then begin
    tyerror range 
      "invalid number of arguments for `%s': expected %d, get %d"
      sig_.s_name (List.length targs) (List.length args)
  end;

  let bds, args = List.fold_left_map (fun bds (a, ety) ->
      match a.data with
      | None ->
        let x = Ident.create "_" in
        let a = { node = EVar x; type_ = (ety :> atype); }  in
        ((x, ety) :: bds, a)
      | Some a ->
        (bds, tt_expr env ~check:(ety :> atype) a)
    ) [] (List.combine args targs)
  in

  let bds = if List.is_empty bds then None else Some (List.rev bds) in

  let node = sig_.s_mk ws args in
  let type_ = (sig_.s_retty ws :> atype) in

  (bds, { node; type_; })

(* -------------------------------------------------------------------- *)
and tt_expr (env : env) ?(check : atype option) (p : pexpr) : aexpr =
  let (args, {node = n_; type_ = t;}) = tt_expr_ env p in
  if not (Option.is_none args) then
    tyerror p.range "high-order functions not allowed here";
  check |> Option.may (fun dst ->
    if not (ty_compatible ~src:t ~dst) then begin
      tyerror p.range
        "this expression has type %a but is expected to have type %a"
        pp_atype t pp_atype dst
    end);
  { node = n_; type_ = Option.default t check; }

(* -------------------------------------------------------------------- *)
and tt_arg (env : env) ((x, { data = `W ty }) : parg) : env * aarg =
  let env, idx = Env.push env (Lc.unloc x) (None, `W ty) in
  (env, (idx, `W ty))

(* -------------------------------------------------------------------- *)
and tt_args (env : env) (args : pargs) : env * aargs =
  List.fold_left_map tt_arg env args

(* -------------------------------------------------------------------- *)
let tt_def (env : env) (p : pdef) : symbol * adef =
  let env, args = tt_args env p.args in
  let rty = tt_pword env p.rty in
  let bod = tt_expr env ~check:(rty :> atype) p.body in
  (p.name, { name = p.name; arguments = args; body = bod; rettype = rty; })

(* -------------------------------------------------------------------- *)
let tt_program (env : env) (p : pprogram) : (symbol * adef) list =
  List.map (tt_def env) p
