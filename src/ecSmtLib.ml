(* -------------------------------------------------------------------- *)
(* EasyCrypt SMTLib2 backend                                            *)
(*                                                                      *)
(* Translates EasyCrypt goals directly to the SMTLib2 text format and  *)
(* dispatches them to external SMT solvers, bypassing Why3.            *)
(*                                                                      *)
(* Architecture:                                                        *)
(*  - SMTLib2 AST + PP: standalone representation + printer            *)
(*  - Theory (module type): extensible theory signature                 *)
(*  - QFIA: Quantifier-Free Integer Arithmetic (QF_NIA)                *)
(*  - QF_DT: Quantifier-Free Datatypes                                 *)
(*  - ALL: All theories (integers + datatypes + booleans)              *)
(*  - Make(T : Theory): translator functor                              *)
(*  - Solver (module type): abstract solver interface supporting both   *)
(*      direct OCaml bindings and text-over-process backends            *)
(*  - Make_Text_Process(B): process-based solver via stdin/stdout       *)
(*  - Z3_Text, CVC5_Text: concrete text-based instances                *)
(*  - check: top-level entrypoint used by the tactic                   *)
(* -------------------------------------------------------------------- *)

open EcUtils
open EcPath
open EcAst
open EcTypes
open EcFol
open EcEnv

module BI  = EcBigInt
module Mid = EcIdent.Mid

(* ==================================================================== *)
(* SMTLib2 AST                                                          *)
(* ==================================================================== *)

type sort =
  | SInt
  | SBool
  | SCustom of string

type term =
  | TInt  of BI.zint          (** integer numeral (can be negative)    *)
  | TBool of bool
  | TVar  of string
  | TAdd  of term list        (** (+ t1 t2 ...)                        *)
  | TSub  of term * term      (** (- a b)                              *)
  | TNeg  of term             (** (- t) — unary minus                  *)
  | TMul  of term * term      (** (times a b)                          *)
  | TEq   of term * term      (** (= a b)                              *)
  | TLe   of term * term      (** (<= a b)                             *)
  | TLt   of term * term      (** (< a b)                              *)
  | TGe   of term * term      (** (>= a b)                             *)
  | TGt   of term * term      (** (> a b)                              *)
  | TAnd  of term list        (** (and t1 t2 ...)                      *)
  | TOr   of term list        (** (or t1 t2 ...)                       *)
  | TNot  of term             (** (not t)                              *)
  | TImpl of term * term      (** (=> a b)                             *)
  | TIte  of term * term * term (** (ite c t f)                        *)
  | TCtor of string * term list (** constructor application              *)
  | TMatch of term * (string * string list * term) list
  (** (match scrutinee ((ctor vars... body) ...))                       *)

(** A model is a list of (variable-name, value) pairs. *)
type model = (string * term) list

(* ==================================================================== *)
(* PP: SMTLib2 text serialiser                                          *)
(* ==================================================================== *)

module PP = struct
  let sort buf = function
    | SInt      -> Buffer.add_string buf "Int"
    | SBool     -> Buffer.add_string buf "Bool"
    | SCustom s -> Buffer.add_string buf s

  let rec term buf t =
    match t with
    | TInt n ->
      if BI.sign n < 0 then begin
        Buffer.add_string buf "(- ";
        Buffer.add_string buf (BI.to_string (BI.neg n));
        Buffer.add_char   buf ')'
      end else
        Buffer.add_string buf (BI.to_string n)

    | TBool b ->
      Buffer.add_string buf (if b then "true" else "false")

    | TVar s ->
      Buffer.add_string buf s

    | TAdd [] ->
      Buffer.add_string buf "0"

    | TAdd [t] ->
      term buf t

    | TAdd ts ->
      Buffer.add_string buf "(+";
      List.iter (fun t -> Buffer.add_char buf ' '; term buf t) ts;
      Buffer.add_char buf ')'

    | TSub (a, b) ->
      Buffer.add_string buf "(- ";
      term buf a; Buffer.add_char buf ' '; term buf b;
      Buffer.add_char buf ')'

    | TNeg t ->
      Buffer.add_string buf "(- ";
      term buf t;
      Buffer.add_char buf ')'

    | TMul (a, b) ->
      Buffer.add_string buf "(* ";
      term buf a; Buffer.add_char buf ' '; term buf b;
      Buffer.add_char buf ')'

    | TEq (a, b) ->
      Buffer.add_string buf "(= ";
      term buf a; Buffer.add_char buf ' '; term buf b;
      Buffer.add_char buf ')'

    | TLe (a, b) ->
      Buffer.add_string buf "(<= ";
      term buf a; Buffer.add_char buf ' '; term buf b;
      Buffer.add_char buf ')'

    | TLt (a, b) ->
      Buffer.add_string buf "(< ";
      term buf a; Buffer.add_char buf ' '; term buf b;
      Buffer.add_char buf ')'

    | TGe (a, b) ->
      Buffer.add_string buf "(>= ";
      term buf a; Buffer.add_char buf ' '; term buf b;
      Buffer.add_char buf ')'

    | TGt (a, b) ->
      Buffer.add_string buf "(> ";
      term buf a; Buffer.add_char buf ' '; term buf b;
      Buffer.add_char buf ')'

    | TAnd [] ->
      Buffer.add_string buf "true"

    | TAnd [t] ->
      term buf t

    | TAnd ts ->
      Buffer.add_string buf "(and";
      List.iter (fun t -> Buffer.add_char buf ' '; term buf t) ts;
      Buffer.add_char buf ')'

    | TOr [] ->
      Buffer.add_string buf "false"

    | TOr [t] ->
      term buf t

    | TOr ts ->
      Buffer.add_string buf "(or";
      List.iter (fun t -> Buffer.add_char buf ' '; term buf t) ts;
      Buffer.add_char buf ')'

    | TNot t ->
      Buffer.add_string buf "(not ";
      term buf t;
      Buffer.add_char buf ')'

    | TImpl (a, b) ->
      Buffer.add_string buf "(=> ";
      term buf a; Buffer.add_char buf ' '; term buf b;
      Buffer.add_char buf ')'

    | TIte (c, t, f) ->
      Buffer.add_string buf "(ite ";
      term buf c; Buffer.add_char buf ' ';
      term buf t; Buffer.add_char buf ' ';
      term buf f; Buffer.add_char buf ')'

    | TCtor (name, []) ->
      Buffer.add_string buf name

    | TCtor (name, args) ->
      Buffer.add_char   buf '(';
      Buffer.add_string buf name;
      List.iter (fun t -> Buffer.add_char buf ' '; term buf t) args;
      Buffer.add_char buf ')'

    | TMatch (scrut, branches) ->
      Buffer.add_string buf "(match ";
      term buf scrut;
      Buffer.add_string buf " (";
      List.iteri (fun i (ctor, vars, body) ->
        if i > 0 then Buffer.add_char buf ' ';
        Buffer.add_char buf '(';
        (if vars = [] then
          Buffer.add_string buf ctor
        else begin
          Buffer.add_char buf '(';
          Buffer.add_string buf ctor;
          List.iter (fun v -> Buffer.add_char buf ' '; Buffer.add_string buf v) vars;
          Buffer.add_char buf ')'
        end);
        Buffer.add_char buf ' ';
        term buf body;
        Buffer.add_char buf ')'
      ) branches;
      Buffer.add_string buf "))"

  (** Serialise a command to a string. *)
  let to_string pp_fn x =
    let buf = Buffer.create 64 in
    pp_fn buf x;
    Buffer.contents buf
end

(* ==================================================================== *)
(* Theory signature                                                     *)
(* ==================================================================== *)

(** Raised when a formula or type cannot be handled by the theory. *)
exception Unsupported of string

(** Operator classification tags returned by [trans_op]. *)
type op_tag = [
  | `Add | `Mul | `Opp     (** arithmetic: +, *, unary - *)
  | `Le  | `Lt  | `Ge | `Gt (** comparisons *)
  | `And | `Or  | `Not | `Imp (** boolean connectives *)
  | `Eq                       (** polymorphic equality *)
  | `True | `False            (** boolean constants *)
  | `Ite                      (** if-then-else *)
  | `Ctor of string           (** datatype constructor; carries SMTLib name *)
]

(** A theory determines:
    - which SMTLib2 logic to use ([logic_name])
    - how to translate EasyCrypt types to SMTLib sorts
    - how to classify EasyCrypt operator paths

    To extend to a new theory (e.g. QF_BV), implement this signature
    and pass it to [Make]. *)
module type Theory = sig
  val logic_name : string
  (** e.g. ["QF_NIA"], ["QF_BV"], ... *)

  val trans_ty : env -> ty -> sort
  (** Translate an EasyCrypt type to an SMTLib sort.
      Raises [Unsupported] if the type is not in the theory. *)

  val trans_op : env -> path -> op_tag
  (** Classify an EasyCrypt operator path.
      Raises [Unsupported] if the operator is not in the theory. *)
end

(* ==================================================================== *)
(* QFIA: Quantifier-Free Integer Arithmetic (QF_NIA)                   *)
(* ==================================================================== *)

module QFIA : Theory = struct
  let logic_name = "QF_NIA"

  let trans_ty _env ty =
    match ty.ty_node with
    | Tconstr (p, []) when p_equal p EcCoreLib.CI_Int.p_int   -> SInt
    | Tconstr (p, []) when p_equal p EcCoreLib.CI_Bool.p_bool -> SBool
    | _ ->
      raise (Unsupported (Printf.sprintf "type not in QF_NIA: %s"
        (match ty.ty_node with
         | Tconstr (p, _) -> EcPath.tostring p
         | Tvar tv        -> EcIdent.name tv
         | _              -> "<complex type>")))

  let trans_op _env p =
    let open EcCoreLib in
    if      p_equal p CI_Int.p_int_add  then `Add
    else if p_equal p CI_Int.p_int_opp  then `Opp
    else if p_equal p CI_Int.p_int_mul  then `Mul
    else if p_equal p CI_Int.p_int_le   then `Le
    else if p_equal p CI_Int.p_int_lt   then `Lt
    else if p_equal p CI_Bool.p_not     then `Not
    else if p_equal p CI_Bool.p_and     then `And
    else if p_equal p CI_Bool.p_anda    then `And
    else if p_equal p CI_Bool.p_or      then `Or
    else if p_equal p CI_Bool.p_ora     then `Or
    else if p_equal p CI_Bool.p_imp     then `Imp
    else if p_equal p CI_Bool.p_eq      then `Eq
    else if p_equal p CI_Bool.p_true    then `True
    else if p_equal p CI_Bool.p_false   then `False
    else raise (Unsupported (Printf.sprintf "operator not in QF_NIA: %s"
        (EcPath.tostring p)))
end

(* ==================================================================== *)
(* QF_DT: Quantifier-Free Datatypes (no arithmetic)                    *)
(* ==================================================================== *)

(** Pure algebraic-datatype theory.  Supports booleans and user-defined
    datatypes but no integer arithmetic.  Corresponds to the SMTLib2
    [QF_DT] logic. *)
module QF_DT : Theory = struct
  let logic_name = "QF_DT"

  let trans_ty env ty =
    match ty.ty_node with
    | Tconstr (p, []) when p_equal p EcCoreLib.CI_Bool.p_bool -> SBool
    | Tconstr (p, []) ->
      (match EcEnv.Ty.by_path_opt p env with
       | Some tydecl when EcDecl.tydecl_as_datatype tydecl <> None ->
         SCustom (EcPath.basename p)
       | _ ->
         raise (Unsupported (Printf.sprintf "type not in QF_DT: %s"
           (EcPath.tostring p))))
    | Tconstr (p, _) ->
      raise (Unsupported (Printf.sprintf
        "parameterised type not yet supported: %s" (EcPath.tostring p)))
    | Tvar tv ->
      raise (Unsupported (Printf.sprintf "type variable: %s" (EcIdent.name tv)))
    | _ ->
      raise (Unsupported "unsupported type in QF_DT")

  let trans_op env p =
    let open EcCoreLib in
    if      p_equal p CI_Bool.p_not   then `Not
    else if p_equal p CI_Bool.p_and   then `And
    else if p_equal p CI_Bool.p_anda  then `And
    else if p_equal p CI_Bool.p_or    then `Or
    else if p_equal p CI_Bool.p_ora   then `Or
    else if p_equal p CI_Bool.p_imp   then `Imp
    else if p_equal p CI_Bool.p_eq    then `Eq
    else if p_equal p CI_Bool.p_true  then `True
    else if p_equal p CI_Bool.p_false then `False
    else
      (* Check if p is a datatype constructor. *)
      (match EcEnv.Op.by_path_opt p env with
       | Some op when EcDecl.is_ctor op ->
         `Ctor (EcPath.basename p)
       | _ ->
         raise (Unsupported (Printf.sprintf "operator not in QF_DT: %s"
           (EcPath.tostring p))))
end

(* ==================================================================== *)
(* ALL: All theories (integers + datatypes + booleans)                  *)
(* ==================================================================== *)

(** Combination of integer arithmetic and algebraic datatypes.
    Corresponds to the SMTLib2 [ALL] logic, which Z3 and CVC5 both
    support for the combination of NIA and inductive datatypes. *)
module ALL : Theory = struct
  let logic_name = "ALL"

  let trans_ty env ty =
    match ty.ty_node with
    | Tconstr (p, []) when p_equal p EcCoreLib.CI_Int.p_int -> SInt
    | _ ->
      (* Delegate remaining types to QF_DT. *)
      (match QF_DT.trans_ty env ty with
       | s -> s
       | exception (Unsupported _) ->
         raise (Unsupported (Printf.sprintf "type not in ALL: %s"
           (match ty.ty_node with
            | Tconstr (p, _) -> EcPath.tostring p
            | Tvar tv        -> EcIdent.name tv
            | _              -> "<complex type>"))))

  let trans_op env p =
    (* Try integer arithmetic operators first. *)
    match QFIA.trans_op env p with
    | tag -> tag
    | exception (Unsupported _) ->
      (* Fall back to datatype/boolean operators. *)
      (match QF_DT.trans_op env p with
       | tag -> tag
       | exception (Unsupported _) ->
         raise (Unsupported (Printf.sprintf "operator not in ALL: %s"
           (EcPath.tostring p))))
end

(* ==================================================================== *)
(* Translator functor                                                   *)
(* ==================================================================== *)

module Make (T : Theory) = struct
  (** Translation environment.
      [vars] maps local EcIdent.t → SMTLib variable name.
      [ops]  maps opaque nullary operator paths → SMTLib constant name.
      Both kinds of names are declared as [(declare-const ...)] in the solver. *)
  type lenv = {
    vars : string Mid.t;
    ops  : string EcPath.Mp.t;
  }

  let empty_lenv : lenv = { vars = Mid.empty; ops = EcPath.Mp.empty }

  (** Sanitise an arbitrary string to a plain SMTLib symbol. *)
  let smtlib_sanitize s =
    String.map (fun c -> match c with
      | '\'' | '.' | '/' | '\\' | ' ' | '[' | ']' | '!' -> '_'
      | _ -> c) s

  (** Fresh name for a local variable (tag ensures uniqueness). *)
  let smtlib_name id =
    let safe = smtlib_sanitize (EcIdent.name id) in
    Printf.sprintf "%s_%d" safe (EcIdent.tag id)

  (** Fresh name for an opaque operator path. *)
  let smtlib_op_name p =
    "op_" ^ smtlib_sanitize (EcPath.tostring p)

  let add_var lenv id =
    let name = smtlib_name id in
    ({ lenv with vars = Mid.add id name lenv.vars }, name)

  let add_op lenv p =
    let name = smtlib_op_name p in
    ({ lenv with ops = EcPath.Mp.add p name lenv.ops }, name)

  (** Translate a type using the theory. *)
  let trans_ty env ty = T.trans_ty env ty

  (** Translate an EasyCrypt formula to an SMTLib term.
      Raises [Unsupported] for any construct outside the theory. *)
  let rec trans_form (env : env) (lenv : lenv) (f : form) : term =
    match f.f_node with
    | Fint n ->
      TInt n

    | Flocal id ->
      (match Mid.find_opt id lenv.vars with
       | Some name -> TVar name
       | None ->
         raise (Unsupported
           (Printf.sprintf "unbound local variable: %s" (EcIdent.name id))))

    | Fop (p, _tys) ->
      (* First check for theory-known nullary ops (true/false). *)
      (match T.trans_op env p with
       | `True  -> TBool true
       | `False -> TBool false
       | _ ->
         raise (Unsupported
           (Printf.sprintf "unsupported nullary operator: %s"
              (EcPath.tostring p)))
       | exception (Unsupported _) ->
         (* Not a theory operator — treat as an opaque declared constant. *)
         match EcPath.Mp.find_opt p lenv.ops with
         | Some name -> TVar name
         | None ->
           raise (Unsupported
             (Printf.sprintf "undeclared opaque operator: %s \
               (hint: use collect_ops before translating)"
                (EcPath.tostring p))))

    | Fapp ({f_node = Fop (p, _tys); _}, args) ->
      trans_app env lenv p args

    | Fif (c, t, e) ->
      TIte (trans_form env lenv c, trans_form env lenv t, trans_form env lenv e)

    | Fmatch (fb, branches, _result_ty) ->
      (* Determine the matched datatype from the scrutinee's type. *)
      let p, tydecl, _tvs =
        match EcEnv.Ty.get_top_decl fb.f_ty env with
        | Some x -> x
        | None   ->
          raise (Unsupported "cannot determine datatype for match scrutinee")
      in
      let dtype =
        match EcDecl.tydecl_as_datatype tydecl with
        | Some dt -> dt
        | None    ->
          raise (Unsupported (Printf.sprintf "match on non-datatype: %s"
            (EcPath.tostring p)))
      in
      let scrut = trans_form env lenv fb in
      let branches_with_ctors =
        List.combine branches dtype.EcDecl.tydt_ctors in
      let trans_branch (branch_form, (ctor_name, arg_types)) =
        let n = List.length arg_types in
        (* Each branch is stored as a lambda fun x1...xn -> body. *)
        let bds, body = EcFol.decompose_lambda branch_form in
        let ctor_bds, rest_bds = List.takedrop n bds in
        let body =
          if rest_bds = [] then body
          else EcFol.f_lambda rest_bds body
        in
        (* Extend the local environment with the constructor-bound variables. *)
        let lenv_inner, var_names =
          List.fold_left (fun (le, ns) (id, _gty) ->
            let (le', name) = add_var le id in
            (le', ns @ [name])
          ) (lenv, []) ctor_bds
        in
        let body_term = trans_form env lenv_inner body in
        (ctor_name, var_names, body_term)
      in
      TMatch (scrut, List.map trans_branch branches_with_ctors)

    | Fquant _ ->
      raise (Unsupported "quantifiers are not supported in QF_NIA")

    | Flet _ ->
      raise (Unsupported "let-bindings are not yet supported")

    | _ ->
      raise (Unsupported (Printf.sprintf
        "unsupported formula node (type: %s)"
        (match f.f_ty.ty_node with
          | Tconstr (p, _) -> EcPath.tostring p
          | _ -> "<complex type>")))

  and trans_app (env : env) (lenv : lenv) (p : path) (args : form list) : term =
    (* Classify the operator *)
    let tag = T.trans_op env p in
    match tag, args with
    (* Arithmetic *)
    | `Add, [a; b] ->
      TAdd [trans_form env lenv a; trans_form env lenv b]
    | `Add, _ ->
      TAdd (List.map (trans_form env lenv) args)
    | `Opp, [a] ->
      TNeg (trans_form env lenv a)
    | `Mul, [a; b] ->
      TMul (trans_form env lenv a, trans_form env lenv b)
    (* Comparisons *)
    | `Le, [a; b] -> TLe (trans_form env lenv a, trans_form env lenv b)
    | `Lt, [a; b] -> TLt (trans_form env lenv a, trans_form env lenv b)
    | `Ge, [a; b] -> TGe (trans_form env lenv a, trans_form env lenv b)
    | `Gt, [a; b] -> TGt (trans_form env lenv a, trans_form env lenv b)
    (* Boolean connectives *)
    | `And, [a; b] ->
      TAnd [trans_form env lenv a; trans_form env lenv b]
    | `And, _ ->
      TAnd (List.map (trans_form env lenv) args)
    | `Or, [a; b] ->
      TOr [trans_form env lenv a; trans_form env lenv b]
    | `Or, _ ->
      TOr (List.map (trans_form env lenv) args)
    | `Not, [a] ->
      TNot (trans_form env lenv a)
    | `Imp, [a; b] ->
      TImpl (trans_form env lenv a, trans_form env lenv b)
    (* Equality: check that the argument type is supported *)
    | `Eq, [a; b] ->
      (* Verify the type is in the theory (raises Unsupported if not). *)
      ignore (T.trans_ty env a.f_ty);
      TEq (trans_form env lenv a, trans_form env lenv b)
    (* Constants used as functions (shouldn't happen, but be safe) *)
    | `True,  [] -> TBool true
    | `False, [] -> TBool false
    (* Ite *)
    | `Ite, [c; t; f] ->
      TIte (trans_form env lenv c, trans_form env lenv t, trans_form env lenv f)
    (* Datatype constructor *)
    | `Ctor name, args ->
      TCtor (name, List.map (trans_form env lenv) args)
    | _, _ ->
      raise (Unsupported (Printf.sprintf
        "operator %s applied to wrong number of arguments (%d)"
        (EcPath.tostring p) (List.length args)))

  (** Collect all free local variables (Flocal) in a formula.
      Returns [(ident, ty, sort)] for each local whose type is in the theory. *)
  let collect_locals env f =
    let seen = ref Mid.empty in
    let acc  = ref [] in
    let rec walk f =
      match f.f_node with
      | Flocal id ->
        if not (Mid.mem id !seen) then begin
          seen := Mid.add id () !seen;
          acc  := (id, f.f_ty) :: !acc
        end
      | Fapp (g, args)     -> walk g; List.iter walk args
      | Fif  (c, t, e)     -> walk c; walk t; walk e
      | Fmatch (fb, bs, _) -> walk fb; List.iter walk bs
      | Fop _ | Fint _ -> ()
      | _ -> ()
    in
    walk f;
    List.filter_map (fun (id, ty) ->
      match T.trans_ty env ty with
      | s -> Some (id, ty, s)
      | exception (Unsupported _) -> None
    ) (List.rev !acc)

  (** Collect all opaque nullary operators (Fop with no args) in a formula
      whose return type is supported by the theory and which are not already
      handled as theory primitives (e.g. [true], [false]).
      Returns [(path, sort)] in order of first occurrence.
      These must be declared as SMTLib constants before translating. *)
  let collect_ops env f =
    let seen = ref EcPath.Mp.empty in
    let acc  = ref [] in
    let rec walk f =
      match f.f_node with
      | Fop (p, _) ->
        if not (EcPath.Mp.mem p !seen) then begin
          (* Skip operators the theory already knows how to handle *)
          match T.trans_op env p with
          | _ -> ()
          | exception (Unsupported _) ->
            (* Unknown op — include if its type is in the theory *)
            (match T.trans_ty env f.f_ty with
             | s ->
               seen := EcPath.Mp.add p () !seen;
               acc  := (p, s) :: !acc
             | exception (Unsupported _) -> ())
        end
      | Fapp (g, args)      -> walk g; List.iter walk args
      | Fif  (c, t, e)      -> walk c; walk t; walk e
      | Fmatch (fb, bs, _)  -> walk fb; List.iter walk bs
      | Flocal _ | Fint _   -> ()
      | _ -> ()
    in
    walk f;
    List.rev !acc

  (** Collect all algebraic datatypes that appear in a formula (by type),
      in order of first occurrence.  Returns [(type_path, ty_dtype, type_args)]
      for each distinct datatype encountered.
      The list is topologically sorted: a type used as a field type appears
      before the type that contains it (because we walk field types
      recursively before recording the parent). *)
  let collect_datatypes env f =
    let seen = ref EcPath.Sp.empty in
    let acc  = ref [] in
    let rec walk_ty ty =
      match ty.ty_node with
      | Tconstr (p, targs) ->
        if not (EcPath.Sp.mem p !seen) then begin
          (* Mark early to break cycles. *)
          seen := EcPath.Sp.add p !seen;
          (match EcEnv.Ty.by_path_opt p env with
           | Some tydecl ->
             (match EcDecl.tydecl_as_datatype tydecl with
              | Some dtype ->
                (* Walk field types first for correct declaration order. *)
                List.iter (fun (_cname, field_tys) ->
                  List.iter walk_ty field_tys
                ) dtype.EcDecl.tydt_ctors;
                acc := (p, dtype) :: !acc
              | None -> ())
           | None -> ())
        end;
        List.iter walk_ty targs
      | _ -> ()
    in
    let rec walk_form f =
      walk_ty f.f_ty;
      match f.f_node with
      | Fmatch (fb, bs, rty) ->
        walk_ty rty; walk_form fb; List.iter walk_form bs
      | Fapp (g, args)     -> walk_form g; List.iter walk_form args
      | Fif  (c, t, e)     -> walk_form c; walk_form t; walk_form e
      | Flocal _ | Fint _ | Fop _ -> ()
      | _ -> ()
    in
    walk_form f;
    List.rev !acc
end

(* ==================================================================== *)
(* Solver interface                                                     *)
(* ==================================================================== *)

(** Abstract interface for an incremental SMT solver session.
    Implementations may use:
    - direct OCaml bindings to the solver library (zero serialisation cost)
    - a subprocess communicating via the SMTLib2 text protocol
    Callers work exclusively through this interface. *)
module type Solver = sig
  type t

  val create        : ?timeout:int -> unit -> t
  (** Start a new solver session, optionally with a timeout in seconds. *)

  val set_logic     : t -> string -> unit
  (** [set_logic s logic] emits [(set-logic logic)]. *)

  val declare_const : t -> string -> sort -> unit
  (** [declare_const s name sort] declares an uninterpreted constant. *)

  val assert_       : t -> term -> unit
  (** Assert a formula into the current scope. *)

  val push          : t -> unit
  (** Push a scope frame (for incremental mode). *)

  val pop           : t -> unit
  (** Pop the top scope frame. *)

  val check_sat     : t -> [`Sat | `Unsat | `Unknown]
  (** Check satisfiability of the current assertion set. *)

  val get_model     : t -> model
  (** Retrieve a satisfying model.  Only valid after [check_sat] returns
      [`Sat].  Raises [Failure] if the solver cannot produce a model. *)

  val declare_datatype : t -> string -> (string * (string * sort) list) list -> unit
  (** [declare_datatype s name ctors] emits a [(declare-datatype)] command.
      [ctors] is a list of [(constructor_name, [(field_name, sort)])] pairs. *)

  val close         : t -> unit
  (** Close the solver session and release resources. *)
end

(* ==================================================================== *)
(* Text-process solver bridge                                           *)
(* ==================================================================== *)

(** Configuration for a text-based (stdin/stdout) solver backend.
    For solvers with OCaml bindings, implement [Solver] directly instead. *)
module type Text_Backend = sig
  val name       : string
  (** Human-readable solver name used in error messages. *)

  val binary     : string
  (** Executable name looked up in PATH (e.g. ["z3"], ["cvc5"]). *)

  val extra_args : string list
  (** Extra command-line arguments for the binary.
      These must put the solver into incremental SMTLib2 stdin mode.
      Example: Z3 uses [["-in"]], CVC5 uses [["--lang=smt2";"--incremental"]]. *)
end

(** Minimal S-expression parser used to extract models from [(get-model)]
    responses. *)
module Sexpr = struct
  type t =
    | Atom of string
    | List of t list

  exception Parse_error of string

  let of_string s =
    let n   = String.length s in
    let pos = ref 0 in

    let skip_ws () =
      while !pos < n && (s.[!pos] = ' ' || s.[!pos] = '\t'
                         || s.[!pos] = '\n' || s.[!pos] = '\r') do
        incr pos
      done
    in

    let read_atom () =
      let start = !pos in
      while !pos < n && s.[!pos] <> '(' && s.[!pos] <> ')'
            && s.[!pos] <> ' ' && s.[!pos] <> '\t'
            && s.[!pos] <> '\n' && s.[!pos] <> '\r' do
        incr pos
      done;
      String.sub s start (!pos - start)
    in

    let rec read () =
      skip_ws ();
      if !pos >= n then raise (Parse_error "unexpected end of input");
      match s.[!pos] with
      | '(' ->
        incr pos;
        let children = ref [] in
        skip_ws ();
        while !pos < n && s.[!pos] <> ')' do
          children := read () :: !children;
          skip_ws ()
        done;
        if !pos >= n then raise (Parse_error "unclosed '('");
        incr pos;
        List (List.rev !children)
      | ')' ->
        raise (Parse_error "unexpected ')'")
      | _ ->
        let a = read_atom () in
        Atom a
    in

    read ()
end

(** Extract model bindings from a [(get-model)] S-expression response.
    Z3 and CVC5 both return something like:
    {[(model (define-fun x () Int 42) ...)]} *)
let parse_model (response : string) : model =
  (* Collect lines until we have balanced parentheses *)
  let extract_value (sexp : Sexpr.t) : term option =
    match sexp with
    | Sexpr.Atom s ->
      (try Some (TInt (BI.of_string s))
       with _ ->
         if s = "true"  then Some (TBool true)
         else if s = "false" then Some (TBool false)
         else Some (TVar s))
    | Sexpr.List [Sexpr.Atom "-"; Sexpr.Atom n] ->
      (try Some (TInt (BI.neg (BI.of_string n)))
       with _ -> None)
    | _ -> None
  in
  match Sexpr.of_string (String.trim response) with
  | Sexpr.List (Sexpr.Atom "model" :: defs)
  | Sexpr.List defs ->
    List.filter_map (function
      | Sexpr.List [Sexpr.Atom "define-fun";
                    Sexpr.Atom name;
                    Sexpr.List [];   (* no arguments = constant *)
                    _;               (* sort *)
                    value] ->
        (match extract_value value with
         | Some v -> Some (name, v)
         | None   -> None)
      | _ -> None
    ) defs
  | _ | exception _ -> []

(** Find an executable in PATH. *)
let find_in_path binary =
  match Sys.getenv_opt "PATH" with
  | None -> None
  | Some path ->
    let dirs = String.split_on_char ':' path in
    List.fold_left (fun acc dir ->
      match acc with
      | Some _ -> acc
      | None ->
        let full = Filename.concat dir binary in
        if Sys.file_exists full then Some full else None
    ) None dirs

(** [Make_Text_Process(B)] creates a [Solver] implementation that:
    - spawns [B.binary] as a persistent child process
    - communicates via SMTLib2 text over stdin/stdout
    - supports incremental mode via [(push)] and [(pop)]
    - implements [get_model] by parsing [(get-model)] output

    To add a solver with native OCaml bindings, implement [Solver]
    directly instead of using this functor. *)
module Make_Text_Process (B : Text_Backend) : Solver = struct
  type t = {
    mutable ic   : in_channel;
    mutable oc   : out_channel;
    timeout      : int;
    mutable open_ : bool;
  }

  let send t s =
    if not t.open_ then failwith (B.name ^ ": solver session is closed");
    output_string t.oc s;
    output_char   t.oc '\n';
    flush t.oc

  let recv_line t =
    input_line t.ic

  (** Read lines from the solver until we have a complete S-expression
      (balanced parentheses), then return the whole block as a string. *)
  let recv_sexp t =
    let buf    = Buffer.create 256 in
    let depth  = ref 0 in
    let first  = ref true in
    let done_  = ref false in
    while not !done_ do
      let line = recv_line t in
      let line = String.trim line in
      if line = "" then ()
      else begin
        if not !first then Buffer.add_char buf '\n';
        first := false;
        Buffer.add_string buf line;
        String.iter (function
          | '(' -> incr depth
          | ')' -> decr depth
          | _   -> ()) line;
        if !depth <= 0 then done_ := true
      end
    done;
    Buffer.contents buf

  let create ?(timeout = 30) () =
    let binary =
      match find_in_path B.binary with
      | Some p -> p
      | None   ->
        failwith (Printf.sprintf
          "smtlib: solver '%s' not found in PATH; please install %s"
          B.binary B.name)
    in
    let args = Array.of_list (B.binary :: B.extra_args) in
    let ic, oc = Unix.open_process_args binary args in
    { ic; oc; timeout; open_ = true }

  let set_logic t logic =
    send t (Printf.sprintf "(set-logic %s)" logic)

  let declare_const t name sort =
    let buf = Buffer.create 32 in
    Buffer.add_string buf "(declare-const ";
    Buffer.add_string buf name;
    Buffer.add_char   buf ' ';
    PP.sort buf sort;
    Buffer.add_char   buf ')';
    send t (Buffer.contents buf)

  let assert_ t term =
    let buf = Buffer.create 64 in
    Buffer.add_string buf "(assert ";
    PP.term buf term;
    Buffer.add_char   buf ')';
    send t (Buffer.contents buf)

  let push t =
    send t "(push 1)"

  let pop t =
    send t "(pop 1)"

  let check_sat t =
    send t (Printf.sprintf "(set-option :timeout %d000)" t.timeout);
    send t "(check-sat)";
    let response = recv_line t in
    match String.trim response with
    | "unsat"   -> `Unsat
    | "sat"     -> `Sat
    | "unknown" -> `Unknown
    | other     ->
      `Unknown  (* treat unexpected response as unknown *)
    [@@warning "-8"]

  let declare_datatype t name ctors =
    let buf = Buffer.create 64 in
    Buffer.add_string buf "(declare-datatype ";
    Buffer.add_string buf name;
    Buffer.add_string buf " (";
    List.iter (fun (ctor_name, fields) ->
      Buffer.add_char buf '(';
      Buffer.add_string buf ctor_name;
      List.iter (fun (field_name, sort) ->
        Buffer.add_string buf " (";
        Buffer.add_string buf field_name;
        Buffer.add_char   buf ' ';
        PP.sort buf sort;
        Buffer.add_char   buf ')'
      ) fields;
      Buffer.add_char buf ')'
    ) ctors;
    Buffer.add_string buf "))";
    send t (Buffer.contents buf)

  let get_model t =
    send t "(get-model)";
    let response = recv_sexp t in
    parse_model response

  let close t =
    if t.open_ then begin
      (try send t "(exit)" with _ -> ());
      (try ignore (Unix.close_process (t.ic, t.oc)) with _ -> ());
      t.open_ <- false
    end
end

(* ==================================================================== *)
(* Concrete solver backends                                             *)
(* ==================================================================== *)

(** Z3 text-based backend.
    Z3 supports incremental mode via the [-in] flag. *)
module Z3_Text_Backend : Text_Backend = struct
  let name       = "Z3"
  let binary     = "z3"
  let extra_args = ["-in"]
end

(** CVC5 text-based backend.
    CVC5 requires explicit language and incremental flags. *)
module CVC5_Text_Backend : Text_Backend = struct
  let name       = "CVC5"
  let binary     = "cvc5"
  let extra_args = ["--lang=smt2"; "--incremental"]
end

module Z3_Text   = Make_Text_Process(Z3_Text_Backend)
module CVC5_Text = Make_Text_Process(CVC5_Text_Backend)

(** To add a native OCaml-binding backend (e.g. using the [z3] opam package),
    implement the [Solver] module type directly:

    {[
      module Z3_Native : Solver = struct
        type t = { ctx : Z3.context; solver : Z3.Solver.solver; ... }
        let create ?timeout () = ...
        let assert_ t term = ... (* translate term to Z3.Expr.expr *)
        let check_sat t = ...
        let get_model t = ...
        ...
      end
    ]}

    Then add [z3] (or [cvc5]) to the [libraries] stanza in [src/dune]
    and select the native module in [check] below. *)

(* ==================================================================== *)
(* Solver selection                                                     *)
(* ==================================================================== *)

type solver_instance =
  | Z3   of Z3_Text.t
  | CVC5 of CVC5_Text.t

(** Wrapper that hides the sum type behind a uniform interface. *)
module SI = struct
  type t = solver_instance

  let dispatch (type a) (z3 : Z3_Text.t -> a) (cvc5 : CVC5_Text.t -> a) = function
    | Z3   s -> z3   s
    | CVC5 s -> cvc5 s

  let create ?timeout name =
    match String.lowercase_ascii name with
    | "z3"   -> Z3   (Z3_Text.create   ?timeout ())
    | "cvc5" -> CVC5 (CVC5_Text.create ?timeout ())
    | other  ->
      failwith (Printf.sprintf "smtlib: unknown solver '%s'" other)

  let set_logic     t l   = dispatch (fun s -> Z3_Text.set_logic   s l)
                                     (fun s -> CVC5_Text.set_logic  s l) t
  let declare_const t n s = dispatch (fun s' -> Z3_Text.declare_const s' n s)
                                     (fun s' -> CVC5_Text.declare_const s' n s) t
  let assert_       t f   = dispatch (fun s -> Z3_Text.assert_      s f)
                                     (fun s -> CVC5_Text.assert_    s f) t
  let push          t     = dispatch  Z3_Text.push   CVC5_Text.push  t
  let pop           t     = dispatch  Z3_Text.pop    CVC5_Text.pop   t
  let check_sat     t     = dispatch  Z3_Text.check_sat CVC5_Text.check_sat t
  let get_model     t     = dispatch  Z3_Text.get_model CVC5_Text.get_model t
  let declare_datatype t name ctors =
    dispatch (fun s -> Z3_Text.declare_datatype   s name ctors)
             (fun s -> CVC5_Text.declare_datatype  s name ctors) t
  let close         t     = dispatch  Z3_Text.close  CVC5_Text.close t
end

(* ==================================================================== *)
(* Top-level check function                                             *)
(* ==================================================================== *)

module Trans = Make(ALL)

(** Default prover priority list. *)
let default_provers = ["z3"; "cvc5"]

(** Format a model for display. *)
let pp_model (model : model) : string =
  if model = [] then "(empty model)"
  else
    let buf = Buffer.create 64 in
    List.iter (fun (name, value) ->
      Buffer.add_string buf "  ";
      Buffer.add_string buf name;
      Buffer.add_string buf " = ";
      PP.term buf value;
      Buffer.add_char buf '\n'
    ) model;
    Buffer.contents buf

(** [check ~notify pi env hyps concl] attempts to prove [concl] under
    [hyps] using a direct SMTLib2 connection.

    Returns [true] if the goal is proved (solver returned [unsat] for
    the negation).  Returns [false] otherwise.  If the solver returns
    [sat], a counterexample model is displayed via [notify]. *)
let check
    ~(notify   : EcGState.loglevel -> string lazy_t -> unit)
    (pi        : EcProvers.prover_infos)
    (hyps      : LDecl.hyps)
    (concl     : form)
  : bool
=
  let env  = LDecl.toenv hyps in
  let hyps = LDecl.tohyps hyps in

  (* Pick a solver: first name in pi.pr_provers that we recognise *)
  let solver_name =
    let names =
      match pi.EcProvers.pr_provers with
      | [] -> default_provers
      | ns -> ns
    in
    (* Return first recognised name, fall back to "z3" *)
    List.find_opt (fun n ->
      match String.lowercase_ascii n with
      | "z3" | "cvc5" -> true
      | _ -> false
    ) names
    |> Option.value ~default:"z3"
  in

  let timeout = pi.EcProvers.pr_timelimit in

  (* Attempt the translation; if anything is Unsupported, propagate. *)
  let prove () =
    let solver = SI.create ~timeout solver_name in
    EcUtils.try_finally (fun () ->
      SI.set_logic solver ALL.logic_name;

      (* Gather all formulas that will be translated. *)
      let lenv = ref Trans.empty_lenv in
      let all_forms =
        let hyp_forms = List.filter_map (fun (_, lk) ->
          match lk with
          | EcBaseLogic.LD_hyp f -> Some f
          | _ -> None
        ) hyps.EcBaseLogic.h_local
        in
        hyp_forms @ [concl]
      in

      (* Collect all free locals across all formulas and declare them. *)
      let all_locals =
        let seen = ref EcIdent.Mid.empty in
        let acc  = ref [] in
        List.iter (fun f ->
          let ls = Trans.collect_locals env f in
          List.iter (fun (id, ty, sort) ->
            if not (EcIdent.Mid.mem id !seen) then begin
              seen := EcIdent.Mid.add id () !seen;
              acc  := (id, ty, sort) :: !acc
            end
          ) ls
        ) all_forms;
        List.rev !acc
      in
      List.iter (fun (id, _ty, sort) ->
        let (new_lenv, name) = Trans.add_var !lenv id in
        lenv := new_lenv;
        SI.declare_const solver name sort
      ) all_locals;

      (* Collect all opaque nullary operators (e.g. [op c : int]) and
         declare them as SMTLib constants so trans_form can look them up. *)
      let all_ops =
        let seen = ref EcPath.Mp.empty in
        let acc  = ref [] in
        List.iter (fun f ->
          let ops = Trans.collect_ops env f in
          List.iter (fun (p, sort) ->
            if not (EcPath.Mp.mem p !seen) then begin
              seen := EcPath.Mp.add p () !seen;
              acc  := (p, sort) :: !acc
            end
          ) ops
        ) all_forms;
        List.rev !acc
      in
      List.iter (fun (p, sort) ->
        let (new_lenv, name) = Trans.add_op !lenv p in
        lenv := new_lenv;
        SI.declare_const solver name sort
      ) all_ops;

      (* Collect all algebraic datatypes appearing in formula types and
         declare them to the solver.  Must happen before any assert_
         that references those types. *)
      let all_datatypes =
        let seen = ref EcPath.Sp.empty in
        let acc  = ref [] in
        List.iter (fun f ->
          let dts = Trans.collect_datatypes env f in
          List.iter (fun (p, dtype) ->
            if not (EcPath.Sp.mem p !seen) then begin
              seen := EcPath.Sp.add p !seen;
              acc  := (p, dtype) :: !acc
            end
          ) dts
        ) all_forms;
        List.rev !acc
      in
      List.iter (fun (_p, dtype) ->
        let dt_name = EcPath.basename _p in
        let ctors = List.map (fun (ctor_name, field_tys) ->
          let fields = List.mapi (fun i fty ->
            let sort =
              (match ALL.trans_ty env fty with
               | s -> s
               | exception (Unsupported _) -> SCustom "Unknown")
            in
            (Printf.sprintf "%s_field%d" ctor_name i, sort)
          ) field_tys in
          (ctor_name, fields)
        ) dtype.EcDecl.tydt_ctors in
        SI.declare_datatype solver dt_name ctors
      ) all_datatypes;

      (* Assert all local hypotheses. *)
      List.iter (fun (_, lk) ->
        match lk with
        | EcBaseLogic.LD_hyp f ->
          (match Trans.trans_form env !lenv f with
           | t -> SI.assert_ solver t
           | exception (Unsupported _) ->
             (* Skip hypotheses we cannot translate; conservative but safe. *)
             ())
        | _ -> ()
      ) hyps.EcBaseLogic.h_local;

      (* Assert globally wanted lemmas (from smtlib(lemma1 lemma2) arguments).
         [pi.pr_wanted] contains the paths the user explicitly named.
         We iterate all environment axioms and assert those that match.
         Lemmas with untranslatable types/operators are silently skipped. *)
      let assert_global_lemma p (ax : EcDecl.axiom) =
        if EcProvers.Hints.mem p pi.EcProvers.pr_wanted then begin
          let spec = ax.EcDecl.ax_spec in
          (* Declare any free locals in the lemma (usually none for closed lemmas). *)
          let ax_locals = Trans.collect_locals env spec in
          List.iter (fun (id, _ty, sort) ->
            if not (Mid.mem id !lenv.vars) then begin
              let (new_lenv, name) = Trans.add_var !lenv id in
              lenv := new_lenv;
              SI.declare_const solver name sort
            end
          ) ax_locals;
          (* Declare any opaque ops appearing in the lemma. *)
          let ax_ops = Trans.collect_ops env spec in
          List.iter (fun (op_p, sort) ->
            if not (EcPath.Mp.mem op_p !lenv.ops) then begin
              let (new_lenv, name) = Trans.add_op !lenv op_p in
              lenv := new_lenv;
              SI.declare_const solver name sort
            end
          ) ax_ops;
          match Trans.trans_form env !lenv ax.EcDecl.ax_spec with
          | t -> SI.assert_ solver t
          | exception (Unsupported _) -> ()
        end
      in
      EcEnv.Ax.iter assert_global_lemma env;

      (* Assert the negation of the conclusion. *)
      let concl_term = Trans.trans_form env !lenv concl in
      SI.assert_ solver (TNot concl_term);

      (* Query the solver. *)
      match SI.check_sat solver with
      | `Unsat  -> true
      | `Unknown ->
        notify `Warning (lazy "smtlib: solver returned 'unknown'");
        false
      | `Sat ->
        (* Retrieve and display a counterexample model. *)
        let model =
          (try SI.get_model solver
           with _ -> [])
        in
        notify `Warning (lazy (Printf.sprintf
          "smtlib: goal is falsifiable%s"
          (if model = [] then ""
           else Printf.sprintf ";\ncounterexample:\n%s" (pp_model model))));
        false
    ) (fun () -> SI.close solver)
  in

  match prove () with
  | result -> result
  | exception (Unsupported msg) ->
    notify `Warning (lazy (Printf.sprintf
      "smtlib: cannot translate goal: %s" msg));
    false
  | exception Failure msg ->
    notify `Warning (lazy msg);
    false
