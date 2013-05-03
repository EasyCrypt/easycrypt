(* -------------------------------------------------------------------- *)
open EcUtils
open EcSymbols
open EcLocation
open EcParsetree
open EcTyping
open EcOptions
open EcLogic
open EcPrinting
open EcPrinting.Pp

(* -------------------------------------------------------------------- *)
exception TopError of EcLocation.t * exn

let rec toperror_of_exn exn =
  match exn with
  | TopError (loc, e)    -> Some (loc, e)
  | TyError  (loc, _, _) -> Some (loc, exn)
  | TacError _           -> Some (_dummy, exn)
  | ParseError (loc, _)  -> Some (loc, exn)
  | LocError (loc, e)    -> begin
      match toperror_of_exn e with
      | None -> Some (loc, e)
      | Some (loc, e) -> Some (loc, e)
    end
  | _ -> None

let toperror_of_exn exn =
  match toperror_of_exn exn with
  | Some (loc, exn) -> TopError (loc, exn)
  | None            -> exn

let pp_toperror fmt loc exn =
  Format.fprintf fmt "%s: %a"
    (EcLocation.tostring loc)
    EcPException.exn_printer exn

let () =
  let pp fmt exn =
    match exn with
    | TopError (loc, exn) -> pp_toperror fmt loc exn
    | _ -> raise exn
  in
    EcPException.register pp

(* -------------------------------------------------------------------- *)
let loader = EcLoader.create ()

(* -------------------------------------------------------------------- *)
let process_pr scope p = 
  let env = EcScope.env scope in
  match p with 
  | Pr_ty qs ->
      let (x, ty) = EcEnv.Ty.lookup qs.pl_desc env in
      EcPrinting.pr_typedecl (EcPrinting.empty env) (x, ty)
        
  | Pr_op qs | Pr_pr qs ->
      let (x, op) = EcEnv.Op.lookup qs.pl_desc env in
      EcPrinting.pr_opdecl (EcPrinting.empty env) (x, op)
        
  | Pr_th qs ->
      let (p, th) = EcEnv.Theory.lookup qs.pl_desc env in
      EcPrinting.pr_theory (EcPrinting.empty env) (p, th)
  | Pr_ax qs ->
      let (p, ax) = EcEnv.Ax.lookup qs.pl_desc env in
      EcPrinting.pr_axiom (EcPrinting.empty env) (p, ax)

let process_print scope p = 
  let doc = process_pr scope p in
    EcPrinting.pretty stdout (doc ^^ Pp.hardline)

(* -------------------------------------------------------------------- *)
let addidir (idir : string) =
  EcLoader.addidir idir loader

(* -------------------------------------------------------------------- *)
type notifier = string -> unit

let default_notifier msg =
  Format.eprintf "%s\n%!" msg

let _notifier = ref (default_notifier : notifier)

let set_notifier (n : notifier) = _notifier := n
let get_notifier () = !_notifier

let notify scope msg =
  Format.ksprintf
    (fun msg ->
      if EcScope.verbose scope then !_notifier msg)
    msg

(* -------------------------------------------------------------------- *)
let rec process_type (scope : EcScope.scope) (tyd : ptydecl located) =
  let tyname = (tyd.pl_desc.pty_tyvars, tyd.pl_desc.pty_name) in
  let scope = 
    match tyd.pl_desc.pty_body with
    | None    -> EcScope.Ty.add    scope (mk_loc tyd.pl_loc tyname)
    | Some bd -> EcScope.Ty.define scope (mk_loc tyd.pl_loc tyname) bd
  in
    notify scope "added type: `%s'" (unloc tyd.pl_desc.pty_name);
    scope
  
(* -------------------------------------------------------------------- *)
and process_datatype (_scope : EcScope.scope) _ =
  failwith "not-implemented-yet"

(* -------------------------------------------------------------------- *)
and process_module (scope : EcScope.scope) (x, m) =
  EcScope.Mod.add scope x.pl_desc m

(* -------------------------------------------------------------------- *)
and process_interface (scope : EcScope.scope) (x, i) =
  EcScope.ModType.add scope x.pl_desc i

(* -------------------------------------------------------------------- *)
and process_operator (scope : EcScope.scope) (op : poperator located) =
  let scope = EcScope.Op.add scope op in
    notify scope "added operator: `%s'" (unloc op.pl_desc.po_name);
    scope

(* -------------------------------------------------------------------- *)
and process_predicate (scope : EcScope.scope) (p : ppredicate located) =
  let scope = EcScope.Pred.add scope p in
    notify scope "added predicate: `%s'" (unloc p.pl_desc.pp_name);
    scope

(* -------------------------------------------------------------------- *)
and process_axiom (scope : EcScope.scope) (ax : paxiom) =
  let (name, scope) = EcScope.Ax.add scope ax in
    EcUtils.oiter name
      (fun x -> notify scope "added axiom: `%s'" x);
    scope

(* -------------------------------------------------------------------- *)
and process_claim (scope : EcScope.scope) _ =
  scope

(* -------------------------------------------------------------------- *)
and process_th_open (scope : EcScope.scope) name =
  EcScope.Theory.enter scope name

(* -------------------------------------------------------------------- *)
and process_th_close (scope : EcScope.scope) name =
  if (EcScope.name scope) <> name then
    failwith "invalid theory name";     (* FIXME *)
  snd (EcScope.Theory.exit scope)

(* -------------------------------------------------------------------- *)
and process_th_require (scope : EcScope.scope) (x,io) = 
  let name  = x.pl_desc in
    match EcLoader.locate name loader with
    | None ->
        failwith ("cannot locate: " ^ name) (* FIXME *)

    | Some filename ->
        let loader iscope =
          let commands = EcIo.parseall (EcIo.from_file filename) in
            List.fold_left process_internal iscope commands in 
        let scope = EcScope.Theory.require scope name loader in
          match io with
          | None       -> scope
          | Some true  -> process_th_export scope ([], name)
          | Some false -> process_th_import scope ([], name)

(* -------------------------------------------------------------------- *)
and process_th_import (scope : EcScope.scope) name =
  EcScope.Theory.import scope name

(* -------------------------------------------------------------------- *)
and process_th_export (scope : EcScope.scope) name =
  EcScope.Theory.export scope name

(* -------------------------------------------------------------------- *)
and process_th_clone (scope : EcScope.scope) thcl =
  EcScope.Theory.clone scope thcl

(* -------------------------------------------------------------------- *)
and process_w3_import (scope : EcScope.scope) (p, f, r) =
  EcScope.Theory.import_w3 scope p f r

(* -------------------------------------------------------------------- *)
and process_tactics (scope : EcScope.scope) t = 
  EcScope.Tactic.process scope t

(* -------------------------------------------------------------------- *)
and process_save (scope : EcScope.scope) loc =
  let (name, scope) = EcScope.Ax.save scope loc in
    EcUtils.oiter name
      (fun x -> notify scope "added axiom: `%s'" x);
    scope

(* -------------------------------------------------------------------- *)
and process_proverinfo scope pi = 
  let scope = EcScope.Prover.process scope pi in
    scope

(* -------------------------------------------------------------------- *)
and process_checkproof scope b = 
  let scope = EcScope.Prover.check_proof scope b in
    scope

(* -------------------------------------------------------------------- *)
and process (scope : EcScope.scope) (g : global located) =
  let loc = g.pl_loc in

  let scope =
    match g.pl_desc with
    | Gtype      t    -> process_type       scope (mk_loc loc t)
    | Gdatatype  t    -> process_datatype   scope (mk_loc loc t)
    | Gmodule    m    -> process_module     scope m
    | Ginterface i    -> process_interface  scope i
    | Goperator  o    -> process_operator   scope (mk_loc loc o)
    | Gpredicate p    -> process_predicate  scope (mk_loc loc p)
    | Gaxiom     a    -> process_axiom      scope a
    | Gclaim     c    -> process_claim      scope c
    | GthOpen    name -> process_th_open    scope name.pl_desc
    | GthClose   name -> process_th_close   scope name.pl_desc
    | GthRequire name -> process_th_require scope name
    | GthImport  name -> process_th_import  scope name.pl_desc
    | GthExport  name -> process_th_export  scope name.pl_desc
    | GthClone   thcl -> process_th_clone   scope thcl
    | GthW3      a    -> process_w3_import  scope a
    | Gprint     p    -> process_print      scope p; scope
    | Gtactics   t    -> process_tactics    scope t
    | Gprover_info pi -> process_proverinfo scope pi
    | Gcheckproof b   -> process_checkproof scope b
    | Gsave      loc  -> process_save       scope loc
  in
    scope

(* -------------------------------------------------------------------- *)
and process_internal (scope : EcScope.scope) (g : global located) =
  process scope g

(* -------------------------------------------------------------------- *)
let context = ref (0, EcScope.empty, [])

(* -------------------------------------------------------------------- *)
let current () =
  let (_, scope, _) = !context in scope

(* -------------------------------------------------------------------- *)
let full_check b max_provers provers =
  let (idx,scope,l) = !context in
  assert (idx = 0 && l = []);  
  let scope = EcScope.Prover.set_default scope max_provers provers in
  let scope = 
    if b then EcScope.Prover.full_check scope 
    else scope in
  context := (idx, scope, l)

(* -------------------------------------------------------------------- *)
let uuid () : int =
  let (idx, _, _) = !context in idx

(* -------------------------------------------------------------------- *)
let undo (olduuid : int) =
  if olduuid < (uuid ()) then
    begin
      for i = (uuid ()) - 1 downto olduuid do
        let (_, _scope, stack) = !context in
        context := (i, List.hd stack, List.tl stack)
      done
    end

(* -------------------------------------------------------------------- *)
let process (g : global located) =
  let (idx, scope, stack) = !context in
  let newscope = process scope g in
    context := (idx+1, newscope, scope :: stack)

(* -------------------------------------------------------------------- *)
module IntCommand = struct
  open EcScope
  open EcBaseLogic
  open EcLogic
  open EcPrinting

  let goalline = String.make 72 '-'

  let prgoal env (stream : out_channel) (n, (hyps, concl)) =
    let pr_hyp t (id, k) = 
      let dk = 
        match k with
        | LD_var (ty, _body) -> pr_type t ty (* FIXME body *)
        | LD_mem _           -> tk_memory
        | LD_modty p         -> pr_modtype t p
        | LD_hyp f           -> pr_form t f
      in

      let dh = join [pr_ident t id; !^":"; dk] in
        Printf.fprintf stream "%t\n%!"
          (fun stream -> pretty stream dh);
        PPE.add_local t id
    in
      begin
        match n with
        | 0 -> Printf.fprintf stream "Current goal\n%!"
        | _ -> Printf.fprintf stream "Current goal (remaining: %d)\n%!" n
      end;
      Printf.fprintf stream "Type variables: %t\n%!"
        (fun stream ->
          let doc = 
            List.map (pr_tvar (EcPrinting.empty env))
              hyps.h_tvar in (* FIXME *)
            pretty stream (seq ~sep:"," doc));
      let _ =
        List.fold_left pr_hyp (EcPrinting.empty env) (List.rev hyps.h_local) (* FIXME *)
      in
        Printf.fprintf stream "%s\n%!" goalline;
        Printf.fprintf stream "%t\n%!"
          (fun stream -> pretty stream (pr_form (EcPrinting.empty env) concl)) (* FIXME *)

  let prgoal_current (stream : out_channel) =
    let (_, scope, _) = !context in

      match List.ohead (EcScope.goal scope) with
      | None -> ()

      | Some goal -> begin
          let juc = goal.puc_jdg in
          try 
            let n = List.length (snd (find_all_goals juc)) in
            let g = get_goal (get_first_goal juc) in
              prgoal (EcScope.env scope) stream (n, g)
          with EcBaseLogic.NotAnOpenGoal _ -> 
            Printf.fprintf stream "No more goals\n%!"
      end
end
