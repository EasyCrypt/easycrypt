open EcFol

let is_f_glob f =
  match f.f_node with
  | Fglob _ -> true
  | _       -> false

(*
let is_classical_or_local  =
  let rec is_classical env f =
  match f.f_node with
  | Fquant (_,_,f) | Fproj(f,_) -> is_classical env f
  | Fif (f1,f2,f3) -> is_classical env f1 && is_classical env f2 && is_classical env f3
  | Flet (_,f1,f2) -> is_classical env f1 && is_classical env f2
  | Fmatch (f,fs,_) | Fapp(f,fs) -> List.for_all (is_classical env) (f::fs)
  | Ftuple fs -> List.for_all (is_classical env) fs
  | Fglob   (mp,_) -> is_classical_glob env mp
  | Fint _ | Flocal _ | Fop _ -> true
  | Fpvar _ -> true
  (* FIXME quantum : what to do here ? *)
  | FhoareF _ | FhoareS _
  | FcHoareF _ | FcHoareS _
  | FbdHoareF _ | FbdHoareS _
  | FequivF _ | FequivS _
  | FeagerF _  | Fcoe _ | Fpr _ -> assert false in
  is_classical
 *)

let rec wf_quantum env f =
  match f.f_node with
  | Fquant(Lforall, _, f) -> wf_quantum env f
  | Fapp({f_node = Fop(op, _)}, args) ->
    begin match op_kind op, args with
    | Some(`And `Sym), [f1; f2] -> wf_quantum env f1 && wf_quantum env f2
    (* Fixme quantum : is it valid ? *)
   (* | Some(`And `Asym), [f1; f2] -> is_classical env f1 && wf_quantum env f2 *)
    | Some(`And `Asym), [f1; f2] -> wf_quantum env f1 && wf_quantum env f2
    | Some(`Or _), [f1; f2] ->
         is_classical(* _or_local*) env f1 && wf_quantum env f2
      || wf_quantum env f1 && is_classical (*_or_local*) env f2
    | Some `Imp, [f1; f2] ->
      is_classical(*_or_local*) env f1 && wf_quantum env f2
    | Some `Eq, [f1; f2] when is_f_glob f1 && is_f_glob f2 -> true
    | _ -> is_classical(*_or_local*) env f
    end
  | Fif (f1, f2, f3) ->
    is_classical env f1 && wf_quantum env f2 && wf_quantum env f3
  | _ -> is_classical env f

(*
FIXME quantum
a || b
a \/ (!a => b)

a \/ (!!a \/ b)
a \/ (a \/ b)

I really don't like that
a && b
a /\ a => b

*)

exception NotWfQuantum of EcEnv.env * form
exception NotClassical of EcEnv.env * form

(* FIXME: quantum *)
let check_wf_quantum env f =
  if not (wf_quantum env f) then
    EcCoreGoal.tacuerror_exn (NotWfQuantum(env, f))

let check_classical env f =
  if not (is_classical env f) then
    EcCoreGoal.tacuerror_exn (NotClassical(env, f))

(* ------------------------------------------------------------------ *)

let pp_exn fmt exn =
  match exn with
  | NotWfQuantum(env, f) ->
    let ppe = EcPrinting.PPEnv.ofenv env in
    Format.fprintf fmt "invalid quantum formula : @[%a@]"
      (EcPrinting.pp_form ppe) f

  | NotClassical(env, f) ->
    let ppe = EcPrinting.PPEnv.ofenv env in
    Format.fprintf fmt "not a classical formula : @[%a@]"
      (EcPrinting.pp_form ppe) f
  | _ -> raise exn

let _ = EcPException.register pp_exn
