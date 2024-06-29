open EcUtils
open EcFol
open EcEnv
open EcProvers

(*---------------------------------------------------------------------------------*)
(* What follows is inspired from Frama-C                                           *)
(*---------------------------------------------------------------------------------*)

type prover_call = {
  prover : Why3.Whyconf.prover ;
  call : Why3.Call_provers.prover_call ;
  steps : int option ;
  timeout : float ;
  mutable timeover : float option ;
  mutable interrupted : bool ;
}

type verdict =
  | NoResult
  | Invalid
  | Unknown
  | Timeout
  | Stepout
  | Valid
  | Failed
  | Canceled

type result = {
  verdict : verdict ;
  cached : bool ;
  solver_time : float ;
  prover_time : float ;
  prover_steps : int ;
  prover_errpos : Lexing.position option ;
  prover_errmsg : string ;
}

let result ?(cached=false) ?(solver=0.0) ?(time=0.0) ?(steps=0) verdict =
  {
    verdict ;
    cached = cached ;
    solver_time = solver ;
    prover_time = time ;
    prover_steps = steps ;
    prover_errpos = None ;
    prover_errmsg = "" ;
  }

let no_result = result NoResult
let valid = result Valid
let invalid = result Invalid
let unknown = result Unknown
let timeout t = result ~time:t Timeout
let stepout n = result ~steps:n Stepout
let failed ?pos msg = {
  verdict = Failed ;
  cached = false ;
  solver_time = 0.0 ;
  prover_time = 0.0 ;
  prover_steps = 0 ;
  prover_errpos = pos ;
  prover_errmsg = msg ;
}
let canceled = result Canceled

let is_valid = function { verdict = Valid } -> true | _ -> false

let ping_prover_call ~config p =
  let pr = Why3.Call_provers.wait_on_call p.call in
  let r =
    match pr.pr_answer with
    | Timeout -> timeout pr.pr_time
    | Valid -> result ~time:pr.pr_time ~steps:pr.pr_steps Valid
    | Invalid -> result ~time:pr.pr_time ~steps:pr.pr_steps Invalid
    | OutOfMemory -> failed "out of memory"
    | StepLimitExceeded -> result ?steps:p.steps Stepout
    | Unknown _ -> unknown
    | _ when p.interrupted -> timeout p.timeout
    | Failure s -> failed s
    | HighFailure -> failed "Unknown error"
  in
  Some r

let call_prover_task ~timeout ~steps ~config prover call =
  let timeout = match timeout with None -> 0.0 | Some tlimit -> tlimit in
  let pcall = {
    call ; prover ;
    interrupted = false ;
    steps ; timeout ; timeover = None ;
  }
  in
  ping_prover_call ~config pcall

let run_batch pconf driver ~config ?script ~timeout prover task =
  let config = Why3.Whyconf.get_main config in
  let config_mem = Why3.Whyconf.memlimit config in
  let steps = None in
  let config_time = Why3.Whyconf.timelimit config in
  let config_steps = Why3.Call_provers.empty_limit.limit_steps in
  let limit =
    Why3.Call_provers.{
      limit_time = Option.value ~default:config_time timeout;
      limit_steps = config_steps;
      limit_mem = config_mem;
    }
  in
  let with_steps = false in
  let command = Why3.Whyconf.get_complete_command pconf ~with_steps in
  let inplace = if script <> None then Some true else None in
  let call =
    Why3.Driver.prove_task_prepared ?old:script ?inplace
      ~command ~limit ~config driver task
  in
  call_prover_task ~config ~timeout ~steps prover call

let pp_to_file f pp =
  let cout = open_out f in
  let fout = Format.formatter_of_out_channel cout in
  try
    pp fout ;
    Format.pp_print_flush fout () ;
    close_out cout
  with err ->
    Format.pp_print_flush fout () ;
    close_out cout ;
    raise err

let make_output_dir dir =
  if Sys.file_exists dir then ()
  else Unix.mkdir dir 0o770

let editor_command pconf config =
  try
    let ed = Why3.Whyconf.editor_by_id config pconf.Why3.Whyconf.editor in
    String.concat " " (ed.editor_command :: ed.editor_options)
  with Not_found ->
    Why3.Whyconf.(default_editor (get_main config))

let scriptfile ~(loc:EcLocation.t) ~name ~ext =
  let file = loc.loc_fname in
  let path = Filename.dirname file in
  let path = path ^ "/.interactive" in
  make_output_dir path;
  let name =
    if String.is_empty name then
      begin
        let name = Filename.basename file in
        let name = Filename.remove_extension name in
        let l,r = loc.loc_start in
        let sid = string_of_int l ^ string_of_int r in
        name ^ sid
      end
    else name
  in
  Format.sprintf "%s/%s%s" path name ext

let safe_remove f = try Unix.unlink f with Unix.Unix_error _ -> ()

let updatescript ~script driver task =
  let backup = script ^ ".bak" in
  Sys.rename script backup ;
  let old = open_in backup in
  pp_to_file script
    (fun fmt ->
       ignore @@ Why3.Driver.print_task_prepared ~old driver fmt task
    );
  close_in old ;
  let d_old = Digest.file backup in
  let d_new = Digest.file script in
  if String.equal d_new d_old then safe_remove backup

let editor ~script ~merge ~config pconf driver task =
  if merge then updatescript ~script driver task ;
  let command = editor_command pconf config in
  let config = Why3.Whyconf.get_main config in
  let call =
    Why3.Call_provers.call_editor
      ~command ~config script
  in
  call_prover_task ~config ~timeout:None ~steps:None pconf.prover call

let prepare ~name ~loc driver task =
  let ext = Filename.extension (Why3.Driver.file_of_task driver "S" "T" task) in
  let script = scriptfile ~loc ~name ~ext in
  if Sys.file_exists script then (script, true) else
    begin
      pp_to_file script
        (fun fmt ->
           ignore @@ Why3.Driver.print_task_prepared driver fmt task
        );
      (script, false)
    end

let interactive ~notify ~name ~coqmode ~loc pconf ~config driver prover task =
  let time = 10 in
  let timeout = if time <= 0 then None else Some (float time) in
  let script, merge =  prepare ~name ~loc driver task in
  if merge then updatescript ~script driver task ;
  match coqmode with
  | Check ->
    run_batch ~script ~timeout ~config pconf driver prover task
  | Edit ->
    editor ~script ~merge ~config pconf driver task |> obind (fun _ ->
        run_batch ~script ~timeout ~config pconf driver prover task)
  | Fix ->
    run_batch ~script ~timeout ~config pconf driver prover task
    |> obind (fun r ->
        if is_valid r then Some r else
          editor ~script ~merge ~config pconf driver task |> obind (fun _ ->
              run_batch ~script ~timeout ~config pconf driver prover task))

let is_trivial (t : Why3.Task.task) =
  let goal = Why3.Task.task_goal_fmla t in
  Why3.Term.t_equal goal Why3.Term.t_true

exception CoqNotFound

let build_proof_task ~notify ~name ~coqmode ~loc ~config ~env task =
  try
    let (prover,pconf) =
      let fp = Why3.Whyconf.parse_filter_prover "Coq" in
      let provers = Why3.Whyconf.filter_provers config fp in
      begin
        match Why3.Whyconf.Mprover.is_empty provers with
        | false ->
          begin
            (* Format.eprintf "Versions of Coq found:\n"; *)
            (* Why3.Whyconf.(Mprover.iter (fun k _ -> *)
            (*     Format.printf " %s\n" k.prover_version *)
            (*   )) provers; *)

            let prover = Why3.Whyconf.Mprover.max_binding provers in

            (* Format.eprintf "Take Coq %s\n" (fst prover).prover_version; *)

            prover
          end
        | true -> raise CoqNotFound
      end
    in
    let drv = Why3.Driver.load_driver_for_prover (Why3.Whyconf.get_main config)
        env pconf
    in
    let task = Why3.Driver.prepare_task drv task in

    if is_trivial task then
      Some valid
    else
      interactive ~notify ~name ~coqmode ~loc pconf ~config drv prover task
  with
  | CoqNotFound ->
    notify |> oiter (fun notify -> notify `Critical (lazy (
        Format.asprintf "Prover Coq not installed or not configured"
      )));
    None
  | exn ->
    notify |> oiter (fun notify -> notify `Critical (lazy (
        Format.asprintf "[Why3 Error] %a" Why3.Exn_printer.exn_printer exn
      )));
    None

let config = lazy (get_w3_conf ())
let env = lazy (get_w3_env ())

let check ~loc ~name ?notify pi ?(coqmode=Edit) (hyps : LDecl.hyps) (concl : form) =
  let config = Lazy.force config in
  let env = Lazy.force env in
  let ec_env = LDecl.toenv hyps in
  let hyps = LDecl.tohyps hyps in
  let tenv = EcSmt.init ~env ec_env in

  let execute_task toadd =
    let task = EcSmt.make_task tenv hyps concl toadd in
    match build_proof_task ~notify ~name ~coqmode ~loc ~config ~env task with
    | None -> None
    | Some r -> match r.verdict with
      | Valid -> Some true
      | _ -> None
  in
  EcSmt.select ec_env pi hyps concl execute_task
