(* -------------------------------------------------------------------- *)
open EcUtils
open EcLocation
open EcFol
open EcEnv
open EcProvers

(* -------------------------------------------------------------------- *)
module WCall_provers = Why3.Call_provers
module WConf         = Why3.Whyconf
module WDriver       = Why3.Driver
module WEnv          = Why3.Env
module WTask         = Why3.Task

(* -------------------------------------------------------------------- *)
type coqenv = {
  config : WConf.config;
  main   : WConf.main;
  driver : WDriver.driver;
  cnfprv : WConf.config_prover;
  prover : WConf.prover;
}

(* -------------------------------------------------------------------- *)
let call_prover_task ~(coqenv : coqenv) (call : WCall_provers.prover_call) =
  EcUtils.try_finally
    (fun () ->
      match (Why3.Call_provers.wait_on_call call).pr_answer with
      | Valid -> Some `Valid
      | Invalid -> Some `Invalid
      | _ -> None)
    (fun () ->
      WCall_provers.interrupt_call ~config:coqenv.main call)

(* -------------------------------------------------------------------- *)
let run_batch ~(script : string) ~(coqenv : coqenv) (task : WTask.task) =
  let config = Why3.Whyconf.get_main coqenv.config in
  let config_mem = Why3.Whyconf.memlimit config in
  let config_time = Why3.Whyconf.timelimit config in
  let limit =
    Why3.Call_provers.{
      limit_time = config_time;
      limit_steps = 0;
      limit_mem = config_mem;
    }
  in
  let command =
    Why3.Whyconf.get_complete_command
      coqenv.cnfprv ~with_steps:false in
  let call =
    Why3.Driver.prove_task_prepared
      ~old:script ~inplace:true
      ~command ~limit ~config coqenv.driver task
  in call_prover_task ~coqenv call

(* -------------------------------------------------------------------- *)
let editor_command ~(coqenv : coqenv) : string =
  try
    let editors = Why3.Whyconf.get_editors coqenv.config in
    let editors =
      Why3.Whyconf.Meditor.filter
        (fun _ a -> a.Why3.Whyconf.editor_name = "Emacs/ProofGeneral/Coq")
        editors
    in
    let _, ed = Why3.Whyconf.Meditor.max_binding editors in
    String.concat " " (ed.editor_command :: ed.editor_options)

  with Not_found ->
    Why3.Whyconf.(default_editor (get_main coqenv.config))

(* -------------------------------------------------------------------- *)
let script_file ~(name : string located) ~(ext : string) =
  let { pl_loc = loc; pl_desc = name; } = name in
  let file = loc.loc_fname in
  let path = Filename.dirname file in
  let path =
    if Filename.is_relative path then
      Filename.concat (Sys.getcwd ()) path
    else path in
  let path = Filename.concat path ".interactive" in
  let name =
    if String.is_empty name then
      let name = Filename.basename file in
      let name = Filename.remove_extension name in
      let l, r = loc.loc_start in
      Format.sprintf "%s-%d-%d" name l r
    else name
  in
  Format.sprintf "%s/%s%s" path name ext

(* -------------------------------------------------------------------- *)
let update_script
  ~(script : string)
  ~(coqenv : coqenv)
   (task   : WTask.task)
=
  let backup = Format.sprintf "%s~" script in
  Sys.rename script backup;

  let old = open_in backup in
  EcUtils.try_finally
    (fun () ->
      IO.pp_to_file ~filename:script
      (fun fmt -> ignore @@
        Why3.Driver.print_task_prepared ~old coqenv.driver fmt task))
    (fun () -> close_in old)

(* -------------------------------------------------------------------- *)
let editor
  ~(script : string)
  ~(merge  : bool)
  ~(coqenv : coqenv)
   (task   : WTask.task)
=
  if merge then update_script ~script ~coqenv task;
  let command = editor_command ~coqenv in
  let config = WConf.get_main coqenv.config in
  let call = WCall_provers.call_editor ~command ~config script in
  ignore @@ call_prover_task ~coqenv call

(* -------------------------------------------------------------------- *)
let prepare
  ~(name   : string located)
  ~(coqenv : coqenv)
   (task   : WTask.task)
=
  let ext = Why3.Driver.file_of_task coqenv.driver "S" "T" task in
  let ext = Filename.extension ext in
  let script = script_file ~name ~ext in

  if Sys.file_exists script then
    (script, true)
  else begin
    EcUtils.makedirs (Filename.dirname script);
    EcUtils.IO.pp_to_file ~filename:script
      (fun fmt -> ignore @@
        Why3.Driver.print_task_prepared coqenv.driver fmt task);
    (script, false)
  end

(* -------------------------------------------------------------------- *)
let interactive
  ~(name    : string located)
  ~(coqmode : coq_mode)
  ~(coqenv  : coqenv)
   (task    : WTask.task)
=
  let script, merge = prepare ~name ~coqenv task in

  if merge then
    update_script ~script ~coqenv task;
  match coqmode with
  | Check ->
    run_batch ~script ~coqenv task

  | Edit ->
      editor ~script ~merge ~coqenv task;
      run_batch ~script ~coqenv task

  | Fix -> begin
    match run_batch ~script ~coqenv task with
    | Some `Valid as answer ->
      answer
    | _ ->
      editor ~script ~merge ~coqenv task;
      run_batch ~script ~coqenv task
  end

(* -------------------------------------------------------------------- *)
let is_trivial (t : Why3.Task.task) =
  let goal = Why3.Task.task_goal_fmla t in
  Why3.Term.t_equal goal Why3.Term.t_true

(* -------------------------------------------------------------------- *)
let build_proof_task
  ~(notify  : notify option)
  ~(name    : string located)
  ~(coqmode : coq_mode)
  ~(config  : WConf.config)
  ~(env     : WEnv.env)
   (task    : WTask.task)
=
  let exception CoqNotFound in

  try
    let coqenv =
      let (prover, cnfprv) =
        let fp = Why3.Whyconf.parse_filter_prover "Coq" in
        let provers = Why3.Whyconf.filter_provers config fp in
        begin
          match Why3.Whyconf.Mprover.is_empty provers with
          | false -> Why3.Whyconf.Mprover.max_binding provers
          | true -> raise CoqNotFound
        end
      in
      let main = Why3.Whyconf.get_main config in
      let driver =
        Why3.Driver.load_driver_for_prover
          main env cnfprv
      in { config; main; driver; cnfprv; prover; } in

    let task = Why3.Driver.prepare_task coqenv.driver task in

    if is_trivial task then
      Some `Valid
    else
      interactive ~name ~coqmode ~coqenv task

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

(* -------------------------------------------------------------------- *)
let check
  ~(loc     : EcLocation.t)
  ~(name    : string)
  ?(notify  : notify option)
   (pi      : prover_infos)
  ?(coqmode : coq_mode = Edit)
   (hyps    : LDecl.hyps)
   (concl   : form)
=
  EcProvers.maybe_start_why3_server pi;

  let config = EcProvers.get_w3_conf () in
  let env = EcProvers.get_w3_env () in
  let ec_env, hyps, tenv, decl = EcSmt.init hyps concl in

  let execute_task toadd =
    let task = EcSmt.make_task tenv toadd decl in
    let result =
      build_proof_task ~notify ~name:(mk_loc loc name) ~coqmode ~config ~env task in
    Option.map (fun r -> r = `Valid) result
  in EcSmt.select ec_env pi hyps concl execute_task
