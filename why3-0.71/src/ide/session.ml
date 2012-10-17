(**************************************************************************)
(*                                                                        *)
(*  Copyright (C) 2010-2011                                               *)
(*    François Bobot                                                      *)
(*    Jean-Christophe Filliâtre                                           *)
(*    Claude Marché                                                       *)
(*    Andrei Paskevich                                                    *)
(*                                                                        *)
(*  This software is free software; you can redistribute it and/or        *)
(*  modify it under the terms of the GNU Library General Public           *)
(*  License version 2.1, with the special exception on linking            *)
(*  described in file LICENSE.                                            *)
(*                                                                        *)
(*  This software is distributed in the hope that it will be useful,      *)
(*  but WITHOUT ANY WARRANTY; without even the implied warranty of        *)
(*  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.                  *)
(*                                                                        *)
(**************************************************************************)


open Why3
open Format

(***************************)
(*     provers             *)
(***************************)

type prover_data =
    { prover_id : string;
      prover_name : string;
      prover_version : string;
      command : string;
      driver_name : string;
      driver : Driver.driver;
      mutable editor : string;
      interactive : bool;
    }

let get_prover_data env id pr acc =
  try
    let dr = Driver.load_driver env pr.Whyconf.driver in
    Util.Mstr.add id
      { prover_id = id ;
        prover_name = pr.Whyconf.name;
        prover_version = pr.Whyconf.version;
        command = pr.Whyconf.command;
        driver_name = pr.Whyconf.driver;
        driver = dr;
        editor = pr.Whyconf.editor;
        interactive = pr.Whyconf.interactive;
      }
      acc
  with e ->
    eprintf "Failed to load driver %s for prover %s (%a). prover disabled@."
      pr.Whyconf.driver
      pr.Whyconf.name
      Exn_printer.exn_printer e
      ;
    acc

(***************************)
(*      transformations    *)
(***************************)

type trans =
  | Trans_one of Task.task Trans.trans
  | Trans_list of Task.task Trans.tlist

type transformation_data =
    { transformation_name : string;
      transformation : trans;
    }

let transformation_id t = t.transformation_name

let lookup_trans env name =
  try
    let t = Trans.lookup_transform name env in
    Trans_one t
  with Trans.UnknownTrans _ ->
    let t = Trans.lookup_transform_l name env in
    Trans_list t

let lookup_transformation env =
  let h = Hashtbl.create 13 in
  fun name ->
    try
      Hashtbl.find h name
    with Not_found ->
      let t = {transformation_name = name;
               transformation = lookup_trans env name }
      in Hashtbl.add h name t; t

(***************************)
(*     proof status        *)
(***************************)

type proof_attempt_status =
  | Undone
  | Scheduled (** external proof attempt is scheduled *)
  | Interrupted
  | Running (** external proof attempt is in progress *)
  | Done of Call_provers.prover_result (** external proof done *)
  | InternalFailure of exn (** external proof aborted by internal error *)
  | Unedited (** interactive prover yet no proof script *)

(***************************)
(*     main functor        *)
(***************************)

module type OBSERVER = sig
  type key
  val create: ?parent:key -> unit -> key
  val remove: key -> unit
  val reset: unit -> unit

  val timeout: ms:int -> (unit -> bool) -> unit
  val idle: (unit -> bool) -> unit

  val notify_timer_state : int -> int -> int -> unit

end

module Make(O : OBSERVER) = struct

(***************************)
(*     session state       *)
(***************************)

type prover_option =
  | Detected_prover of prover_data
  | Undetected_prover of string

let prover_id p = match p with
  | Detected_prover p -> p.prover_id
  | Undetected_prover s -> s

type proof_attempt =
    { prover : prover_option;
      proof_goal : goal;
      proof_key : O.key;
      mutable proof_state : proof_attempt_status;
      mutable timelimit : int;
      mutable proof_obsolete : bool;
      mutable edited_as : string;
    }

and goal_parent =
  | Parent_theory of theory
  | Parent_transf of transf

and goal =
    { goal_name : string;
      goal_expl : string option;
      parent : goal_parent;
      mutable task: Task.task option;
      mutable checksum : string;
      goal_shape : string;
      goal_key : O.key;
      mutable proved : bool;
      mutable goal_expanded : bool;
      external_proofs: (string, proof_attempt) Hashtbl.t;
      transformations : (string, transf) Hashtbl.t;
    }

and transf =
    { transf : transformation_data;
      parent_goal : goal;
      mutable transf_proved : bool;
      transf_key : O.key;
      mutable subgoals : goal list;
      mutable transf_expanded : bool;
    }

and theory =
    { theory_name : string;
      mutable theory : Theory.theory option;
      theory_key : O.key;
      theory_parent : file;
      mutable goals : goal list;
      mutable verified : bool;
      mutable theory_expanded : bool;
    }

and file =
    { file_name : string;
      file_key : O.key;
      mutable theories: theory list;
      mutable file_verified : bool;
      mutable file_expanded : bool;
    }

type any =
  | File of file
  | Theory of theory
  | Goal of goal
  | Proof_attempt of proof_attempt
  | Transformation of transf

let theory_name t = t.theory_name
let theory_key t = t.theory_key
let verified t = t.verified
let goals t = t.goals
let theory_expanded t = t.theory_expanded

let running a = match a.proof_state with
  | Scheduled | Running | Interrupted -> true
  | Undone | Done _ | InternalFailure _ | Unedited -> false

let get_theory t =
  match t.theory with
    | None ->
        eprintf "Session: theory not yet reimported, this should not happen@.";
        assert false
    | Some t -> t

let goal_name g = g.goal_name
let goal_expl g =
  match g.goal_expl with
    | None -> g.goal_name
    | Some s -> s
let goal_key g = g.goal_key
let goal_proved g = g.proved
let transformations g = g.transformations
let external_proofs g = g.external_proofs
let goal_expanded g = g.goal_expanded

let get_task g =
  match g.task with
    | None ->
        begin
          match g.parent with
            | Parent_theory _th ->
                assert false (* should not happen *)
            | Parent_transf _tr ->
                (* TODO: recompute the task from the parent transformation *)
                assert false
        end
    | Some t -> t


let rec set_goal_expanded g b =
  g.goal_expanded <- b;
  if not b then
    Hashtbl.iter (fun _ tr -> set_transf_expanded tr b) g.transformations

and set_transf_expanded tr b =
  tr.transf_expanded <- b;
  if not b then
    List.iter (fun g -> set_goal_expanded g b) tr.subgoals

let set_theory_expanded t b =
  t.theory_expanded <- b;
  if not b then
    List.iter (fun th -> set_goal_expanded th b) t.goals

let set_file_expanded f b =
  f.file_expanded <- b;
  if not b then
    List.iter (fun th -> set_theory_expanded th b) f.theories

let all_files : file list ref = ref []

let get_all_files () = !all_files

let current_env = ref None
let current_provers = ref Util.Mstr.empty
let project_dir = ref ""

let get_provers () = !current_provers

(************************)
(* saving state on disk *)
(************************)

let save_result fmt r =
  fprintf fmt "@\n<result status=\"%s\" time=\"%.2f\"/>"
    (match r.Call_provers.pr_answer with
       | Call_provers.Valid -> "valid"
       | Call_provers.Failure _ -> "failure"
       | Call_provers.Unknown _ -> "unknown"
       | Call_provers.HighFailure -> "highfailure"
       | Call_provers.Timeout -> "timeout"
       | Call_provers.Invalid -> "invalid")
    r.Call_provers.pr_time

let save_status fmt s =
  match s with
    | Undone | Scheduled | Running | Interrupted ->
        fprintf fmt "<undone/>@\n"
    | Unedited ->
        fprintf fmt "<unedited/>@\n"
    | InternalFailure msg ->
        fprintf fmt "<internalfailure reason=\"%s\"/>@\n"
          (Printexc.to_string msg)
    | Done r -> save_result fmt r

let save_proof_attempt fmt _key a =
  fprintf fmt "@\n@[<v 1><proof@ prover=\"%s\"@ timelimit=\"%d\"@ edited=\"%s\"@ obsolete=\"%b\">"
    (prover_id a.prover) a.timelimit a.edited_as a.proof_obsolete;
  save_status fmt a.proof_state;
  fprintf fmt "@]@\n</proof>"

let opt lab fmt = function
  | None -> ()
  | Some s -> fprintf fmt "%s=\"%s\"@ " lab s

let rec save_goal fmt g =
  assert (g.goal_shape <> "");
  fprintf fmt "@\n@[<v 1><goal@ name=\"%s\"@ %asum=\"%s\"@ proved=\"%b\"@ expanded=\"%b\"@ shape=\"%s\">"
    g.goal_name (opt "expl") g.goal_expl g.checksum g.proved  g.goal_expanded
    g.goal_shape;
  Hashtbl.iter (save_proof_attempt fmt) g.external_proofs;
  Hashtbl.iter (save_trans fmt) g.transformations;
  fprintf fmt "@]@\n</goal>"

and save_trans fmt _ t =
  fprintf fmt "@\n@[<v 1><transf@ name=\"%s\"@ proved=\"%b\"@ expanded=\"%b\">"
    t.transf.transformation_name t.transf_proved t.transf_expanded;
  List.iter (save_goal fmt) t.subgoals;
  fprintf fmt "@]@\n</transf>"

let save_theory fmt t =
  fprintf fmt "@\n@[<v 1><theory@ name=\"%s\"@ verified=\"%b\"@ expanded=\"%b\">"
    t.theory_name t.verified t.theory_expanded;
  List.iter (save_goal fmt) t.goals;
  fprintf fmt "@]@\n</theory>"

let save_file fmt f =
  fprintf fmt "@\n@[<v 1><file@ name=\"%s\"@ verified=\"%b\"@ expanded=\"%b\">"
    f.file_name f.file_verified f.file_expanded;
  List.iter (save_theory fmt) f.theories;
  fprintf fmt "@]@\n</file>"

let save_prover fmt p =
  fprintf fmt "@\n@[<v 1><prover@ id=\"%s\"@ name=\"%s\"@ version=\"%s\"/>@]"
    p.prover_id p.prover_name p.prover_version

let save fname =
  let ch = open_out fname in
  let fmt = formatter_of_out_channel ch in
  fprintf fmt "<?xml version=\"1.0\" encoding=\"UTF-8\"?>@\n";
  fprintf fmt "<!DOCTYPE why3session SYSTEM \"why3session.dtd\">@\n";
  fprintf fmt "@[<v 1><why3session@ name=\"%s\">" fname;
  Util.Mstr.iter (fun _ d -> save_prover fmt d) (get_provers ());
  List.iter (save_file fmt) (get_all_files());
  fprintf fmt "@]@\n</why3session>";
  fprintf fmt "@.";
  close_out ch

(************************)
(*     actions          *)
(************************)

let init_fun = ref (fun (_:O.key) (_:any) -> ())

let notify_fun = ref (fun (_:any) -> ())

let check_file_verified f =
  let b = List.for_all (fun t -> t.verified) f.theories in
  f.file_verified <- b;
  !notify_fun (File f)

let check_theory_proved t =
  let b = List.for_all (fun g -> g.proved) t.goals in
  t.verified <- b;
  !notify_fun (Theory t);
  check_file_verified t.theory_parent

let rec check_goal_proved g =
  let b1 = Hashtbl.fold
    (fun _ a acc -> acc ||
       not a.proof_obsolete &&
       match a.proof_state with
         | Done { Call_provers.pr_answer = Call_provers.Valid} -> true
         | _ -> false) g.external_proofs false
  in
  let b = Hashtbl.fold
    (fun _ t acc -> acc || t.transf_proved) g.transformations b1
  in
  g.proved <- b;
  !notify_fun (Goal g);
  match g.parent with
    | Parent_theory t -> check_theory_proved t
    | Parent_transf t -> check_transf_proved t

and check_transf_proved t =
  let b = List.for_all (fun g -> g.proved) t.subgoals in
  t.transf_proved <- b;
  !notify_fun (Transformation t);
  check_goal_proved t.parent_goal

let set_proof_state ~obsolete a res =
  a.proof_state <- res;
  a.proof_obsolete <- obsolete;
  !notify_fun (Proof_attempt a);
  check_goal_proved a.proof_goal

(*************************)
(*         Scheduler     *)
(*************************)


type action =
  | Action_proof_attempt of bool * int * int * in_channel option * string * Driver.driver *
    (proof_attempt_status -> unit) * Task.task
  | Action_delayed of (unit -> unit)

let actions_queue = Queue.create ()

(* timeout handler *)

type timeout_action =
  | Check_prover of (proof_attempt_status -> unit) * Call_provers.prover_call
  | Any_timeout of (unit -> bool)

let maximum_running_proofs = ref 2
let running_proofs = ref []

let proof_attempts_queue = Queue.create ()

let timeout_handler_activated = ref false
let timeout_handler_running = ref false

let timeout_handler () =
  assert (not !timeout_handler_running);
  timeout_handler_running := true;
  let l = List.fold_left
    (fun acc c ->
       match c with
         | Check_prover(callback,call)  ->
             (match Call_provers.query_call call with
               | None -> c::acc
               | Some post ->
                   let res = post () in callback (Done res);
                   acc)
         | Any_timeout callback ->
             let b = callback () in
             if b then c::acc else acc)
    [] !running_proofs
  in
  let l =
    if List.length l < !maximum_running_proofs then
      begin try
        let (callback,pre_call) = Queue.pop proof_attempts_queue in
        callback Running;
        let call = pre_call () in
        (Check_prover(callback,call))::l
      with Queue.Empty -> l
      end
    else l
  in
  running_proofs := l;
  let continue =
    match l with
      | [] ->
(*
          eprintf "Info: timeout_handler stopped@.";
*)
          false
      | _ -> true
  in
  O.notify_timer_state
    (Queue.length actions_queue)
    (Queue.length proof_attempts_queue) (List.length l);
  timeout_handler_activated := continue;
  timeout_handler_running := false;
  continue

let run_timeout_handler () =
  if !timeout_handler_activated then () else
    begin
      timeout_handler_activated := true;
(*
      eprintf "Info: timeout_handler started@.";
*)
      O.timeout ~ms:100 timeout_handler
    end

let schedule_any_timeout callback =
  running_proofs := (Any_timeout callback) :: ! running_proofs;
  run_timeout_handler ()

(* idle handler *)


let idle_handler_activated = ref false

let idle_handler () =
  try
    begin
      match Queue.pop actions_queue with
        | Action_proof_attempt(debug,timelimit,memlimit,old,command,driver,
                               callback,goal) ->
            callback Scheduled;
            if debug then
              Format.eprintf "Task for prover: %a@."
                (Driver.print_task driver) goal;
            begin
              try
                let pre_call =
                  Driver.prove_task ?old ~command ~timelimit ~memlimit driver goal
                in
                Queue.push (callback,pre_call) proof_attempts_queue;
                run_timeout_handler ()
              with e ->
                Format.eprintf "@[Exception raise in Session.idle_handler:@ %a@.@]"
                  Exn_printer.exn_printer e;
                callback (InternalFailure e)
            end
        | Action_delayed callback -> callback ()
    end;
    true
  with Queue.Empty ->
    idle_handler_activated := false;
(*
    eprintf "Info: idle_handler stopped@.";
*)
    false
    | e ->
      Format.eprintf "@[Exception raise in Session.idle_handler:@ %a@.@]"
        Exn_printer.exn_printer e;
      eprintf "Session.idle_handler stopped@.";
      false


let run_idle_handler () =
  if !idle_handler_activated then () else
    begin
      idle_handler_activated := true;
(*
      eprintf "Info: idle_handler started@.";
*)
      O.idle idle_handler
    end

(* main scheduling functions *)

let cancel_scheduled_proofs () =
  let new_queue = Queue.create () in
  try
    while true do
      match Queue.pop actions_queue with
        | Action_proof_attempt(_debug,_timelimit,_memlimit,_old,_command,
                               _driver,callback,_goal) ->
            callback Interrupted
        | Action_delayed _ as a->
            Queue.push a new_queue
    done
  with Queue.Empty ->
    Queue.transfer new_queue actions_queue;
    try
      while true do
        let (callback,_) = Queue.pop proof_attempts_queue in
        callback Interrupted
      done
    with
      | Queue.Empty -> 
          O.notify_timer_state 0 0 (List.length !running_proofs)


let schedule_proof_attempt ~debug ~timelimit ~memlimit ?old
    ~command ~driver ~callback goal =
  (*
    eprintf "Scheduling a new proof attempt@.";
  *)
  Queue.push
    (Action_proof_attempt(debug,timelimit,memlimit,old,command,driver,
                        callback,goal))
    actions_queue;
  run_idle_handler ()

let schedule_edition command callback =
  let precall =
    Call_provers.call_on_buffer ~command ~regexps:[] ~timeregexps:[]
      ~exitcodes:[(0,Call_provers.Unknown "")] ~filename:"" (Buffer.create 1)
  in
  callback Running;
  running_proofs := (Check_prover(callback, precall ())) :: !running_proofs;
  run_timeout_handler ()

let schedule_delayed_action callback =
  Queue.push (Action_delayed callback) actions_queue;
  run_idle_handler ()

let apply_transformation ~callback t task =
   match t.transformation with
    | Trans_one t ->
        callback [Trans.apply t task]
    | Trans_list t ->
        callback (Trans.apply t task)

let schedule_edit_proof ~debug:_ ~editor ~file ~driver ~callback goal =
  let old =
    if Sys.file_exists file
    then
      begin
        let backup = file ^ ".bak" in
        Sys.rename file backup;
        Some(open_in backup)
      end
    else None
  in
  let ch = open_out file in
  let fmt = formatter_of_out_channel ch in
  Driver.print_task ?old driver fmt goal;
  Util.option_iter close_in old;
  close_out ch;
  let command = editor ^ " \"" ^ file ^ "\"" in
  schedule_edition command callback


(*******************************)
(*          explanations       *)
(*******************************)

  let expl_regexp = Str.regexp "expl:\\(.*\\)"

  exception Found of string

  let check_expl lab =
    if Str.string_match expl_regexp lab 0 then
      raise (Found (Str.matched_group 1 lab))

  let rec get_expl_fmla f =
    List.iter check_expl (List.rev f.Term.t_label);
    (match f.Term.t_node with
      | Term.Tbinop(Term.Timplies,_,f) -> get_expl_fmla f
      | Term.Tquant(Term.Tforall,fq) ->
          let (_,_,f) = Term.t_open_quant fq in get_expl_fmla f
      | Term.Tlet(_,fb) ->
          let (_,f) = Term.t_open_bound fb in get_expl_fmla f
      | Term.Tcase(_,[fb]) ->
          let (_,f) = Term.t_open_branch fb in get_expl_fmla f
      | _ -> ())

  let get_explanation id fmla =
    try
      get_expl_fmla fmla;
      List.iter check_expl (List.rev id.Ident.id_label);
      None
    with Found e -> Some e


(**********************)
(*     check sum      *)
(**********************)

(*
let task_checksum t =
  (* TODO: ignore print_locs and print_labels flag *)
  (* even better: compute check_sum directly, similar to the shape *)
  fprintf str_formatter "%a@." Pretty.print_task t;
  let s = flush_str_formatter () in
(*
  let tmp = Filename.temp_file "task" "out" in
  let c = open_out tmp in
  output_string c s;
  close_out c;
*)
  let sum = Digest.to_hex (Digest.string s) in
(*
  eprintf "task %s, sum = %s@." tmp sum;
*)
  sum
*)



(******************************)
(* raw additions to the model *)
(******************************)

let raw_add_external_proof ~obsolete ~timelimit ~edit (g:goal) p result =
  let key = O.create ~parent:g.goal_key () in
  let a = { prover = p;
            proof_goal = g;
            proof_key = key;
            proof_obsolete = obsolete;
            proof_state = result;
            timelimit = timelimit;
            edited_as = edit;
          }
  in
  Hashtbl.add g.external_proofs (prover_id p) a;
  let any = Proof_attempt a in
  !init_fun key any;
  !notify_fun any;
  a


(* [raw_add_goal parent name expl sum t] adds a goal to the given parent
   DOES NOT record the new goal in its parent, thus this should not be exported
*)
let raw_add_goal parent name expl sum shape topt exp =
  let parent_key = match parent with
    | Parent_theory mth -> mth.theory_key
    | Parent_transf mtr -> mtr.transf_key
  in
  let key = O.create ~parent:parent_key () in
  let sum,shape = match topt with
    | None -> sum,shape
    | Some t -> (Termcode.task_checksum t,
                 Termcode.t_shape_buf (Task.task_goal_fmla t))
  in
  let goal = { goal_name = name;
               goal_expl = expl;
               parent = parent;
               task = topt ;
               checksum = sum;
               goal_shape = shape;
               goal_key = key;
               external_proofs = Hashtbl.create 7;
               transformations = Hashtbl.create 3;
               proved = false;
               goal_expanded = exp;
             }
  in
  let any = Goal goal in
  !init_fun key any;
  !notify_fun any; (*useless ? *)
  goal


(* [raw_add_transformation g name adds a transformation to the given goal g
   Adds no subgoals, thus this should not be exported
*)
let raw_add_transformation g trans exp =
  let parent = g.goal_key in
  let key = O.create ~parent () in
  let tr = { transf = trans;
             parent_goal = g;
             transf_proved = false;
             transf_key = key;
             subgoals = [];
             transf_expanded = exp;
           }
  in
  Hashtbl.add g.transformations trans.transformation_name tr;
  let any = Transformation tr in
  !init_fun key any;
  !notify_fun any;
  tr

let raw_add_theory mfile thopt thname exp =
  let parent = mfile.file_key in
  let key = O.create ~parent () in
  let mth = { theory_name = thname;
              theory = thopt;
              theory_key = key;
              theory_parent = mfile;
              goals = [] ;
              verified = false;
              theory_expanded = exp;
            }
  in
  let any = Theory mth in
  !init_fun key any;
  !notify_fun any;
  mth



let add_theory mfile name th =
  let tasks = List.rev (Task.split_theory th None None) in
  let mth = raw_add_theory mfile (Some th) name true in
  let goals =
    List.fold_left
      (fun acc t ->
         let id = (Task.task_goal t).Decl.pr_name in
         let name = id.Ident.id_string in
         let expl = get_explanation id (Task.task_goal_fmla t) in
         let goal = raw_add_goal (Parent_theory mth) name expl "" "" (Some t) true in
         goal :: acc)
      []
      tasks
  in
  mth.goals <- List.rev goals;
  check_theory_proved mth;
  mth

let raw_add_file f exp =
  let key = O.create () in
  let mfile = { file_name = f;
                file_key = key;
                theories = [] ;
                file_verified = false;
                file_expanded = exp;
              }
  in
  all_files := !all_files @ [mfile];
  let any = File mfile in
  !init_fun key any;
  !notify_fun any;
  mfile


let read_file fn =
  let fn = Filename.concat !project_dir fn in
  let env = match !current_env with
    | None -> assert false | Some e -> e
  in
  let theories = Env.read_file env fn in
  let theories =
    Util.Mstr.fold
      (fun name th acc ->
         match th.Theory.th_name.Ident.id_loc with
           | Some l -> (l,name,th)::acc
           | None   -> (Loc.dummy_position,name,th)::acc)
      theories []
  in
  List.sort
    (fun (l1,_,_) (l2,_,_) -> Loc.compare l1 l2)
    theories

let add_file f =
  let theories = read_file f in
  let mfile = raw_add_file f true in
  let mths =
    List.fold_left
      (fun acc (_,name,t) ->
         let mth = add_theory mfile name t in
         mth :: acc)
      [] theories
  in
  mfile.theories <- List.rev mths;
  check_file_verified mfile;
  !notify_fun (File mfile)



let file_exists fn =
  List.exists (fun f -> f.file_name = fn) !all_files





(*************************************************************)
(* pairing of new and old subgoals of a given transformation *)
(*************************************************************)

(* we have an ordered list of new subgoals

           subgoals = [g1; g2; g3; ...]

   and a list of old subgoals

          old_subgoals = [h1 ; h2 ; ... ]

   we build a map from each new subgoal g to tuples
       (id,subgoal_name,subtask,sum,old_subgoal,obsolete)

   where
     id = name of the goal of g
     subgoal_name = name of parent goal with "dot n" added
     subtask = the corresponding task
     sum = the checksum of that task
     old_subgoal = ref to an optional old subgoal which is paired with g
     obsolete = true when paired to an old goal with different checksum

*)


type any_goal =
  | New_goal of int
  | Old_goal of goal

let array_map_list f l =
  let r = ref l in
  Array.init (List.length l)
    (fun i ->
       match !r with
         | [] -> assert false
         | x::rem -> r := rem; f i x)

let associate_subgoals gname old_goals new_goals =
  (*
     we make a map of old goals indexed by their checksums
  *)
  let old_goals_map = Hashtbl.create 7 in
  List.iter
    (fun g -> Hashtbl.add old_goals_map g.checksum g)
    old_goals;
  (*
     we make an array of new goals with their numbers and checksums 
  *)
  let new_goals_array =
    array_map_list
      (fun i g ->
         let id = (Task.task_goal g).Decl.pr_name in
         let goal_name = gname ^ "." ^ (string_of_int (i+1)) in
         let sum = Termcode.task_checksum g in
         (i,id,goal_name,g,sum))
      new_goals
  in
  let pairing_array =
    Array.make (Array.length new_goals_array) None
  in
  let shape_array =
    Array.make (Array.length new_goals_array) ""
  in
  let obsolete_array =
    Array.make (Array.length new_goals_array) false
  in
  (*
     Phase 1: we first associate each new goal for which there is an
     old goal with the same checksum.
  *)
  let associate_goals ~obsolete i g =
    pairing_array.(i) <- Some g;
    obsolete_array.(i) <- obsolete;
    Hashtbl.remove old_goals_map g.checksum
  in
  Array.iter
    (fun (i,_,_goal_name,_,sum) ->
       try
         let h = Hashtbl.find old_goals_map sum in
         (* an old goal has the same checksum *)
         (*
           eprintf "Merge phase 1: old goal '%s' -> new goal '%s'@."
           h.goal_name goal_name;
         *)
         shape_array.(i) <- h.goal_shape;
         associate_goals ~obsolete:false i h
       with Not_found ->
         (*
           eprintf "Merge phase 1: no old goal -> new goal '%s'@."
           subgoal_name;
         *)
         ())
    new_goals_array;
  (* Phase 2: we now build a list of all remaining new and old goals,
     ordered by shapes, then by name *)
  let old_goals_without_pairing =
    Hashtbl.fold
      (fun _ g acc ->
         let s = g.goal_shape in
         if s = "" then
           (* We don't try to associate old goals without shapes:
              they will be paired in order in next phase *)
           acc
         else
           (s,Old_goal g)::acc)
      old_goals_map
      []
  in
  let all_goals_without_pairing =
    Array.fold_left
      (fun acc (i,_,_, g, _) ->
         match pairing_array.(i) with
           | Some _ -> acc
           | None ->
               let shape = 
                 Termcode.t_shape_buf (Task.task_goal_fmla g)
               in
               shape_array.(i) <- shape;
               (shape,New_goal i)::acc)
      old_goals_without_pairing
      new_goals_array
  in
  let sort_by_shape =
    List.sort (fun (s1,_) (s2,_) -> String.compare s1 s2) 
      all_goals_without_pairing
  in
(*
  eprintf "[Merge] pairing the following shapes:@.";
  List.iter
    (fun (s,g) ->
       match g with
         | New_goal _ ->
             eprintf "new: %s@." s
         | Old_goal _ ->
             eprintf "old: %s@." s)
    sort_by_shape;
*)
  let rec similarity_shape n s1 s2 =
    if String.length s1 <= n || String.length s2 <= n then n else
      if s1.[n] = s2.[n] then similarity_shape (n+1) s1 s2
      else n
  in
(*  let rec match_shape (opt:int option) goals : bool =
    (* when [opt] is [Some n] then it means [goals] starts with a goal g
       which is already claimed to be associated by the former goal h.
       We return a boolean which is true when that first goal g was also
       claimed by the next goal, with a proximity measure larger than n,
       meaning that the former goal h cannot associate with g
    *)
    match goals with
      | [] -> false
      | (si,New_goal i)::rem ->
          begin match rem with
            | [] -> false
            | (_,New_goal _)::_ ->
                let (_:bool) = match_shape None rem in false
            | (sh,Old_goal h)::_ ->
                try_associate si i sh h opt rem
          end
      | (sh,Old_goal h)::rem ->
          begin match rem with
            | [] -> false
            | (_,Old_goal _)::_ ->
                let (_:bool) = match_shape None rem in false
            | (si,New_goal i)::_ ->
                try_associate si i sh h opt rem
          end
  and try_associate si i sh h opt rem =
    let n = similarity_shape 0 si sh in
    eprintf "[Merge] try_associate: claiming similarity %d for new shape@\n%s@\nand old shape@\n%s@." n si sh;
    if (match opt with
      | None ->
          eprintf "[Merge] try_associate: no previous claim@.";
          true
      | Some m ->
          eprintf "[Merge] try_associate: previous claim was %d@." m;
          m < n)
    then
      (* try to associate i with h *)
      let b = match_shape (Some n) rem in
      if b then
        begin
          (* h or i was already paired in rem *)
          eprintf "[Merge] try_associate: failed because claimed further@.";
          false
        end
      else
        begin
          eprintf "[Merge] try_associate: succeeded to associate new goal@\n%s@\nwith old goal@\n%s@." si sh;
          associate_goals ~obsolete:true i h;
          true
        end
    else
      (* no need to try to associate i with h *)
      begin
        eprintf "[Merge] try_associate: no claim further attempted@.";
        let (_:bool) = match_shape None rem in
        false
      end
  in
  let (_:bool) = match_shape None sort_by_shape in
*)
  let rec match_shape (min:int) goals : bool * (string * any_goal) list =
    (* try to associate in [goals] each pair of old and new goal whose
       similarity is at least [min]. Returns a pair [(b,rem)] where
       [rem] is the sublist of [goals] made of goals which have not
       been paired, and [b] is a boolean telling that the head of
       [rem] is the same has the head of [goals] *)
    match goals with
      | [] -> (true, goals)
      | ((si,New_goal i) as hd)::rem ->
          begin match rem with
            | [] -> (true, goals)
            | (_,New_goal _)::_ ->
                let (b,rem2) = match_shape min rem in
                if b then
                  (true, hd::rem2)
                else
                  match_shape min (hd::rem2)
            | (sh,Old_goal h)::_ ->
                try_associate min si i sh h hd rem
          end
      | ((sh,Old_goal h) as hd)::rem ->
          begin match rem with
            | [] -> (true, goals)
            | (_,Old_goal _)::_ ->
                let (b,rem2) = match_shape min rem in
                if b then
                  (true, hd::rem2)
                else
                  match_shape min (hd::rem2)
            | (si,New_goal i)::_ ->
                try_associate min si i sh h hd rem
          end
  and try_associate min si i sh h hd rem =
    let n = similarity_shape 0 si sh in
(*
    eprintf "[Merge] try_associate: claiming similarity %d for new shape@\n%s@\nand old shape@\n%s@." n si sh;
*)
    if n < min then
      begin
(*
        eprintf "[Merge] try_associate: claiming dropped because similarity lower than min = %d@." min;
*)
        let (b,rem2) = match_shape min rem in
        if b then
          (true, hd::rem2)
        else
          match_shape min (hd::rem2)
      end
    else
      match match_shape n rem with
        | false, rem2 ->
            eprintf "[Merge] try_associate: claiming dropped because head was consumed by larger similarity@.";
            match_shape min (hd::rem2)
        | true, [] -> assert false
        | true, _::rem2 ->
(*
            eprintf "[Merge] try_associate: claiming succeeded (similarity %d) for new shape@\n%s@\nand old shape@\n%s@." n si sh;
*)
            associate_goals ~obsolete:true i h;
            let (_,rem3) = match_shape min rem2 in
            (false, rem3)
  in
  let (_b,_rem) = match_shape 0 sort_by_shape in
  (*
     Phase 3: we now associate remaining new goals to the remaining
     old goals in the same order as original
  *)
(*
  eprintf "[Merge] phase 3: associate remaining goals@.";
*)
  let remaining_old_goals =
    Hashtbl.fold
      (fun _ g acc -> (g.goal_name,g)::acc)
      old_goals_map
      []
  in
  let remaining_old_goals =
    ref (List.sort (fun (s1,_) (s2,_) -> String.compare s1 s2)
           remaining_old_goals)
  in
  Array.iteri
    (fun i opt ->
       match opt with
         | Some _ -> ()
         | None ->
             match !remaining_old_goals with
               | [] -> ()
               | (_,h) :: rem ->
                   remaining_old_goals := rem;
                   associate_goals ~obsolete:true i h)
    pairing_array;
  let res = ref [] in
  Array.iter
    (fun (i,id,goal_name,g,sum) ->
       res := (id,goal_name,g,sum,shape_array.(i),pairing_array.(i),
               obsolete_array.(i)) :: !res)
    new_goals_array;
  List.rev !res

(**********************************)
(* reload a file                  *)
(**********************************)


let reload_proof obsolete goal pid old_a =
  let p =
    try
      Detected_prover (Util.Mstr.find pid !current_provers)
    with Not_found ->
      eprintf
        "Warning: prover %s appears in database but is not installed.@."
        pid;
      (Undetected_prover pid)
  in
  let old_res = old_a.proof_state in
  let obsolete = obsolete || old_a.proof_obsolete in
  (* eprintf "proof_obsolete : %b@." obsolete; *)
  let a =
    raw_add_external_proof ~obsolete ~timelimit:old_a.timelimit
      ~edit:old_a.edited_as goal p old_res
  in
  !notify_fun (Goal a.proof_goal)

let rec reload_any_goal parent gid gname sum shape t 
    old_goal goal_obsolete =
  let info = get_explanation gid (Task.task_goal_fmla t) in
  let exp = match old_goal with None -> true | Some g -> g.goal_expanded in
  let goal = raw_add_goal parent gname info sum shape (Some t) exp in
  goal.task <- Some t;
  begin
    match old_goal with
      | None -> ()
      | Some g ->
          Hashtbl.iter (reload_proof goal_obsolete goal) g.external_proofs;
          Hashtbl.iter (reload_trans goal_obsolete goal) g.transformations
  end;
  check_goal_proved goal;
  goal


and reload_trans _goal_obsolete goal _ tr =
  let trname = tr.transf.transformation_name in
  let gname = goal.goal_name in
  eprintf "[Reload] transformation %s for goal %s @\n" trname gname;
  let mtr = raw_add_transformation goal tr.transf tr.transf_expanded in
  let callback subgoals =
    let goals = associate_subgoals gname tr.subgoals subgoals in
    let goals = List.fold_left
      (fun acc (id,subgoal_name,subtask,sum,shape,old_g,subgoal_obsolete) ->
         let mg =
           reload_any_goal (Parent_transf mtr) id
             subgoal_name sum shape subtask old_g subgoal_obsolete
         in mg::acc)
      [] goals
    in
    mtr.subgoals <- (List.rev goals);
    check_transf_proved mtr
  in
  apply_transformation ~callback tr.transf (get_task goal)

exception OutdatedSession
let found_obsolete = ref false

(* reloads the task [t] in theory mth (named tname) *)
let reload_root_goal ~allow_obsolete mth tname old_goals t : goal =
  let id = (Task.task_goal t).Decl.pr_name in
  let gname = id.Ident.id_string in
  let sum = Termcode.task_checksum t in
  let old_goal, goal_obsolete =
    try
      let old_goal = Util.Mstr.find gname old_goals in
      let old_sum = old_goal.checksum in
      (Some old_goal,sum <> old_sum)
    with Not_found -> (None,false)
  in
  if goal_obsolete then
    begin
      eprintf "[Reload] Goal %s.%s has changed@\n" tname gname;
      if allow_obsolete then
        found_obsolete := true
      else
        raise OutdatedSession
    end;
  reload_any_goal (Parent_theory mth) id gname sum "" t old_goal goal_obsolete

(* reloads a theory *)
let reload_theory ~allow_obsolete mfile old_theories (_,tname,th) =
  eprintf "[Reload] theory '%s'@\n"tname;
  let tasks = List.rev (Task.split_theory th None None) in
  let old_goals, old_exp =
    try
      let old_mth = Util.Mstr.find tname old_theories in
      old_mth.goals, old_mth.theory_expanded
    with Not_found -> [], true
  in
  let mth = raw_add_theory mfile (Some th) tname old_exp in
  let goalsmap = List.fold_left
    (fun goalsmap g -> Util.Mstr.add g.goal_name g goalsmap)
    Util.Mstr.empty old_goals
  in
  !notify_fun (Theory mth);
  let new_goals = List.fold_left
    (fun acc t ->
       let g = reload_root_goal ~allow_obsolete mth tname goalsmap t in
       g::acc)
    [] tasks
  in
  mth.goals <- List.rev new_goals;
  check_theory_proved mth;
  mth


(* reloads a file *)
let reload_file ~allow_obsolete mf theories =
  let new_mf = raw_add_file mf.file_name mf.file_expanded in
  let old_theories = List.fold_left
    (fun acc t -> Util.Mstr.add t.theory_name t acc)
    Util.Mstr.empty
    mf.theories
  in
  !notify_fun (File new_mf);
  let mths = List.fold_left
    (fun acc th -> reload_theory ~allow_obsolete new_mf old_theories th :: acc)
    [] theories
  in
  new_mf.theories <- List.rev mths;
  check_file_verified new_mf


(* reloads all files *)
let reload_all allow_obsolete =
  let files = !all_files in
  let all_theories =
    List.map (fun mf ->
                eprintf "[Reload] file '%s'@\n" mf.file_name;
                (mf,read_file mf.file_name))
      files
  in
  all_files := [];
  O.reset ();
  found_obsolete := false;
  List.iter (fun (mf,ths) -> reload_file ~allow_obsolete mf ths) all_theories;
  !found_obsolete

(****************************)
(*     session opening      *)
(****************************)

let bool_attribute field r def =
  try
    match List.assoc field r.Xml.attributes with
      | "true" -> true
      | "false" -> false
      | _ -> assert false
  with Not_found -> def

let int_attribute field r def =
  try
    int_of_string (List.assoc field r.Xml.attributes)
  with Not_found | Invalid_argument _ -> def

let string_attribute_def field r def=
  try
    List.assoc field r.Xml.attributes
  with Not_found -> def

let string_attribute field r =
  try
    List.assoc field r.Xml.attributes
  with Not_found ->
    eprintf "[Error] missing required attribute '%s' from element '%s'@."
      field r.Xml.name;
    assert false

let load_result r =
  match r.Xml.name with
    | "result" ->
        let status = string_attribute "status" r in
        let answer =
          match status with
            | "valid" -> Call_provers.Valid
            | "invalid" -> Call_provers.Invalid
            | "unknown" -> Call_provers.Unknown ""
            | "timeout" -> Call_provers.Timeout
            | "failure" -> Call_provers.Failure ""
            | "highfailure" -> Call_provers.Failure ""
            | s ->
                eprintf
                  "[Warning] Session.load_result: unexpected status '%s'@." s;
                Call_provers.Failure ""
        in
        let time =
          try float_of_string (List.assoc "time" r.Xml.attributes)
          with Not_found -> 0.0
        in
        Done {
          Call_provers.pr_answer = answer;
          Call_provers.pr_time = time;
          Call_provers.pr_output = "";
        }
    | "undone" -> Undone
    | "unedited" -> Unedited
    | s ->
        eprintf "[Warning] Session.load_result: unexpected element '%s'@." s;
        Undone

let rec load_goal ~env ~old_provers parent acc g =
  match g.Xml.name with
    | "goal" ->
        let gname = string_attribute "name" g in
        let expl =
          try Some (List.assoc "expl" g.Xml.attributes)
          with Not_found -> None
        in
        let sum = string_attribute_def "sum" g "" in
        let shape = string_attribute_def "shape" g "" in
        let exp = bool_attribute "expanded" g true in
        let mg = raw_add_goal parent gname expl sum shape None exp in
        List.iter (load_proof_or_transf ~env ~old_provers mg) g.Xml.elements;
        mg::acc
    | s ->
        eprintf "[Warning] Session.load_goal: unexpected element '%s'@." s;
        acc

and load_proof_or_transf ~env ~old_provers mg a =
  match a.Xml.name with
    | "proof" ->
        let prover = string_attribute "prover" a in
        let prover_obsolete,p =
          try
            let p = Util.Mstr.find prover !current_provers in
            try
              let (n,v) = Util.Mstr.find prover old_provers in
              (p.prover_name <> n || p.prover_version <> v), Detected_prover p
            with Not_found ->
              true, Detected_prover p
          with Not_found ->
            true, Undetected_prover prover
        in
        let res = match a.Xml.elements with
          | [r] -> load_result r
          | [] -> Undone
          | _ -> assert false
        in
        let edit = string_attribute "edited" a in
        let obsolete = bool_attribute "obsolete" a true in
        let obsolete = obsolete || prover_obsolete in
        let timelimit = int_attribute "timelimit" a 10 in
        let (_ : proof_attempt) =
          raw_add_external_proof ~obsolete ~timelimit ~edit mg p res
        in
        (* already done by raw_add_external_proof
           Hashtbl.add mg.external_proofs prover pa *)
        ()
    | "transf" ->
        let trname = string_attribute "name" a in
        let tr =
          try
            lookup_transformation env trname
          with Not_found -> assert false (* TODO *)
        in
        let exp = bool_attribute "expanded" a true in
        let mtr = raw_add_transformation mg tr exp in
        mtr.subgoals <-
          List.rev
          (List.fold_left
             (load_goal ~env ~old_provers (Parent_transf mtr))
             [] a.Xml.elements);
        (* already done by raw_add_transformation
           Hashtbl.add mg.transformations trname mtr *)
        ()
    | s ->
        eprintf
          "[Warning] Session.load_proof_or_transf: unexpected element '%s'@."
          s

let load_theory ~env ~old_provers mf acc th =
  match th.Xml.name with
    | "theory" ->
        let thname = string_attribute "name" th in
        let exp = bool_attribute "expanded" th true in
        let mth = raw_add_theory mf None thname exp in
        mth.goals <-
          List.rev
          (List.fold_left
             (load_goal ~env ~old_provers (Parent_theory mth))
             [] th.Xml.elements);
        mth::acc
    | s ->
        eprintf "[Warning] Session.load_theory: unexpected element '%s'@." s;
        acc

let load_file ~env old_provers f =
  match f.Xml.name with
    | "file" ->
        let fn = string_attribute "name" f in
        let exp = bool_attribute "expanded" f true in
        let mf = raw_add_file fn exp in
        mf.theories <-
          List.rev
          (List.fold_left (load_theory ~env ~old_provers mf) [] f.Xml.elements);
        old_provers
    | "prover" ->
        let id = string_attribute "id" f in
        let name = string_attribute "name" f in
        let version = string_attribute "version" f in
        begin
          try
            let p = Util.Mstr.find id !current_provers in
            if p.prover_name <> name || p.prover_version <> version then
              eprintf
                "[Warning] Database prover id '%s' = '%s %s' but on this computer '%s' = '%s %s'@."
                id name version id p.prover_name p.prover_version
          with Not_found ->
            eprintf
              "[Warning] Database has prover %s (%s %s) which is not available on this computer@."
              id name version;
        end;
        Util.Mstr.add id (name,version) old_provers
    | s ->
        eprintf "[Warning] Session.load_file: unexpected element '%s'@." s;
        old_provers

let load_session ~env xml =
  let cont = xml.Xml.content in
  match cont.Xml.name with
    | "why3session" ->
        let _old_provers =
          List.fold_left (load_file ~env) Util.Mstr.empty cont.Xml.elements
        in ()
    | s ->
        eprintf "[Warning] Session.load_session: unexpected element '%s'@." s

let db_filename = "why3session.xml"

let open_session ~allow_obsolete ~env ~config ~init ~notify dir =
  match !current_env with
    | None ->
        init_fun := init; notify_fun := notify;
        project_dir := dir; current_env := Some env;
        let provers = Whyconf.get_provers config in
        current_provers :=
          Util.Mstr.fold (get_prover_data env) provers Util.Mstr.empty;
        begin try
          let xml =
            Xml.from_file (Filename.concat dir db_filename)
          in
          try
            load_session ~env xml;
            reload_all allow_obsolete
          with Sys_error msg ->
            failwith ("Open session: sys error " ^ msg)
        with
          | Sys_error _msg ->
              (* xml does not exist yet *)
	      false
          | Xml.Parse_error s ->
              Format.eprintf "XML database corrupted, ignored (%s)@." s;
              (* failwith ("Open session: XML database corrupted (%s)@." ^ s) *)
              false
        end
    | _ ->
        eprintf "Session.open_session: session already opened@.";
        assert false

let save_session () =
  match !current_env with
    | Some _ ->
        let f = Filename.concat !project_dir db_filename in
        begin if Sys.file_exists f then
          let b = f ^ ".bak" in
          if Sys.file_exists b then Sys.remove b ;
          Sys.rename f b
        end;
        save f
    | None ->
        eprintf "Session.save_session: no session opened@.";
        assert false

(*****************************************************)
(* method: run a given prover on each unproved goals *)
(*****************************************************)

let redo_external_proof ~timelimit g a =
  (* check that the state is not Scheduled or Running *)
  let previous_result,previous_obs = a.proof_state,a.proof_obsolete in
  if running a then ()
    (* info_window `ERROR "Proof already in progress" *)
  else
    match a.prover with
      | Undetected_prover _ -> ()
      | Detected_prover p ->
        if a.edited_as = "" && p.interactive then
          set_proof_state ~obsolete:false a Unedited
        else begin
          let callback result =
            match result with
              | Interrupted ->
                  set_proof_state ~obsolete:previous_obs a previous_result
              | _ ->
                  set_proof_state ~obsolete:false a result;
          in
          let old = if a.edited_as = "" then None else
            begin
              let f = Filename.concat !project_dir a.edited_as in
              Format.eprintf "Info: proving using edited file %s@." f;
              (Some (open_in f))
            end
          in
          schedule_proof_attempt
            ~debug:false ~timelimit ~memlimit:0
            ?old ~command:p.command ~driver:p.driver
            ~callback
            (get_task g)
        end

let rec prover_on_goal ~timelimit p g =
  let id = p.prover_id in
  let a =
    try Hashtbl.find g.external_proofs id
    with Not_found ->
      raw_add_external_proof ~obsolete:false ~timelimit ~edit:"" g
        (Detected_prover p) Undone
  in
  let () = redo_external_proof ~timelimit g a in
  Hashtbl.iter
    (fun _ t -> List.iter (prover_on_goal ~timelimit p) t.subgoals)
    g.transformations

let rec prover_on_goal_or_children ~context_unproved_goals_only ~timelimit p g =
  if not (g.proved && context_unproved_goals_only) then
    begin
      let r = ref true in
      Hashtbl.iter
        (fun _ t ->
           r := false;
           List.iter (prover_on_goal_or_children
                        ~context_unproved_goals_only ~timelimit p)
             t.subgoals) g.transformations;
      if !r then prover_on_goal ~timelimit p g
    end

let run_prover ~context_unproved_goals_only ~timelimit pr a =
  match a with
    | Goal g ->
        prover_on_goal_or_children ~context_unproved_goals_only ~timelimit pr g
    | Theory th ->
        List.iter
          (prover_on_goal_or_children ~context_unproved_goals_only ~timelimit pr)
          th.goals
    | File file ->
        List.iter
          (fun th ->
             List.iter
               (prover_on_goal_or_children ~context_unproved_goals_only ~timelimit pr)
               th.goals)
          file.theories
    | Proof_attempt a ->
        prover_on_goal_or_children ~context_unproved_goals_only ~timelimit pr a.proof_goal
    | Transformation tr ->
        List.iter
          (prover_on_goal_or_children ~context_unproved_goals_only ~timelimit pr)
          tr.subgoals

(**********************************)
(* method: replay obsolete proofs *)
(**********************************)

let proof_successful a =
  match a.proof_state with
    | Done { Call_provers.pr_answer = Call_provers.Valid } -> true
    | _ -> false

let rec replay_on_goal_or_children ~obsolete_only ~context_unproved_goals_only g =
  Hashtbl.iter
    (fun _ a ->
       if not obsolete_only || a.proof_obsolete then
         if not context_unproved_goals_only || proof_successful a
         then redo_external_proof ~timelimit:a.timelimit g a)
    g.external_proofs;
  Hashtbl.iter
    (fun _ t ->
       List.iter
         (replay_on_goal_or_children ~obsolete_only ~context_unproved_goals_only)
         t.subgoals)
    g.transformations

let replay ~obsolete_only ~context_unproved_goals_only a =
  match a with
    | Goal g ->
        replay_on_goal_or_children ~obsolete_only ~context_unproved_goals_only g
    | Theory th ->
        List.iter
          (replay_on_goal_or_children ~obsolete_only ~context_unproved_goals_only)
          th.goals
    | File file ->
        List.iter
          (fun th ->
             List.iter
               (replay_on_goal_or_children ~obsolete_only ~context_unproved_goals_only)
               th.goals)
          file.theories
    | Proof_attempt a ->
        replay_on_goal_or_children ~obsolete_only ~context_unproved_goals_only a.proof_goal
    | Transformation tr ->
        List.iter
          (replay_on_goal_or_children ~obsolete_only ~context_unproved_goals_only)
          tr.subgoals

(***********************************)
(* method: mark proofs as obsolete *)
(***********************************)

let cancel_proof a = set_proof_state ~obsolete:true a a.proof_state

let rec cancel_goal_or_children g =
  Hashtbl.iter (fun _ a -> cancel_proof a) g.external_proofs;
  Hashtbl.iter
    (fun _ t -> List.iter cancel_goal_or_children t.subgoals)
    g.transformations

let cancel a =
  match a with
    | Goal g ->
        cancel_goal_or_children g
    | Theory th ->
        List.iter cancel_goal_or_children th.goals
    | File file ->
        List.iter
          (fun th -> List.iter cancel_goal_or_children th.goals)
          file.theories
    | Proof_attempt a ->
        cancel_goal_or_children a.proof_goal
    | Transformation tr ->
        List.iter cancel_goal_or_children tr.subgoals

(*********************************)
(* method: check existing proofs *)
(*********************************)

type report =
  | Wrong_result of Call_provers.prover_result * Call_provers.prover_result
  | CallFailed of exn
  | Prover_not_installed
  | No_former_result

let reports = ref []

let push_report g p r =
  reports := (g.goal_name,p,r) :: !reports

let proofs_to_do = ref 0
let proofs_done = ref 0

let same_result r1 r2 =
  match r1.Call_provers.pr_answer, r2.Call_provers.pr_answer with
    | Call_provers.Valid, Call_provers.Valid -> true
    | Call_provers.Invalid, Call_provers.Invalid -> true
    | Call_provers.Timeout, Call_provers.Timeout -> true
    | Call_provers.Unknown _, Call_provers.Unknown _-> true
    | Call_provers.Failure _, Call_provers.Failure _-> true
    | _ -> false

let check_external_proof g a =
  (* check that the state is not Scheduled or Running *)
  if running a then ()
  else
    begin
      incr proofs_to_do;
      match a.prover with
        | Undetected_prover s ->
            push_report g s Prover_not_installed;
            incr proofs_done;
            set_proof_state ~obsolete:false a Undone
        | Detected_prover p ->
            let p_name = p.prover_name ^ " " ^ p.prover_version in
            let callback result =
              match result with
                | Scheduled | Running | Interrupted -> ()
                | Undone | Unedited -> assert false
                | InternalFailure msg ->
                    push_report g p_name (CallFailed msg);
                    incr proofs_done;
                    set_proof_state ~obsolete:false a result
                | Done new_res ->
                    begin
                      match a.proof_state with
                        | Done old_res ->
                            if same_result old_res new_res then () else
                              push_report g p_name (Wrong_result(new_res,old_res))
                        | _ ->
                            push_report g p_name No_former_result
                    end;
                    incr proofs_done;
                    set_proof_state ~obsolete:false a result
          in
          let old = if a.edited_as = "" then None else
            begin
              let f = Filename.concat !project_dir a.edited_as in
              (* Format.eprintf "Info: proving using edited file %s@." f; *)
              (Some (open_in f))
            end
          in
          schedule_proof_attempt
            ~debug:false ~timelimit:a.timelimit ~memlimit:0
            ?old ~command:p.command ~driver:p.driver
            ~callback
            (get_task g)
    end

let rec check_goal_and_children g =
  Hashtbl.iter (fun _ a -> check_external_proof g a) g.external_proofs;
  Hashtbl.iter
    (fun _ t ->
       List.iter check_goal_and_children t.subgoals)
    g.transformations

let check_all ~callback =
  reports := [];
  proofs_to_do := 0;
  proofs_done := 0;
  List.iter
    (fun file ->
       List.iter
         (fun th -> List.iter check_goal_and_children th.goals)
         file.theories)
    !all_files;
  let timeout () =
(*
    Printf.eprintf "Progress: %d/%d\r%!" !proofs_done !proofs_to_do;
*)
    if !proofs_done = !proofs_to_do then
      begin
(*
        Printf.eprintf "\n%!";
*)
        decr maximum_running_proofs;
        callback !reports;
        false
      end
    else true
  in
  incr maximum_running_proofs;
  schedule_any_timeout timeout

(*****************************************************)
(* method: split selected goals *)
(*****************************************************)

let task_checksum t =
  fprintf str_formatter "%a@." Pretty.print_task t;
  let s = flush_str_formatter () in
(*
  let tmp = Filename.temp_file "task" "out" in
  let c = open_out tmp in
  output_string c s;
  close_out c;
*)
  let sum = Digest.to_hex (Digest.string s) in
(*
  eprintf "task %s, sum = %s@." tmp sum;
*)
  sum

let transformation_on_goal g tr =
    let callback subgoals =
      let b =
         match subgoals with
          | [task] ->
              (* let s1 = task_checksum (get_task g) in *)
              (* let s2 = task_checksum task in *)
              (* (\* *)
              (*   eprintf "Transformation returned only one task. sum before = %s, sum after = %s@." (task_checksum g.task) (task_checksum task); *)
              (*   eprintf "addresses: %x %x@." (Obj.magic g.task) (Obj.magic task); *)
              (* *\) *)
              (* s1 <> s2 *)
              not (Task.task_equal task (get_task g))
          | _ -> true
      in
      if b then
        let tr = raw_add_transformation g tr true in
        let goal_name = g.goal_name in
        let fold =
          fun (acc,count) subtask ->
            let id = (Task.task_goal subtask).Decl.pr_name in
            let expl =
              get_explanation id (Task.task_goal_fmla subtask)
            in
            let subgoal_name =
              goal_name ^ "." ^ (string_of_int count)
            in
            let goal =
              raw_add_goal (Parent_transf tr)
                subgoal_name expl "" "" (Some subtask) true
            in
            (goal :: acc, count+1)
        in
        let goals,_ =
          List.fold_left fold ([],1) subgoals
        in
        tr.subgoals <- List.rev goals
    in
    apply_transformation ~callback tr (get_task g)

let rec transform_goal_or_children ~context_unproved_goals_only tr g =
  if not (g.proved && context_unproved_goals_only) then
    begin
      let r = ref true in
      Hashtbl.iter
        (fun _ t ->
           r := false;
           List.iter
             (transform_goal_or_children ~context_unproved_goals_only tr)
             t.subgoals)
        g.transformations;
      if !r then
        schedule_delayed_action (fun () -> transformation_on_goal g tr)
    end


let transform ~context_unproved_goals_only tr a =
  let tr = transform_goal_or_children ~context_unproved_goals_only tr in
  match a with
    | Goal g -> tr g
    | Theory th -> List.iter tr th.goals
    | File file ->
        List.iter
          (fun th -> List.iter tr th.goals)
          file.theories
    | Proof_attempt a -> tr a.proof_goal
    | Transformation t -> List.iter tr t.subgoals



(*****************************)
(* method: edit current goal *)
(*****************************)


let ft_of_th th =
  let fn = Filename.basename th.theory_parent.file_name in
  let fn = try Filename.chop_extension fn with Invalid_argument _ -> fn in
  (fn, (* th.theory.Theory.th_name.Ident.id_string *) th.theory_name)

let rec ft_of_goal g =
  match g.parent with
    | Parent_transf tr -> ft_of_goal tr.parent_goal
    | Parent_theory th -> ft_of_th th

let ft_of_pa a =
  ft_of_goal a.proof_goal

let edit_proof ~default_editor ~project_dir a =
  (* check that the state is not Scheduled or Running *)
  if running a then ()
(*
    info_window `ERROR "Edition already in progress"
*)
  else
    match a.prover with
      | Undetected_prover _ -> ()
      | Detected_prover p ->
          let g = a.proof_goal in
          let t = (get_task g) in
          let driver = p.driver in
          let file =
            match a.edited_as with
              | "" ->
                  let (fn,tn) = ft_of_pa a in
                  let file = Driver.file_of_task driver fn tn t in
                  let file = Filename.concat project_dir file in
                  (* Uniquify the filename if it exists on disk *)
                  let i =
                    try String.rindex file '.'
                    with _ -> String.length file
                  in
                  let name = String.sub file 0 i in
                  let ext = String.sub file i (String.length file - i) in
                  let i = ref 1 in
                  while Sys.file_exists
                    (name ^ "_" ^ (string_of_int !i) ^ ext) do
                      incr i
                  done;
                  let file = name ^ "_" ^ (string_of_int !i) ^ ext in
                  let file = Sysutil.relativize_filename project_dir file in
                  a.edited_as <- file;
                  if a.proof_state = Unedited then a.proof_state <- Undone;
                  file
              | f -> f
          in
          let file = Filename.concat project_dir file in
          let old_res = a.proof_state in
          let callback res =
            match res with
              | Done _ ->
                  set_proof_state ~obsolete:true a old_res
              | _ ->
                  set_proof_state ~obsolete:false a res
          in
          let editor =
            match p.editor with
              | "" -> default_editor
              | s -> s
          in
          (*
            eprintf "[Editing] goal %s with command %s %s@." g.Decl.pr_name.id_string editor file;
          *)
          eprintf "[Editing] goal %s with command %s %s@." (Task.task_goal t).Decl.pr_name.Ident.id_string editor file;
          schedule_edit_proof ~debug:false ~editor
            ~file
            ~driver
            ~callback
            t

(*************)
(* removing  *)
(*************)

let remove_proof_attempt a =
  O.remove a.proof_key;
  let g = a.proof_goal in
  Hashtbl.remove g.external_proofs (prover_id a.prover);
  check_goal_proved g

let remove_transformation t =
  O.remove t.transf_key;
  let g = t.parent_goal in
  Hashtbl.remove g.transformations t.transf.transformation_name;
  check_goal_proved g

let rec clean_goal g =
  if g.proved then
    begin
      Hashtbl.iter
        (fun _ a ->
           if a.proof_obsolete || not (proof_successful a) then
             remove_proof_attempt a)
        g.external_proofs;
      Hashtbl.iter
        (fun _ t ->
           if not t.transf_proved then
             remove_transformation t
           else
             List.iter clean_goal t.subgoals)
        g.transformations
    end
  else
    Hashtbl.iter
      (fun _ t -> List.iter clean_goal t.subgoals)
      g.transformations


let clean a =
  match a with
    | Goal g -> clean_goal g
    | Theory th -> List.iter clean_goal th.goals
    | File file ->
        List.iter
          (fun th ->
             List.iter clean_goal th.goals)
          file.theories
    | Proof_attempt a ->
        clean_goal a.proof_goal
    | Transformation tr ->
        List.iter clean_goal tr.subgoals

end

(*
Local Variables:
compile-command: "unset LANG; make -C ../.. bin/why3ide.byte"
End:
*)
