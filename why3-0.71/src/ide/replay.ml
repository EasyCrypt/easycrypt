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


let includes = ref []
let file = ref None
let opt_version = ref false
let opt_stats = ref true
let opt_latex = ref ""
let opt_latex2 = ref ""
let opt_html = ref ""
let opt_force = ref false

let spec = Arg.align [
  ("-I",
   Arg.String (fun s -> includes := s :: !includes),
   "<s> add s to loadpath") ;
  ("-force",
   Arg.Set opt_force,
   " enforce saving of session even if replay failed") ;
  ("-s",
   Arg.Clear opt_stats,
   " do not print statistics") ;
  ("-v",
   Arg.Set opt_version,
   " print version information") ;
  ("-latex",
   Arg.Set_string opt_latex,
   " [Dir_output] produce latex statistics") ;
  ("-latex2",
   Arg.Set_string opt_latex2,
   " [Dir_output] produce latex statistics") ;
  ("-html",
   Arg.Set_string opt_html,
   " [Dir_output] produce html statistics") ;
]

let version_msg = Format.sprintf "Why3 replayer, version %s (build date: %s)"
  Config.version Config.builddate

let usage_str = Format.sprintf
  "Usage: %s [options] [<file.why>|<project directory>]"
  (Filename.basename Sys.argv.(0))

let set_file f = match !file with
  | Some _ ->
      raise (Arg.Bad "only one parameter")
  | None ->
      file := Some f

let () = Arg.parse spec set_file usage_str

let () =
  if !opt_version then begin
    Format.printf "%s@." version_msg;
    exit 0
  end

let fname = match !file with
  | None ->
      Arg.usage spec usage_str;
      exit 1
  | Some f ->
      f

let config = Whyconf.read_config None

let loadpath = (Whyconf.loadpath (Whyconf.get_main config))
  @ List.rev !includes

let env = Env.create_env loadpath

let provers = Whyconf.get_provers config

let provers =
  Util.Mstr.fold (Session.get_prover_data env) provers Util.Mstr.empty

let usleep t = ignore (Unix.select [] [] [] t)


let idle_handler = ref None
let timeout_handler = ref None

module M = Session.Make
  (struct
     type key = int

     let create ?parent () =
       match parent with
         | None -> 0
         | Some  n -> n+1

     let remove _row = ()

     let reset () = ()

     let idle f =
       match !idle_handler with
         | None -> idle_handler := Some f;
         | Some _ -> failwith "Replay.idle: already one handler installed"

     let timeout ~ms f =
       match !timeout_handler with
         | None -> timeout_handler := Some(float ms /. 1000.0 ,f);
         | Some _ -> failwith "Replay.timeout: already one handler installed"

     let notify_timer_state w s r =
       Printf.eprintf "Progress: %d/%d/%d   \r%!" w s r

   end)


let main_loop () =
  let last = ref (Unix.gettimeofday ()) in
  while true do
    let time = Unix.gettimeofday () -. !last in
    (* attempt to run timeout handler *)
    let timeout =
      match !timeout_handler with
        | None -> false
        | Some(ms,f) ->
            if time > ms then
              let b = f () in
              if b then true else
                begin
                  timeout_handler := None;
                  true
                end
            else false
    in
    if timeout then
      last := Unix.gettimeofday ()
    else
      (* attempt to run the idle handler *)
      match !idle_handler with
        | None ->
            begin
              let ms =
                match !timeout_handler with
                  | None -> 100.0 (* raise Exit *)
                  | Some(ms,_) -> ms
              in
              usleep (ms -. time)
            end
        | Some f ->
            let b = f () in
            if b then () else
              begin
                idle_handler := None;
              end
  done

open Format

(*
let model_index = Hashtbl.create 257
*)

let init =
(*
  let cpt = ref 0 in
*)
  fun _row any ->
(*
    incr cpt;
    Hashtbl.add model_index !cpt any;
*)
    let _name =
      match any with
        | M.Goal g -> M.goal_expl g
        | M.Theory th -> M.theory_name th
        | M.File f -> Filename.basename f.M.file_name
        | M.Proof_attempt a ->
            begin
              match a.M.prover with
                | M.Detected_prover p ->
                    p.Session.prover_name ^ " " ^ p.Session.prover_version
                | M.Undetected_prover s -> s
            end
        | M.Transformation tr -> Session.transformation_id tr.M.transf
    in
    (* eprintf "Item '%s' loaded@." name *)
    ()

(*
let string_of_result result =
  match result with
    | Session.Undone -> "undone"
    | Session.Scheduled -> "scheduled"
    | Session.Running -> "running"
    | Session.InternalFailure _ -> "internal failure"
    | Session.Done r -> match r.Call_provers.pr_answer with
        | Call_provers.Valid -> "valid"
        | Call_provers.Invalid -> "invalid"
        | Call_provers.Timeout -> "timeout"
        | Call_provers.Unknown _ -> "unknown"
        | Call_provers.Failure _ -> "failure"
        | Call_provers.HighFailure -> "high failure"

let print_result fmt res =
  let t = match res with
    | Session.Done { Call_provers.pr_time = time } ->
        Format.sprintf "(%.1f)" time
    | _ -> ""
  in
  fprintf fmt "%s%s" (string_of_result res) t
*)


let print_result fmt
    {Call_provers.pr_answer=ans; Call_provers.pr_output=out;
     Call_provers.pr_time=_t} =
(*
  fprintf fmt "%a (%.1fs)" Call_provers.print_prover_answer ans t;
*)
  fprintf fmt "%a" Call_provers.print_prover_answer ans;
  if ans == Call_provers.HighFailure then
    fprintf fmt "@\nProver output:@\n%s@." out

let notify _any = ()
(*
  match any with
    | M.Goal g ->
        printf "Goal '%s' proved: %b@." (M.goal_expl g) (M.goal_proved g)
    | M.Theory th ->
        printf "Theory '%s' verified: %b@." (M.theory_name th) (M.verified th)
    | M.File file ->
        printf "File '%s' verified: %b@." (Filename.basename file.M.file_name)
          file.M.file_verified
    | M.Proof_attempt a ->
        let p = a.M.prover in
        printf "Proof with '%s %s' gives %a@."
          p.Session.prover_name p.Session.prover_version
          print_result a.M.proof_state
    | M.Transformation tr ->
        printf "Transformation '%s' proved: %b@."
          (Session.transformation_id tr.M.transf) tr.M.transf_proved
*)

let project_dir =
  if Sys.file_exists fname then
    begin
      if Sys.is_directory fname then
        begin
          eprintf "Info: found directory '%s' for the project@." fname;
          fname
        end
      else
        begin
          eprintf "Info: found regular file '%s'@." fname;
          let d =
            try Filename.chop_extension fname
            with Invalid_argument _ -> fname
          in
          eprintf "Info: using '%s' as directory for the project@." d;
          d
        end
    end
  else
    failwith "file does not exist"

let goal_statistics (goals,n,m) g =
  if M.goal_proved g then (goals,n+1,m+1) else (g::goals,n,m+1)

let theory_statistics (ths,n,m) th =
  let goals,n1,m1 = List.fold_left goal_statistics ([],0,0) (M.goals th) in
  ((th,goals,n1,m1)::ths,n+n1,m+m1)

let file_statistics (files,n,m) f =
  let ths,n1,m1 = List.fold_left theory_statistics ([],0,0) f.M.theories in
  ((f,ths,n1,m1)::files,n+n1,m+m1)

let print_statistics files =
  List.iter
    (fun (f,ths,n,m) ->
       if n<m then
         begin
           printf "   +--file %s: %d/%d@." f.M.file_name n m;
           List.iter
             (fun (th,goals,n,m) ->
                if n<m then
                  begin
                    printf "      +--theory %s: %d/%d@."
                      (M.theory_name th) n m;
                    List.iter
                      (fun g ->
                         printf "         +--goal %s not proved@." (M.goal_name g))
                      (List.rev goals)
                  end)
             (List.rev ths)
         end)
    (List.rev files)

(* Statistics in LaTeX*)

let rec transf_depth tr =
  List.fold_left (fun depth g -> max depth (goal_depth g)) 0 (tr.M.subgoals)
and goal_depth g =
  Hashtbl.fold
    (fun _st tr depth -> max depth (1 + transf_depth tr)) (M.transformations g) 0

let theory_depth t =
  List.fold_left (fun depth g -> max depth (goal_depth g)) 0 (M.goals t)

let rec provers_latex_stats provers g =
  let proofs = M.external_proofs g in
  Hashtbl.iter (fun p a-> Hashtbl.replace provers p a.M.prover) proofs;
  let tr = M.transformations g in
  Hashtbl.iter (fun _st tr ->
    let goals = tr.M.subgoals in
    List.iter (provers_latex_stats provers) goals) tr

let prover_name a =
  match a with
      M.Detected_prover d -> d.Session.prover_name ^ " " ^ d.Session.prover_version
    | M.Undetected_prover s -> s

let protect s =
  let b = Buffer.create 7 in
  for i = 0 to String.length s - 1 do
    match s.[i] with
	'_' -> Buffer.add_string b "\\_"
      | c -> Buffer.add_char b c
  done;
  Buffer.contents b

let rec goal_latex_stat n fmt prov depth depth_max column subgoal g =
  if n == 1 then
    begin
      if depth > 0 then
	if subgoal > 0 then
	  fprintf fmt "\\cline{%d-%d} @." (depth + 1) column
	else ()
      else
	fprintf fmt "\\hline @.";
    end
  else
    begin
      if depth > 0 then
	fprintf fmt "\\cline{%d-%d} @." 2 column
      else
	fprintf fmt "\\hline @."
    end;
  if(n ==1) then
    begin
      if depth_max > 1 then
	begin
	  if subgoal > 0 then
	    begin
	      if(depth < depth_max)  then
		for i = 1 to depth do fprintf fmt "\\explanation{%s}& \\explanation{%s}" " " " "done
	      else
		for i = 1 to depth - 1 do fprintf fmt "\\explanation{%s}& \\explanation{%s}" " " " " done
	    end
	  else
	    if(depth < depth_max) then
	      if depth > 0 then fprintf fmt "\\explanation{%s}& \\explanation{%s}" " " " "
	end
      else
	begin
	  if subgoal > 0  then
	    for i = 1 to depth  do fprintf fmt "\\explanation{%s}& \\explanation{%s}" " " " " done
	  else
	    if depth > 0 then fprintf fmt "\\explanation{%s}& \\explanation{%s}" " " " "
	end
    end
  else
    for i = 1 to depth do fprintf fmt "\\quad" done;
  if (depth <= 1) then
    fprintf fmt "\\explanation{%s} " (protect (M.goal_expl g))
  else
    if n == 2 then
      fprintf fmt "\\explanation{%d} " (subgoal + 1)
    else
      fprintf fmt "\\explanation{%s}"  " ";
  let proofs = M.external_proofs g in
  if (Hashtbl.length proofs) > 0 then
    begin
      if (n == 1) then
	begin
	  if depth_max <= 1 then
	    begin
	      if depth > 0 then
		for i = depth to (depth_max - depth) do fprintf fmt "& \\explanation{%s}" " " done
	      else
		for i = depth to (depth_max - depth - 1) do fprintf fmt "& \\explanation{%s}" " " done
	    end
	  else
	      if depth > 0 then
		for i = depth to (depth_max - depth - 1) do fprintf fmt "& \\explanation{%s}" " " done
	      else
		for i = depth to (depth_max - depth - 2) do fprintf fmt "& \\explanation{%s}" " " done
	end;
      List.iter (fun (p, _pr) ->
	try
	  let pr = Hashtbl.find proofs p in
	  let s = pr.M.proof_state in
	  match s with
	      Session.Done res ->
		begin
		  match res.Call_provers.pr_answer with
		      Call_provers.Valid -> fprintf fmt "& \\valid{%.2f} " res.Call_provers.pr_time
		    | Call_provers.Invalid -> fprintf fmt "& \\invalid "
		    | Call_provers.Timeout -> fprintf fmt "& \\timeout "
		    | Call_provers.Unknown _s -> fprintf fmt "& \\unknown "
		    | _ -> fprintf fmt "& \\failure "
		end
	    | _ -> fprintf fmt "& Undone"
	with Not_found -> fprintf fmt "& \\noresult") prov;
    fprintf fmt "\\\\ @."
    end;
  let tr = M.transformations g in
  if Hashtbl.length tr > 0 then
  if n == 2 then 
    begin
      if (Hashtbl.length proofs == 0) then 
	fprintf fmt "& \\multicolumn{%d}{|c|}{}\\\\ @." (List.length prov)
    end
  else
      if Hashtbl.length proofs > 0 then 
	  fprintf fmt "\\cline{%d-%d} @." (depth + 2) column;
  Hashtbl.iter (fun _st tr ->
    let goals = tr.M.subgoals in
    let _ = List.fold_left (fun subgoal g ->
      goal_latex_stat n fmt prov (depth + 1) depth_max column (subgoal) g; subgoal + 1) 0 goals in
    () ) tr


let theory_latex_stat n dir t =
  let provers = Hashtbl.create 9 in
  List.iter (provers_latex_stats provers) (M.goals t);
  let provers = Hashtbl.fold (fun p pr acc -> (p, prover_name pr) :: acc) provers [] in
  let provers =
    List.sort (fun (_p1, n1) (_p2, n2) -> String.compare n1 n2) provers in
  let depth = theory_depth  t in
  let name = M.theory_name t in
  let ch = open_out (Filename.concat dir(name^".tex")) in
  let fmt = formatter_of_out_channel ch in
      fprintf fmt "\\begin{tabular}";
  fprintf fmt "{| l |";
  for i = 0 to (List.length provers) + depth do fprintf fmt "c |" done;
  fprintf fmt "}@.";
  if (n == 1) then
    if (depth > 1) then
      fprintf fmt "\\hline \\multicolumn{%d}{|c|}{Proof obligations } "  depth
      else
      fprintf fmt "\\hline \\multicolumn{%d}{|c|}{Proof obligations } " (depth + 1)
  else
    fprintf fmt "\\hline Proof obligations ";
  List.iter (fun (_, a) -> fprintf fmt "& \\provername{%s} " a) provers;
  fprintf fmt "\\\\ @.";
  let column =
    if n == 1 then
    if depth > 1
    then
      (List.length provers) + depth
    else
      (List.length provers) + depth + 1
    else
      (List.length provers) +  1
  in
  List.iter (goal_latex_stat n fmt provers 0 depth column 0) (M.goals t);
  fprintf fmt "\\hline \\end{tabular}@.";
  close_out ch

let file_latex_stat n dir f =
   List.iter (theory_latex_stat n dir) f.M.theories

let print_latex_statistics n dir =
  let files = M.get_all_files () in
  List.iter (file_latex_stat n dir) files

let print_report (g,p,r) =
  printf "   goal '%s', prover '%s': " g p;
  match r with
  | M.Wrong_result(new_res,old_res) ->
      printf "%a instead of %a@."
        print_result new_res print_result old_res
  | M.No_former_result ->
      printf "no former result available@."
  | M.CallFailed msg ->
      printf "internal failure '%a'@." Exn_printer.exn_printer msg;
  | M.Prover_not_installed ->
      printf "not installed@."

let () =
  try
    eprintf "Opening session...@?";
    let found_obs =
      M.open_session ~allow_obsolete:true
        ~env ~config ~init ~notify project_dir
    in
    if found_obs then
      eprintf "[Warning] session is obsolete@.";
    M.maximum_running_proofs :=
      Whyconf.running_provers_max (Whyconf.get_main config);
    eprintf " done@.";
    if !opt_latex <> "" then print_latex_statistics 1 !opt_latex
    else
    if !opt_latex2 <> "" then print_latex_statistics 2 !opt_latex2
    else
      let callback report =
        eprintf "@.";
	let files,n,m =
          List.fold_left file_statistics ([],0,0) (M.get_all_files ())
	in
      match report with
        | [] ->
            if found_obs then
              if n=m then
                printf " %d/%d (replay OK, all proved: obsolete session updated)@." n m
              else
                if !opt_force then
                  printf " %d/%d (replay OK, but not all proved: obsolete session updated since -force was given)@." n m
                else
                  printf " %d/%d (replay OK, but not all proved: obsolete session NOT updated)@." n m
            else
              printf " %d/%d@." n m ;
            if !opt_stats && n<m then print_statistics files;
            eprintf "Everything replayed OK.@.";
            if found_obs && (n=m || !opt_force) then
              begin
                eprintf "Updating obsolete session...@?";
                M.save_session ();
                eprintf " done@."
              end;
            exit 0
        | _ ->
            printf " %d/%d (replay failed)@." n m ;
            List.iter print_report report;
            eprintf "Replay failed.@.";
            exit 1
    in
    M.check_all ~callback;
    try main_loop ()
    with Exit -> eprintf "main replayer exited unexpectedly@."
  with
    | M.OutdatedSession ->
        eprintf "The session database '%s' is outdated, cannot replay@."
          project_dir;
        eprintf "Aborting...@.";
        exit 1
    | e when not (Debug.test_flag Debug.stack_trace) ->
        eprintf "Error while opening session with database '%s' : %a@."
          project_dir
          Exn_printer.exn_printer e;
        eprintf "Aborting...@.";
        exit 1


(*
Local Variables:
compile-command: "unset LANG; make -C ../.. bin/why3replayer.byte"
End:
*)
