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

open Thread
open Why3
open Util
open Env
open Theory
open Task
open Trans
open Driver
open Call_provers

type tool_id = {
  tool_name : string;
  prover_name : string;
  tool_db : Db.prover_id option;
  }
(* tool_name, prover_name *)

type prob_id = {
  prob_name : string;
  prob_file : string;
  prob_theory : string;
  prob_db : Db.goal option;
}
(* prob_name, file_name, theory name *)

type tool = {
  tval     : tool_id;
  ttrans   : (task trans * (Db.transf_id option)) list;
  tdriver  : driver;
  tcommand : string;
  tenv     : env;
  tuse     : (theory * Db.transf_id option) list;
  ttime    : int;
  tmem     : int;
}

type gen_task = env -> (theory * Db.transf_id option) list ->
    (prob_id * task) list

type prob = {
  ptask  : gen_task;
  (** needed for tenv *)
  ptrans : env -> (task list trans * (Db.transf_id option)) list;
}

type why_result =
  | InternalFailure of exn
  | Done of Db.proof_status * float

type result = {tool   : tool_id;
               prob   : prob_id;
               task   : Decl.prsymbol;
               idtask : int;
               result : why_result}


type proof_attempt_status =
  | Runned of why_result
  | Cached of Db.proof_status * float

open Format

type callback = tool_id -> prob_id ->
    task -> int ->  proof_attempt_status -> unit

let debug_call = Debug.register_flag "call"
let debug = Debug.register_flag "bench_core"


module BenchUtil =
struct

  let print_proof_status fmt = function
    | Db.Done a -> Call_provers.print_prover_answer fmt a
    | Db.Undone -> fprintf fmt "Undone"

  open Worker

(* number of scheduled external proofs *)
  let coef_buf = 10
  let scheduled_proofs = ref 0
  let maximum_running_proofs = ref 2

(* they are protected by a lock *)
  let answers_queue = Queue.create ()
  let queue_lock = Mutex.create ()
  let queue_condition = Condition.create ()

(** Before calling this function queue_lock must be locked *)
  let treat_result () =
    let q_tmp = Queue.create () in
    while not (Queue.is_empty answers_queue) do
      Queue.transfer answers_queue q_tmp;
      Mutex.unlock queue_lock;
      let iter (result,callback) = decr scheduled_proofs; callback (result ())
      in
      Queue.iter iter q_tmp;
      Queue.clear q_tmp;
      Mutex.lock queue_lock
    done

  let yield () =
    Thread.yield ();
    Mutex.lock queue_lock;
    treat_result ();
    Mutex.unlock queue_lock

  (** Wait for the last remaining tasks *)
  let wait_remaining_task () =
    Mutex.lock queue_lock;
    while !scheduled_proofs > 0 do
      while Queue.is_empty answers_queue do
        Condition.wait queue_condition queue_lock
      done;
      treat_result ();
    done;
    Mutex.unlock queue_lock

  let new_external_proof =
    let run_external (call_prover,callback) =
      let r = Call_provers.wait_on_call (call_prover ()) in
      Mutex.lock queue_lock;
      Queue.push (r,callback) answers_queue ;
      Condition.signal queue_condition;
      Mutex.unlock queue_lock in
    let external_workers =
      ManyWorkers.create maximum_running_proofs run_external in
    fun (call_prover,callback) ->
      ManyWorkers.add_work external_workers (call_prover,callback);
      incr scheduled_proofs;
    (** Stop the computation if too many external proof are scheduled *)
      while !scheduled_proofs >= !maximum_running_proofs * coef_buf do
        Mutex.lock queue_lock;
        while Queue.is_empty answers_queue do
          Condition.wait queue_condition queue_lock
        done;
        treat_result ();
        Mutex.unlock queue_lock;
      done


(* from Gmain *)
  let task_checksum t =
    fprintf str_formatter "%a@." Pretty.print_task t;
    let s = flush_str_formatter () in
    Digest.to_hex (Digest.string s)


  let apply_trans (task,db_goal) (trans,db_trans) =
    let task = Trans.apply trans task in
    match db_goal, db_trans with
      | Some db_goal, Some db_trans ->
        let transf = try Db.Htransf.find (Db.transformations db_goal) db_trans
          with Not_found ->
            Db.add_transformation db_goal db_trans
        in
        let md5 = task_checksum task in
        let db_goal =
          try
            Mstr.find md5 (Db.subgoals transf)
          with Not_found ->
            Db.add_subgoal transf
              (Task.task_goal task).Decl.pr_name.Ident.id_string
              md5
        in
        (task,Some db_goal)
      | _ -> ((task:task),None)

  let apply_transl (task,db_goal) (trans,db_trans) =
    let tasks = Trans.apply trans task in
    match db_goal, db_trans with
      | Some db_goal, Some db_trans ->
        let transf = try Db.Htransf.find (Db.transformations db_goal) db_trans
          with Not_found -> Db.add_transformation db_goal db_trans
        in
        let map task =
          let md5 = task_checksum task in
          let db_goal =
            try
              Mstr.find md5 (Db.subgoals transf)
            with Not_found ->
              Db.add_subgoal transf
                (Task.task_goal task).Decl.pr_name.Ident.id_string
                md5
          in
          (task,Some db_goal) in
        List.map map tasks
      | _ -> List.map (fun task -> (task:task),None) tasks


  let rec apply_transll trl acc (task,db_goal) =
    match trl with
      | [] -> (task,db_goal)::acc
      | tr::trl ->
        let tl = apply_transl (task,db_goal) tr in
        List.fold_left (apply_transll trl) acc tl

  let proof_status_to_db_result pr = (Db.Done pr.pr_answer, pr.pr_time)

end


let print_why_result fmt = function
  | InternalFailure exn ->
    Format.fprintf fmt "InternalFailure %a" Exn_printer.exn_printer exn
  | Done (pr,_) -> BenchUtil.print_proof_status fmt pr

let print_pas fmt = function
  | Runned sp -> fprintf fmt "Runned %a" print_why_result sp
  | Cached (p,t) -> fprintf fmt "Cached (%a,%f)"
    BenchUtil.print_proof_status p t

let call callback tool prob =
  (** Prove goal *)
  let db_tool = tool.tval.tool_db in
  let new_external_proof pval i cb task =
    try
      let call_prover : Call_provers.pre_prover_call =
        Driver.prove_task ~timelimit:(tool.ttime) ~memlimit:(tool.tmem)
          ~command:(tool.tcommand) (tool.tdriver) task in
      BenchUtil.new_external_proof (call_prover,cb)
    with e ->
      Format.eprintf "%a@." Exn_printer.exn_printer e;
      callback pval i task (Runned (InternalFailure e)) in
  let call pval i (task,db_goal) =
    match db_goal,db_tool with
      | Some db_goal, Some db_tool ->
        let proof_attempt =
          try
            Db.Hprover.find (Db.external_proofs db_goal) db_tool
          with Not_found ->
            Db.add_proof_attempt db_goal db_tool
        in
        let (proof_status,time,_,_) = Db.status_and_time proof_attempt in
        Debug.dprintf debug "Database has (%a,%f) for the goal@."
          BenchUtil.print_proof_status proof_status time;
        begin
          if proof_status = Db.Done Call_provers.Valid ||
            (proof_status = Db.Done Call_provers.Timeout &&
                time > float tool.ttime)
          then
            callback pval i task (Cached (proof_status,time))
          else
            begin
              Debug.dprintf debug "@.time = %f %i@.@."
                time tool.ttime;
              let cb res =
                let (status,time) = BenchUtil.proof_status_to_db_result res in
                callback pval i task (Runned (Done (status,time)));
                Db.set_status proof_attempt status time
              in
              new_external_proof pval i cb task
            end
        end
      | _ ->
        let cb res =
          let (status,time) = BenchUtil.proof_status_to_db_result res in
          callback pval i task (Runned (Done (status,time))) in
        new_external_proof pval i cb task
  in
  (** Apply trans *)
  let iter_task (pval,task) =
    let translist = prob.ptrans tool.tenv in
    let tasks = BenchUtil.apply_transll translist [] (task,pval.prob_db) in
    let tasks = List.map
      (fun task -> List.fold_left BenchUtil.apply_trans task tool.ttrans)
      tasks
    in
    let iter i task = call pval i task; succ i in
    ignore (List.fold_left iter 0 (List.rev tasks)) in
  (** Split *)
  let ths = prob.ptask tool.tenv tool.tuse in
  List.iter iter_task ths


let general ?(callback=fun _ _ _ _ _ -> ()) iter add =
  Debug.dprintf debug "Start one general@.";
  (** Main worker *)
  (** Start all *)
  iter (fun v tool prob ->
    let cb pval i task res =
      callback tool.tval pval task i res;
      add v {tool = tool.tval; prob = pval;
             task = Task.task_goal task;
             idtask = i;
             result = match res with
               | Runned res -> res
               | Cached (res,time) -> Done (res,time)
            } in
    call cb tool prob);
  BenchUtil.wait_remaining_task ()

let any ?callback toolprob =
  let l = ref [] in
  general ?callback (fun f -> List.iter (fun (t,p) -> f () t p) toolprob)
    (fun () r -> l:=r::!l);
  !l


let all_list_tp ?callback tools probs =
  let l = ref [] in
  general ?callback (fun f ->
    List.iter (fun t -> List.iter (fun p -> f () t p) probs) tools)
    (fun () r -> l:=r::!l);
  !l

let all_list_pt ?callback tools probs =
  let l = ref [] in
  general ?callback (fun f ->
    List.iter (fun p -> List.iter (fun t -> f () t p) tools) probs)
    (fun () r -> l:=r::!l);
  !l

let all_array ?callback tools probs =
  let m = Array.make_matrix (Array.length tools) (Array.length probs)
    [] in
  general ?callback (fun f ->
    Array.iteri (fun i t -> Array.iteri (fun j p -> f (i,j) t p) probs) tools)
    (fun (i,j) r -> m.(i).(j) <- r::m.(i).(j));
  m


let all_list_tools ?callback tools probs =
  let tools = List.map (fun t -> (t, ref [])) tools in
  general ?callback (fun f ->
    List.iter (fun (t,l) -> List.iter (fun p -> f l t p) probs) tools)
    (fun l r -> l:=r::!l);
  List.map (fun (t,l) -> (t.tval,!l)) tools

type output =
  (** on stdout *)
  |Average of string
  |Timeline of string
  (** In a file *)
  |Csv of string

type bench =
    {
      bname  : string;
      btools : tool list;
      bprobs : prob list;
      boutputs : output list;
    }

let run_bench ?callback bench =
  all_list_pt ?callback bench.btools bench.bprobs

let run_benchs ?callback benchs =
  let benchs = List.map (fun b -> (b,ref [])) benchs in
  general ?callback (fun f ->
    List.iter (fun (b,l) ->
    List.iter (fun t -> List.iter (fun p -> f l t p) b.bprobs)
      b.btools) benchs)
    (fun l r -> l:=r::!l);
  List.map (fun (b,l) -> (b,!l)) benchs

let run_benchs_tools ?callback benchs =
  let benchs = List.map (fun b ->
    b, List.map (fun t -> t,ref []) b.btools) benchs in
  general ?callback (fun f ->
    List.iter (fun (b,l) ->
    List.iter (fun p -> List.iter (fun (t,l) -> f l t p) l)
      b.bprobs) benchs)
    (fun l r -> l:=r::!l);
  List.map (fun (b,l) -> b,List.map (fun (t,l) -> t.tval,!l) l) benchs



(** average *)

(** valid * timeout * unknown * invalid  *)
type nb_avg = int * float

let add_nb_avg (nb,avg) time =
  (succ nb, ((float nb) *. avg +. time) /. (float (succ nb)))
let empty_nb_avg = (0,0.)

let print_nb_avg fmt (nb,avg) = fprintf fmt "%i : %.2f" nb avg

type tool_res =
    { valid : nb_avg;
      timeout : nb_avg;
      unknown : nb_avg;
      invalid : nb_avg;
      failure : nb_avg}

let empty_tool_res =
  { valid   = empty_nb_avg;
    timeout = empty_nb_avg;
    unknown = empty_nb_avg;
    invalid = empty_nb_avg;
    failure = empty_nb_avg;
  }

  let print_tool_res fmt tool_res =
    fprintf fmt "(%a, %a, %a, %a, %a)"
      print_nb_avg tool_res.valid
      print_nb_avg tool_res.unknown
      print_nb_avg tool_res.timeout
      print_nb_avg tool_res.invalid
      print_nb_avg tool_res.failure

  let compute_average l =
  let fold tr res =
    let r = res.result in
    match r with
      | Done (answer,time) ->
        begin match answer with
          | Db.Done Call_provers.Valid ->
              {tr with valid = add_nb_avg tr.valid time}
          | Db.Done Call_provers.Timeout ->
              {tr with timeout = add_nb_avg tr.timeout time}
          | Db.Done Call_provers.Invalid ->
              {tr with invalid = add_nb_avg tr.invalid time}
          | Db.Undone | Db.Done (Call_provers.Unknown _) ->
              {tr with unknown = add_nb_avg tr.unknown time}
          | Db.Done (Call_provers.Failure _)
          | Db.Done Call_provers.HighFailure ->
              {tr with failure = add_nb_avg tr.failure time}
        end
      | InternalFailure _ ->
          {tr with failure = add_nb_avg tr.failure 0.} in
    List.fold_left fold empty_tool_res l

  let extract_time = function Done (_,t) -> t
    | InternalFailure _ -> assert false

  let filter_timeline l =
    let l = List.filter (function
      | {result = Done (Db.Done Call_provers.Valid,_)} -> true
      | _ -> false) l in
    let compare_valid x y =
      let c = compare (extract_time x.result)
        (extract_time y.result) in
      if c <> 0 then c else compare x y in
    let l = List.fast_sort compare_valid l in
    l

  let compute_timeline min max step =
    let rec aux acc cur next = function
      | _ when next > max -> List.rev acc
      | [] -> aux (cur::acc) cur (next+.step) []
      | {result= InternalFailure _}::l -> aux acc cur next l
      | {result= Done (_,t)}::_ as l when t >= next ->
        aux (cur::acc) cur (next+.step) l
      | _::l -> aux acc (cur+1) next l in
    aux [] 0 min

  let max_time l =
    List.fold_left (fun acc {result=r} ->
      match r with
        | Done (_,t) -> max acc t
        | InternalFailure _ -> acc ) 0. l
  open Format
(**
answer output time

*)


  let print_newline fmt () = fprintf fmt "\n"

  let transpose_sorted = function
    | [] -> []
    | (_,lres)::_ as l ->
    let lref = List.map (fun r -> (r.prob,r.task,r.idtask),ref []) lres in
    let l = List.rev l in
    let add (_,lr) res = lr := res :: !lr in
    List.iter (fun (_,lres) -> List.iter2 add lref lres) l;
    List.map (fun (b,lr) -> b,!lr) lref

  let print_csv cmp print_tool print_prob fmt l =
    let cmp x y =
      let c = cmp x.prob y.prob in
      if c <> 0 then c else
        let id x = x.task.Decl.pr_name.Ident.id_string in
        let c = String.compare (id x) (id y) in
        if c <> 0 then c else compare x.idtask y.idtask in
    let l = List.map (fun (p,l) -> p,List.fast_sort cmp l) l in
    fprintf fmt " ,";
    let print_header fmt (p,_) = fprintf fmt "%a, " print_tool p in
    Pp.print_list Pp.comma print_header fmt l;
    print_newline fmt ();
    let l = transpose_sorted l in
    let print_cell fmt {result= r} =
      match r with
        | Done (answer,time) ->
          fprintf fmt "%a, %.3f" (*"%a, %S, %.3f"*)
            BenchUtil.print_proof_status answer (*r.result.pr_output*)
            time
        | InternalFailure _ -> fprintf fmt "InternalFailure, \"\""
in
    let print_line fmt ((b,t,id),l) =
      (* No printer for task since we want the same name evenif its
         the same file with different environnement (loaded two times) *)
      fprintf fmt "%a|%s|%i ," print_prob b
        t.Decl.pr_name.Ident.id_string
        id;
      Pp.print_list Pp.comma print_cell fmt l in
    Pp.print_list print_newline print_line fmt l

  let print_timeline print_tool fmt l =
    let l = List.map (fun (t,l) -> t,filter_timeline l) l in
    let max = List.fold_left (fun acc (_,l) -> max acc (max_time l)) 0. l in
    let max = max +. 0.1 in
    let step = max /. 10. in
    let tl = List.map (fun (t,l) -> t,compute_timeline 0. max step l) l in
    let print_timeline (tool_val,timeline) =
      fprintf fmt "%a - %a\n"
        (Pp.print_list Pp.comma (fun fmt -> fprintf fmt "%4i"))
        timeline print_tool tool_val in
    fprintf fmt "%a\n"
      (Pp.print_iter1 (fun f -> Util.iterf f 0. max)
         Pp.comma (fun fmt -> fprintf fmt "%3.2f"))
      step;
    List.iter print_timeline tl


  let print_average print_tool fmt l =
    let tool_res = List.map (fun (t,l) -> t,compute_average l) l in
    let print_tool_res (tool_val,tool_res) =
      fprintf fmt "%a - %a\n" print_tool_res tool_res print_tool tool_val in
    fprintf fmt "(v,u,t,i,f) - valid, unknown, timeout, invalid, failure\n";
    List.iter print_tool_res tool_res


  let print_output cmp print_tool print_probs (b,l) =
    let open_std f s =
      if s = "-"
      then begin f std_formatter;pp_print_flush std_formatter () end
      else
        let cout = (open_out s) in
        let fmt = (formatter_of_out_channel cout) in
        f fmt;
        pp_print_flush fmt ();
        close_out cout in
    List.iter (function
      | Average s -> open_std (fun fmt ->
        Pp.wnl fmt;
        print_average print_tool fmt l) s
      | Timeline s -> open_std (fun fmt ->
        Pp.wnl fmt;
        print_timeline print_tool fmt l) s
      | Csv s ->
        open_std (fun fmt -> Pp.wnl fmt;
          print_csv cmp print_tool print_probs fmt l) s
    ) b.boutputs


