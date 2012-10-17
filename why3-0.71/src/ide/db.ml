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
open Sqlite3


type transaction_mode = | Deferred | Immediate | Exclusive

type handle = {
  raw_db : Sqlite3.db;
  mutable in_transaction: int;
  busyfn: Sqlite3.db -> unit;
  mode: transaction_mode;
  db_name : string;
}

let current_db = ref None

let current () =
  match !current_db with
    | None -> failwith "Db.current: database not yet initialized"
    | Some x -> x

let is_initialized () = !current_db <> None
let db_name () = (current ()).db_name


let default_busyfn (_db:Sqlite3.db) =
  prerr_endline "Db.default_busyfn WARNING: busy";
  (* Thread.delay (Random.float 1.) *)
  ignore (Unix.select [] [] [] (Random.float 1.))

let raise_sql_error x = raise (Sqlite3.Error (Rc.to_string x))


(* retry until a non-BUSY error code is returned *)
let rec db_busy_retry db fn =
  match fn () with
    | Rc.BUSY ->
        db.busyfn db.raw_db; db_busy_retry db fn
    | x ->
        x

(* make sure an OK is returned from the database *)
let db_must_ok db fn =
  match db_busy_retry db fn with
    | Rc.OK -> ()
    | x -> raise_sql_error x

(* make sure a DONE is returned from the database *)
let db_must_done db fn =
  match db_busy_retry db fn with
    | Rc.DONE -> ()
    | x -> raise_sql_error x

(* request a transaction *)
let transaction db fn =
  let m = match db.mode with
    | Deferred -> "DEFERRED"
    | Immediate -> "IMMEDIATE"
    | Exclusive -> "EXCLUSIVE"
  in
  try
    db_must_ok db
      (fun () -> exec db.raw_db ("BEGIN " ^ m ^ " TRANSACTION"));
    assert (db.in_transaction = 0);
    db.in_transaction <- 1;
    let res = fn () in
    db_must_ok db (fun () -> exec db.raw_db "END TRANSACTION");
    assert (db.in_transaction = 1);
    db.in_transaction <- 0;
    res
  with
      e ->
        prerr_string "Db.transaction WARNING: exception: ";
        prerr_endline (Printexc.to_string e);
        prerr_endline "== exception backtrace ==";
        Printexc.print_backtrace stderr;
        prerr_endline "== end of backtrace ==";
        db_must_ok db (fun () -> exec db.raw_db "END TRANSACTION");
        assert (db.in_transaction = 1);
        db.in_transaction <- 0;
        raise e


(* iterate over a result set *)
let step_fold db stmt iterfn =
  let stepfn () = Sqlite3.step stmt in
  let rec fn a = match db_busy_retry db stepfn with
    | Sqlite3.Rc.ROW -> fn (iterfn stmt :: a)
    | Sqlite3.Rc.DONE -> a
    | x -> raise_sql_error x
  in
  fn []

(* iterate over a result set *)
let step_iter db stmt iterfn =
  let stepfn () = Sqlite3.step stmt in
  let rec fn () = match db_busy_retry db stepfn with
    | Sqlite3.Rc.ROW -> iterfn stmt; fn ()
    | Sqlite3.Rc.DONE -> ()
    | x -> raise_sql_error x
  in
  fn ()

(* iterate over a result set *)
let step_fold_gen db stmt iterfn start =
  let stepfn () = Sqlite3.step stmt in
  let rec fn a = match db_busy_retry db stepfn with
    | Sqlite3.Rc.ROW -> fn (iterfn stmt a)
    | Sqlite3.Rc.DONE -> a
    | x -> raise_sql_error x
  in
  fn start

(* DB/SQL helpers *)

let bind db sql l =
  let stmt = Sqlite3.prepare db.raw_db sql in
  let _ =
    List.fold_left
      (fun i v -> db_must_ok db (fun () -> Sqlite3.bind stmt i v); succ i)
      1 l
  in stmt

let stmt_column_INT stmt i msg =
  match Sqlite3.column stmt i with
    | Sqlite3.Data.INT i -> i
    | _ -> failwith msg

let stmt_column_FLOAT stmt i msg =
  match Sqlite3.column stmt i with
    | Sqlite3.Data.FLOAT i -> i
    | _ -> failwith msg

(*
let stmt_column_TEXT stmt i msg =
  match Sqlite3.column stmt i with
    | Sqlite3.Data.TEXT i -> i
    | _ -> failwith msg
*)

let stmt_column_int stmt i msg =
  match Sqlite3.column stmt i with
    | Sqlite3.Data.INT i -> Int64.to_int i
    | _ -> failwith msg

let int64_from_bool b =
  if b then 1L else 0L

let bool_from_int64 i =
  if i=0L then false else
    if i=1L then true else
      failwith "Db.bool_from_int64"

let stmt_column_bool stmt i msg =
  match Sqlite3.column stmt i with
    | Sqlite3.Data.INT i -> bool_from_int64 i
    | _ -> failwith msg

let stmt_column_string stmt i msg =
  match Sqlite3.column stmt i with
    | Sqlite3.Data.TEXT i -> i
    | _ -> failwith msg

(** Data *)

type prover_id =
    { prover_id : int64;
      prover_name : string;
    }

let prover_name p = p.prover_name



module Hprover = Hashtbl.Make
  (struct
     type t = prover_id
     let equal p1 p2 = p1.prover_id = p2.prover_id
     let hash p = Hashtbl.hash p.prover_id
   end)

type transf_id =
    { transformation_id : int64;
      transformation_name : string;
    }

let transf_name t = t.transformation_name

module Htransf = Hashtbl.Make
  (struct
     type t = transf_id
     let equal t1 t2 = t1.transformation_id = t2.transformation_id
     let hash t = Hashtbl.hash t.transformation_id
   end)




type proof_status =
  | Undone                      (** external proof attempt not done yet *)
  | Done of Call_provers.prover_answer  (** external proof attempt done *)

type proof_attempt = int64
(*
{
    mutable proof_attempt_id : int;
    mutable prover : prover_id;
    mutable timelimit : int;
    mutable memlimit : int;
    mutable status : proof_status;
    mutable result_time : float;
    mutable edited_as : string;
    mutable proof_obsolete : bool;
}
*)

(*
let prover _p = assert false (* p.prover *)
*)
(*
let status _p = assert false (* p.status *)
*)
(*
let proof_obsolete _p = assert false (* p.proof_obsolete *)
*)
(*
let time _p = assert false (* p.result_time *)
*)
let edited_as _p = assert false (* p.edited_as *)

type transf = int64
and goal = int64



type theory = int64


type file = int64

(*
let file_name _ = assert false
*)




module ProverId = struct

  let init db =
    let sql =
      "CREATE TABLE IF NOT EXISTS prover \
       (prover_id INTEGER PRIMARY KEY AUTOINCREMENT,prover_name TEXT);"
    in
    db_must_ok db (fun () -> Sqlite3.exec db.raw_db sql);
    let sql =
      "CREATE UNIQUE INDEX IF NOT EXISTS prover_name_idx \
       ON prover (prover_name)"
    in
    db_must_ok db (fun () -> Sqlite3.exec db.raw_db sql)

(*
  let delete db pr =
    let id =  pr.prover_id in
    let sql = "DELETE FROM prover WHERE id=?" in
    let stmt = Sqlite3.prepare db.raw_db sql in
    db_must_ok db (fun () -> Sqlite3.bind stmt 1 (Sqlite3.Data.INT id));
    ignore (step_fold db stmt (fun _ -> ()));
    pr.prover_id <- 0L
*)

  let add db name =
    transaction db
      (fun () ->
         let sql = "INSERT INTO prover VALUES(NULL,?)" in
         let stmt = bind db sql [ Sqlite3.Data.TEXT name ] in
         db_must_done db (fun () -> Sqlite3.step stmt);
         let new_id = Sqlite3.last_insert_rowid db.raw_db in
         { prover_id = new_id ;
           prover_name = name }
      )

  let from_name db name =
    let sql =
      "SELECT prover.prover_id FROM prover \
       WHERE prover.prover_name=?"
    in
    let stmt = bind db sql [Sqlite3.Data.TEXT name] in
    (* convert statement into record *)
    let of_stmt stmt =
      { prover_id = stmt_column_INT stmt 0 "ProverId.get: bad prover id";
        prover_name = name;
      }
    in
    (* execute the SQL query *)
    match step_fold db stmt of_stmt with
      | [] -> raise Not_found
      | [x] -> x
      | _ -> assert false

  let from_id db id =
    let sql =
      "SELECT prover.prover_name FROM prover \
       WHERE prover.prover_id=?"
    in
    let stmt = bind db sql [Sqlite3.Data.INT id] in
    (* convert statement into record *)
    let of_stmt stmt =
      { prover_id = id ;
        prover_name = stmt_column_string stmt 0
          "ProverId.from_id: bad prover_name";
      }
    in
    (* execute the SQL query *)
    match step_fold db stmt of_stmt with
      | [] -> raise Not_found
      | [x] -> x
      | _ -> assert false

end

let prover_memo = Hashtbl.create 7

let prover_from_id id =
  try
    Hashtbl.find prover_memo id
  with Not_found ->
    let p =
      let db = current () in
      try ProverId.from_id db id
      with Not_found -> assert false
    in
    Hashtbl.add prover_memo id p;
    p


let prover_from_name n =
  let db = current () in
  try ProverId.from_name db n
  with Not_found -> ProverId.add db n


(*
let prover e = get_prover_from_id e.prover

let get_prover name (* ~short ~long ~command ~driver *) =
  let db = current () in
(*
  let checksum = Digest.file driver in
*)
  try ProverId.get db name (* ~short ~long ~command ~checksum *)
  with Not_found ->
    ProverId.add db name (* ~short ~long ~command ~checksum *)

*)


module TransfId = struct

  let init db =
    let sql =
      "CREATE TABLE IF NOT EXISTS transformation \
       (transformation_id INTEGER PRIMARY KEY AUTOINCREMENT,transformation_name TEXT);"
    in
    db_must_ok db (fun () -> Sqlite3.exec db.raw_db sql);
    let sql =
      "CREATE UNIQUE INDEX IF NOT EXISTS transformation_name_idx \
       ON transformation (transformation_name)"
    in
    db_must_ok db (fun () -> Sqlite3.exec db.raw_db sql)

(*
  let delete db pr =
    let id =  pr.prover_id in
    let sql = "DELETE FROM prover WHERE id=?" in
    let stmt = Sqlite3.prepare db.raw_db sql in
    db_must_ok db (fun () -> Sqlite3.bind stmt 1 (Sqlite3.Data.INT id));
    ignore (step_fold db stmt (fun _ -> ()));
    pr.prover_id <- 0L
*)

  let add db name =
    transaction db
      (fun () ->
         let sql = "INSERT INTO transformation VALUES(NULL,?)" in
         let stmt = bind db sql [ Sqlite3.Data.TEXT name ] in
         db_must_done db (fun () -> Sqlite3.step stmt);
         let new_id = Sqlite3.last_insert_rowid db.raw_db in
         { transformation_id = new_id ;
           transformation_name = name }
      )

  let from_name db name =
    let sql =
      "SELECT transformation.transformation_id FROM transformation \
       WHERE transformation.transformation_name=?"
    in
    let stmt = bind db sql [Sqlite3.Data.TEXT name] in
    (* convert statement into record *)
    let of_stmt stmt =
      { transformation_id = stmt_column_INT stmt 0 "TransfId.from_name: bad transformation id";
        transformation_name = name;
      }
    in
    (* execute the SQL query *)
    match step_fold db stmt of_stmt with
      | [] -> raise Not_found
      | [x] -> x
      | _ -> assert false

  let from_id db id =
    let sql =
      "SELECT transformation.transformation_name FROM transformation \
       WHERE transformation.transformation_id=?"
    in
    let stmt = bind db sql [Sqlite3.Data.INT id] in
    (* convert statement into record *)
    let of_stmt stmt =
      { transformation_id = id ;
        transformation_name = stmt_column_string stmt 0
          "TransfId.from_id: bad transformation name";
      }
    in
    (* execute the SQL query *)
    match step_fold db stmt of_stmt with
      | [] -> raise Not_found
      | [x] -> x
      | _ -> assert false

end

let transf_memo = Hashtbl.create 7

let transf_from_id id =
  try
    Hashtbl.find transf_memo id
  with Not_found ->
    let t =
      let db = current () in
      try TransfId.from_id db id
      with Not_found -> assert false
    in
    Hashtbl.add transf_memo id t;
    t

let transf_from_name n =
  let db = current () in
  try TransfId.from_name db n
  with Not_found -> TransfId.add db n


let int64_from_status = function
  | Undone                        -> 0L
  | Done Call_provers.Valid       -> 1L
  | Done Call_provers.Timeout     -> 2L
  | Done (Call_provers.Unknown _) -> 3L
  | Done (Call_provers.Failure _) -> 4L
  | Done Call_provers.Invalid     -> 5L
  | Done Call_provers.HighFailure -> 6L

let status_array = [|
  Undone;
  Done Call_provers.Valid;
  Done Call_provers.Timeout;
  Done (Call_provers.Unknown "");
  Done (Call_provers.Failure "");
  Done Call_provers.Invalid;
  Done Call_provers.HighFailure; |]

let status_from_int64 i =
  try
    status_array.(Int64.to_int i)
  with _ -> failwith "Db.status_from_int64"

module External_proof = struct

  let init db =
    let sql =
      (* timelimit INTEGER, memlimit INTEGER,
         *)
      "CREATE TABLE IF NOT EXISTS external_proofs \
       (external_proof_id INTEGER PRIMARY KEY AUTOINCREMENT,\
        goal_id INTEGER,\
        prover_id INTEGER, \
        status INTEGER,\
        obsolete INTEGER,\
        time REAL,\
        edited_as TEXT);"
    in
    db_must_ok db (fun () -> Sqlite3.exec db.raw_db sql)

  let delete db e =
    let sql = "DELETE FROM external_proofs WHERE external_proof_id=?" in
    let stmt = bind db sql [ Sqlite3.Data.INT e ] in
    ignore(step_fold db stmt (fun _ -> ()))

  let add db (g : goal) (p: prover_id) =
    transaction db
      (fun () ->
         let sql = "INSERT INTO external_proofs VALUES(NULL,?,?,0,0,0.0,\"\")" in
         let stmt = bind db sql [
           Sqlite3.Data.INT g;
           Sqlite3.Data.INT p.prover_id;
(*
           Sqlite3.Data.INT (Int64.of_int e.timelimit);
           Sqlite3.Data.INT (Int64.of_int e.memlimit);
*)
(*
           Sqlite3.Data.INT (int64_from_status e.status);
           Sqlite3.Data.INT (int64_from_bool e.proof_obsolete);
           Sqlite3.Data.FLOAT e.result_time;
*)
(*
           Sqlite3.Data.TEXT e.trace;
*)
         ]
         in
         db_must_done db (fun () -> Sqlite3.step stmt);
         Sqlite3.last_insert_rowid db.raw_db)

  let set_status db e stat time =
    transaction db
      (fun () ->
         let sql =
           "UPDATE external_proofs SET status=?,obsolete=0,time=? WHERE external_proof_id=?"
         in
         let stmt = bind db sql [
           Sqlite3.Data.INT (int64_from_status stat);
           Sqlite3.Data.FLOAT time;
           Sqlite3.Data.INT e;
         ]
         in
         db_must_done db (fun () -> Sqlite3.step stmt))

  let set_obsolete db e =
    transaction db
      (fun () ->
         let sql =
           "UPDATE external_proofs SET obsolete=1 WHERE external_proof_id=?"
         in
         let stmt = bind db sql [
           Sqlite3.Data.INT e;
         ]
         in
         db_must_done db (fun () -> Sqlite3.step stmt))

  let set_edited_as db e f =
    transaction db
      (fun () ->
         let sql =
           "UPDATE external_proofs SET edited_as=? WHERE external_proof_id=?"
         in
         let stmt = bind db sql [
           Sqlite3.Data.TEXT f;
           Sqlite3.Data.INT e;
         ]
         in
         db_must_done db (fun () -> Sqlite3.step stmt))

  let of_goal db g =
    let sql="SELECT prover_id,external_proof_id FROM external_proofs \
       WHERE external_proofs.goal_id=?"
    in
    let stmt = bind db sql [Sqlite3.Data.INT g] in
    let res = Hprover.create 7 in
    let of_stmt stmt =
      let pid = stmt_column_INT stmt 0 "External_proof.of_goal" in
      let a = stmt_column_INT stmt 1 "External_proof.of_goal" in
      Hprover.add res (prover_from_id pid) a
    in
    step_iter db stmt of_stmt;
    res

  let status_and_time db p =
    let sql="SELECT status,time,obsolete,edited_as FROM external_proofs \
       WHERE external_proofs.external_proof_id=?"
    in
    let stmt = bind db sql [Sqlite3.Data.INT p] in
    let of_stmt stmt =
      let status = stmt_column_INT stmt 0 "External_proof.status_and_time" in
      let t = stmt_column_FLOAT stmt 1 "External_proof.status_and_time" in
      let o = stmt_column_bool stmt 2 "External_proof.status_and_time" in
      let e = stmt_column_string stmt 3 "External_proof.status_and_time" in
      (status_from_int64 status, t, o, e)
    in
    match step_fold db stmt of_stmt with
      | [] -> raise Not_found
      | [x] -> x
      | _ -> assert false


end

let status_and_time p = External_proof.status_and_time (current()) p

let external_proofs g = External_proof.of_goal (current()) g

let remove_proof_attempt e = External_proof.delete (current()) e

module Goal = struct

  let init db =
    let sql =
      "CREATE TABLE IF NOT EXISTS goals \
       (goal_id INTEGER PRIMARY KEY AUTOINCREMENT, \
        goal_theory INTEGER,\
        goal_transf INTEGER,\
        goal_name TEXT, task_checksum TEXT, proved INTEGER);"
        (* goal_transf is 0 for root goals
           goal_theory is 0 for subgoals *)
    in
    db_must_ok db (fun () -> Sqlite3.exec db.raw_db sql);
(*
    let sql =
      "CREATE UNIQUE INDEX IF NOT EXISTS goal_theory_idx \
       ON goals (goal_theory)"
    in
    db_must_ok db (fun () -> Sqlite3.exec db.raw_db sql);
*)
(*
    let sql = "create table if not exists map_external_proofs_goal_external_proof (goal_id integer, external_proof_id integer, primary key(goal_id, external_proof_id));" in
    db_must_ok db (fun () -> Sqlite3.exec db.db sql);
    let sql = "create table if not exists map_transformations_goal_transf (goal_id integer, transf_id integer, primary key(goal_id, transf_id));" in
    db_must_ok db (fun () -> Sqlite3.exec db.db sql);
*)
    ()

  let add db (th:theory) (name : string) (sum:string) =
    transaction db
      (fun () ->
         let sql =
           "INSERT INTO goals VALUES(NULL,?,0,?,?,0)"
         in
         let stmt = bind db sql [
           Sqlite3.Data.INT th;
           Sqlite3.Data.TEXT name;
           Sqlite3.Data.TEXT sum;
         ]
         in
         db_must_done db (fun () -> Sqlite3.step stmt);
         Sqlite3.last_insert_rowid db.raw_db)

  let add_as_subgoal db (tr:transf) (name : string) (sum:string) =
    transaction db
      (fun () ->
         let sql =
           "INSERT INTO goals VALUES(NULL,0,?,?,?,0)"
         in
         let stmt = bind db sql [
           Sqlite3.Data.INT tr;
           Sqlite3.Data.TEXT name;
           Sqlite3.Data.TEXT sum;
         ]
         in
         db_must_done db (fun () -> Sqlite3.step stmt);
         Sqlite3.last_insert_rowid db.raw_db)

  let delete db e =
    let sql = "DELETE FROM goals WHERE goal_id=?" in
    let stmt = bind db sql [ Sqlite3.Data.INT e ] in
    ignore(step_fold db stmt (fun _ -> ()))


  let set_task_checksum db g s =
    transaction db
      (fun () ->
         let sql =
           "UPDATE goals SET task_checksum=? WHERE goal_id=?"
         in
         let stmt = bind db sql [
           Sqlite3.Data.TEXT s;
           Sqlite3.Data.INT g;
         ]
         in
         db_must_done db (fun () -> Sqlite3.step stmt))


  let name db g =
    let sql="SELECT goal_name FROM goals \
       WHERE goals.goal_id=?"
    in
    let stmt = bind db sql [Sqlite3.Data.INT g] in
    let of_stmt stmt =
      (stmt_column_string stmt 0 "Goal.name")
    in
    match step_fold db stmt of_stmt with
      | [] -> raise Not_found
      | [x] -> x
      | _ -> assert false

  let task_checksum db g =
    let sql="SELECT task_checksum FROM goals WHERE goals.goal_id=?"
    in
    let stmt = bind db sql [Sqlite3.Data.INT g] in
    let of_stmt stmt =
      (stmt_column_string stmt 0 "Goal.task_checksum")
    in
    match step_fold db stmt of_stmt with
      | [] -> raise Not_found
      | [x] -> x
      | _ -> assert false

  let of_theory db th =
    let sql="SELECT goal_id,goal_name FROM goals \
       WHERE goals.goal_theory=?"
    in
    let stmt = bind db sql [Sqlite3.Data.INT th] in
    step_fold_gen db stmt
      (fun stmt acc ->
         let g = stmt_column_INT stmt 0 "Goal.of_theory" in
         let n = stmt_column_string stmt 1 "Goal.of_theory" in
         Util.Mstr.add n g acc)
      Util.Mstr.empty

  let of_transf db tr =
    let sql="SELECT goal_id,task_checksum FROM goals \
       WHERE goals.goal_transf=?"
    in
    let stmt = bind db sql [Sqlite3.Data.INT tr] in
    step_fold_gen db stmt
      (fun stmt acc ->
         let g = stmt_column_INT stmt 0 "Goal.of_transf" in
         let sum = stmt_column_string stmt 1 "Goal.of_transf" in
         Util.Mstr.add sum g acc)
      Util.Mstr.empty

end

let goal_name g = Goal.name (current()) g
let task_checksum g = Goal.task_checksum (current()) g
let change_checksum g s = Goal.set_task_checksum (current()) g s

let goals th = Goal.of_theory (current()) th

let subgoals tr = Goal.of_transf (current()) tr

let remove_subgoal g = Goal.delete (current()) g







(* {transformations} *)




module Transf = struct


  let init db =
    let sql =
      "CREATE TABLE IF NOT EXISTS transformations \
       (transf_id INTEGER PRIMARY KEY AUTOINCREMENT, \
        transf_id_id INTEGER,\
        parent_goal INTEGER);"
    in
    db_must_ok db (fun () -> Sqlite3.exec db.raw_db sql)

  let add db root_goal tr_id =
    transaction db
      (fun () ->
         let sql =
           "INSERT INTO transformations VALUES(NULL,?,?)"
         in
         let stmt = bind db sql [
           Sqlite3.Data.INT tr_id.transformation_id;
           Sqlite3.Data.INT root_goal;
         ]
         in
         db_must_done db (fun () -> Sqlite3.step stmt);
         Sqlite3.last_insert_rowid db.raw_db)

  let delete db t =
    let sql = "DELETE FROM transformations WHERE transf_id=?" in
    let stmt = bind db sql [ Sqlite3.Data.INT t ] in
    ignore(step_fold db stmt (fun _ -> ()))

  let of_goal db g =
    let sql="SELECT transf_id,transf_id_id FROM transformations \
       WHERE transformations.parent_goal=?"
    in
    let stmt = bind db sql [Sqlite3.Data.INT g] in
    let res = Htransf.create 7 in
    let of_stmt stmt =
      let t = stmt_column_INT stmt 0 "Transf.of_goal" in
      let tid = stmt_column_INT stmt 1 "Transf.of_goal" in
      Htransf.add res (transf_from_id tid) t
    in
    step_iter db stmt of_stmt;
    res


end

let transformations g = Transf.of_goal (current()) g

let remove_transformation t = Transf.delete (current()) t

module Theory = struct

  let init db =
    let sql =
      "CREATE TABLE IF NOT EXISTS theories \
       (theory_id INTEGER PRIMARY KEY AUTOINCREMENT,\
        theory_file INTEGER, theory_name TEXT);" in
    db_must_ok db (fun () -> Sqlite3.exec db.raw_db sql);
    ()

  let name db th =
    let sql="SELECT theory_name FROM theories \
       WHERE theories.theory_id=?"
    in
    let stmt = bind db sql [Sqlite3.Data.INT th] in
    let of_stmt stmt =
      (stmt_column_string stmt 0 "Theory.name")
    in
    match step_fold db stmt of_stmt with
      | [] -> raise Not_found
      | [x] -> x
      | _ -> assert false

  let of_file db f =
    let sql="SELECT theory_name,theory_id FROM theories \
       WHERE theories.theory_file=?"
    in
    let stmt = bind db sql [Sqlite3.Data.INT f] in
    step_fold_gen db stmt
      (fun stmt acc ->
         let name = stmt_column_string stmt 0 "Theory.of_file" in
         let th = stmt_column_INT stmt 1 "Theory.of_file" in
         Util.Mstr.add name th acc)
      Util.Mstr.empty

  let add db file name =
    transaction db
      (fun () ->
         let sql = "INSERT INTO theories VALUES(NULL,?,?)" in
         let stmt = bind db sql
           [ Sqlite3.Data.INT file;
             Sqlite3.Data.TEXT name;
           ]
         in
         db_must_done db (fun () -> Sqlite3.step stmt);
         let new_id = Sqlite3.last_insert_rowid db.raw_db in
         new_id)
end

let theory_name th = Theory.name (current()) th

let theories f = Theory.of_file (current()) f

module Main = struct

  let init db =
    let sql = "CREATE TABLE IF NOT EXISTS files \
          (file_id INTEGER PRIMARY KEY AUTOINCREMENT,file_name TEXT);"
    in
    db_must_ok db (fun () -> Sqlite3.exec db.raw_db sql)

  let all_files db =
    let sql="SELECT file_id,file_name FROM files" in
    let stmt = Sqlite3.prepare db.raw_db sql in
    let of_stmt stmt =
      (stmt_column_INT stmt 0 "Db.all_files",
       stmt_column_string stmt 1 "Db.all_files")
    in
    step_fold db stmt of_stmt

  let add db name =
    transaction db
      (fun () ->
         let sql = "INSERT INTO files VALUES(NULL,?)" in
         let stmt = bind db sql [ Sqlite3.Data.TEXT name ] in
         db_must_done db (fun () -> Sqlite3.step stmt);
         let new_id = Sqlite3.last_insert_rowid db.raw_db in
         new_id)
end


let init_db ?(busyfn=default_busyfn) ?(mode=Immediate) db_name =
  match !current_db with
    | None ->
        let db = {
          raw_db = Sqlite3.db_open db_name;
          in_transaction = 0;
          mode = mode;
          busyfn = busyfn;
          db_name = db_name;
        }
        in
        current_db := Some db;
        ProverId.init db;
        TransfId.init db;
        External_proof.init db;
        Goal.init db;
        Transf.init db;
        Theory.init db;
        Main.init db

    | Some _ -> failwith "Db.init_db: already opened"


let init_base f = init_db ~mode:Deferred f

let files () = List.rev (Main.all_files (current()))

exception AlreadyExist

let add_proof_attempt g pid = External_proof.add (current()) g pid

let set_status a r t =
  External_proof.set_status (current()) a r t

let set_obsolete a =
  External_proof.set_obsolete (current()) a

let set_edited_as a f =
  External_proof.set_edited_as (current()) a f

let add_transformation g tr_id = Transf.add (current()) g tr_id

let add_goal th id sum = Goal.add (current()) th id sum

let add_subgoal tr id sum = Goal.add_as_subgoal (current()) tr id sum

let add_theory f th = Theory.add (current()) f th

let add_file f = Main.add (current()) f


(*
Local Variables:
compile-command: "unset LANG; make -C ../.. bin/why3ide.byte"
End:
*)
