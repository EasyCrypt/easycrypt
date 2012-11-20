(** Call provers through {{:http://why.lri.fr/index.en.html}WHY},
    * and get the results back. *)
(* ------------------------------------------------------------------------ *)

open EcUtil

(* ------------------------------------------------------------------------ *)

type prover = Ergo | Simplify | Coq | Yices | Z3 | Cvc3 

let prover_list = [Ergo ; Simplify; Coq; Yices; Z3; Cvc3]

let prover_name = function
  | Ergo -> "alt-ergo"
  | Simplify -> "simplify"
  | Yices -> "yices"
  | Z3 -> "z3"
  | Cvc3 -> "cvc3"
  | Coq -> "coq"

let pp_prover_name fmt prover =
  Format.fprintf fmt "%s" (prover_name prover)

type result = PWvalid | PWinvalid | PWunknown | PWtimeout | PWfailure

let result_text = function
  | PWvalid -> "valid"
  | PWinvalid -> "invalid"
  | PWunknown -> "unknown"
  | PWtimeout -> "timeout"
  | PWfailure -> "failure"

let pretty fmt r = Format.pp_print_string fmt (result_text r)

let prover_of_name = function
  | "yices" -> Yices
  | "z3" -> Z3
  | "cvc3" -> Cvc3
  | "simplify" -> Simplify
  | "alt-ergo" -> Ergo
  | "coq" -> Coq
  | s ->
    warning "unknown prover '%s'. Use 'alt-ergo'" s ; Ergo

(*
  let get_prover () =
  match Wp_parameters.get_prover () with
  | None -> None
  | Some p -> Some(prover_of_name p)
*)

let why_prover_option prover = match prover with
  | Yices | Z3 | Cvc3 -> ["--smtlib"]
  | Ergo -> ["--why"] (* TODO : what is the difference with --alt-ergo ? *)
  | Simplify -> ["--simplify"]
  | Coq -> ["--coq"; "-coq-preamble"; "Require Import Why. Require Import Reals."]
(*| Coq -> ["--coq"]*)

(** See why/src/dispatcher.ml *)
let why_ext prover = match prover with
  | Ergo -> "_why.why"
  | Simplify -> "_why.sx"
  | Coq -> "_why.v"
  | Yices | Z3 | Cvc3 -> "_why.smt"


let why_dp_prover_option prover =
  match prover with
    | Yices -> ["-smt-solver yices" ]
    | Z3 ->  ["-smt-solver z3" ]
    | Cvc3 ->  ["-smt-solver cvc3" ]
    | Coq | Ergo | Simplify -> []
(* prover selection is done using the file extension. *)

let resfile = Filename.temp_file "easycrypt" ".result" 

let build_command pg args =
  let rec add str l =
    match l with [] -> str
      | s::tl -> add (str^" "^s) tl
  in
  let cmd = add pg args in
  cmd ^ " 2> /dev/null > " ^ resfile


let get_result () = 
  let inc = open_in resfile in
 let f _s _c valid inval unk timeout failure =
    match valid,inval,unk,timeout,failure with 
    | 0,0,0,0,0 -> PWinvalid
    | 1,0,0,0,0 -> PWvalid
    | 0,1,0,0,0 -> PWinvalid
    | 0,0,1,0,0 -> PWunknown
    | 0,0,0,1,0 -> PWtimeout
    | 0,0,0,0,1 -> PWfailure 
    | _ -> assert false in
  let res = 
    Scanf.fscanf inc "(. = valid * = invalid ? = unknown # = timeout ! = failure)\n%s%[^(] (%i/%i/%i/%i/%i)" f in
  close_in inc;
  res


let command pg args =
  let cmd = build_command pg args in
  debug db_wp "Try to run : %s@." cmd;
  Unix.system cmd


(**
   * Notice that the prover selection is done by [why-dp]
   * using the file extension.
   * @param batch is useful only if there is only one proof obligation in the file.
*)
let prove _batch file prover =
  let whydp = "why-dp" in
  let whydp_args = ["-timeout "^(string_of_int (Global.Timeout.get ()))] in
  let whydp_args = whydp_args @ (why_dp_prover_option prover) in
  let whydp_args = whydp_args @ [file] in
  let _ = command whydp whydp_args in
  get_result ()
  (*res 
  match batch, res with
    | _, Unix.WEXITED 0 -> PWvalid
    | true, Unix.WEXITED 2 -> PWinvalid
    | true, Unix.WEXITED 3 -> PWunknown
    | true, Unix.WEXITED 4 -> PWtimeout
    | true, _ -> PWfailure
    | false, _ -> warning "Could not run whydp."; PWfailure *)

let file_to_prove why_file prover =
  let whybin = "why" in
  let why_args = why_prover_option prover in
  let why_args = why_args@[why_file] in
  if command whybin why_args <> (Unix.WEXITED 0)
  then
    begin
      warning "Could not run why (command failed). %s" why_file;
      None
    end
  else
    let base = Filename.chop_extension why_file in
    Some (base^(why_ext prover))

let check ?(pp_failure=true) name why_file prover =
  let prover_file = file_to_prove why_file prover in
  match prover_file with
    | None -> false (* TODO: Check ??? *)
    | Some prover_file ->
      let status = prove true prover_file prover in
      let res = status = PWvalid in
      if not res && pp_failure then
        Format.eprintf
          "Prover '%a' returned '%s' for goal '%s' in file %s@."
          pp_prover_name prover (result_text status) name  prover_file;
      res



(***************************************************************)
(* THIS CODE BELOW HAS BEEN COMMENTED OUT SINCE IT IS NOT USED *)
(***************************************************************)

(* let para_prover = [ Simplify; Ergo ] *)

(* exception CanNotRunWhy *)

(* let para_check _pp_failure _name why_file = *)
(*   let batch = false in *)
(*   let start_prove prover file = *)
(*     let whydp = "why-dp" in *)
(*     let whydp_args = if batch then ["-batch"] else [] in *)
(*     let whydp_args = ("-timeout "^(string_of_int (Global.get_timeout())))::whydp_args in *)
(*     let whydp_args = whydp_args @ (why_dp_prover_option prover) in *)
(*     let whydp_args = whydp_args @ [file] in *)
(*     Unix.create_process whydp (Array.of_list whydp_args) *)
(*       Unix.stdin Unix.stdout Unix.stderr in *)
(*   let start_check prover = *)
(*     debug 1 "start prover %s@." (prover_name prover); *)
(*     let prover_file = file_to_prove why_file prover in *)
(*     match prover_file with *)
(*       | None -> raise CanNotRunWhy *)
(*       | Some prover_file -> start_prove prover prover_file in *)
(*   let lpid = ref (List.map start_check para_prover) in *)
(*   let res = ref false in *)
(*   let kill_other pid lpid = *)
(*     while !lpid <> [] do *)
(*       let hd = List.hd !lpid in *)
(*       lpid := List.tl !lpid; *)
(*       if hd <> pid then Unix.kill hd 9 *)
(*     done in *)
(*   while !lpid <> [] do *)
(*     let (pid,status) = Unix.wait () in *)
(*     match status with *)
(*       | Unix.WEXITED 0 -> kill_other pid lpid; res := true *)
(*       | Unix.WEXITED 2 -> kill_other pid lpid; res := false *)
(*       | _ -> lpid := List.filter (fun p -> p <> pid) !lpid *)
(*   done; *)
(*   !res *)



