open EcUtil
open Why3

let config : Whyconf.config = Whyconf.read_config None

let main : Whyconf.main = Whyconf.get_main config

let env : Env.env = Env.create_env (Whyconf.loadpath main)

let _ = 
  debug db_var "LOADPATH = \n%a"
    (EcUtil.pp_string_list ~sep:"\n") (Whyconf.loadpath main)

let theories = ref []

let find_th l s =
  let th = Env.find_theory env l s in
  theories := th::!theories;
  th

let find_ts th s =
  Theory.ns_find_ts th.Theory.th_export [s]

let find_ls th s = 
  Theory.ns_find_ls th.Theory.th_export [s]


(** Int theory *)

let int_theory = find_th ["int"] "Int"
let int_div_theory = find_th ["int"] "EuclideanDivision"
let int_pow_theory = find_th ["int"] "Power" 
let int_abs_theory = find_th ["int"] "Abs" 


let ps_le_int = find_ls int_theory "infix <="

let ps_lt_int = find_ls int_theory "infix <"

let ls_opp_int = find_ls int_theory "prefix -"
let ls_add_int = find_ls int_theory "infix +"
let ls_sub_int = find_ls int_theory "infix -"
let ls_mul_int = find_ls int_theory "infix *"
let ls_div_int = find_ls int_div_theory "div"
let ls_mod_int = find_ls int_div_theory "mod"
let ls_abs_int = find_ls int_abs_theory "abs"
let ls_pow_int = find_ls int_pow_theory "power"

(** Real theory *)
let real_theory = find_th ["real"] "RealInfix"
let real_fint_theory = find_th ["real"] "FromInt"
let real_abs_theory = find_th ["real"] "Abs"
let real_pow_theory = find_th ["real"] "Power"
let real_explog_theory = find_th ["real"] "ExpLog"
  
let ty_real = Ty.ty_app (find_ts real_theory "real") []
let ps_le_real = find_ls real_theory "infix <=."
let ps_lt_real = find_ls real_theory "infix <."

let ls_opp_real = find_ls real_theory "prefix -."
let ls_add_real = find_ls real_theory "infix +."
let ls_sub_real = find_ls real_theory "infix -."
let ls_mul_real = find_ls real_theory "infix *."
let ls_div_real = find_ls real_theory "infix /."
let ls_real_of_int = find_ls real_fint_theory "from_int"
let ls_abs_real = find_ls real_abs_theory "abs"
let ls_pow_real = find_ls real_pow_theory "pow"
let ls_exp_real = find_ls real_explog_theory "exp"

(** Bool theory *)
let bool_theory = find_th ["bool"] "Bool"

let ty_bool = Ty.ty_app (find_ts bool_theory "bool") []

let bool_true = 
  let ls = find_ls bool_theory "True" in
  Term.t_app_infer ls []

let bool_false = 
  let ls = find_ls bool_theory "False" in
  Term.t_app_infer ls []

let ls_andb = find_ls bool_theory "andb"
let ls_orb = find_ls bool_theory "orb"
let ls_xorb = find_ls bool_theory "xorb"
let ls_notb = find_ls bool_theory "notb"

(* Unit *)
let ty_unit = Ty.ty_app (Ty.ts_tuple 0) []

let htuple = Hashtbl.create 17 
  
let add_tuple size = 
  try
    ignore (Hashtbl.find htuple size)
  with _ ->
    Hashtbl.add htuple size ()

let ty_tuple l =
  add_tuple (List.length l);
  Ty.ty_tuple l

(* List *)

let list_theory = find_th ["list"] "List" 
let list_length_theory = find_th ["list"] "Length" 
let list_mem_theory = find_th ["list"] "Mem"
let list_append_theory = find_th ["list"] "Append"

let ts_list = find_ts list_theory "list"
let ls_nil = find_ls list_theory "Nil"
let ls_cons = find_ls list_theory "Cons"
let ls_length = find_ls list_length_theory "length"
let ls_mem = find_ls list_mem_theory "mem"
let ls_app = find_ls list_append_theory "infix ++"

(* option *)
let option_theory = find_th ["option"] "Option"
let ts_option = find_ts option_theory "option"
let ls_none = find_ls option_theory "None"
let ls_some = find_ls option_theory "Some"


(** Building types *)


(** Building terms *)

let mk_prop t = Term.t_equ t bool_true

let is_psymbol ls = ls.Term.ls_value = None

let mk_bool t = 
  Term.t_if_simp t bool_true bool_false

(*** Provers *)

let provers : Whyconf.config_prover Util.Mstr.t = Whyconf.get_provers config

let provers_list = 
  Util.Mstr.fold (fun s config l ->
    (s, config, Driver.load_driver env config.Whyconf.driver) :: l) provers []

let _ = 
  EcUtil.debug db_var "List of available provers %a@."
  (pp_list ~sep:", " (fun fmt (s,_,_) ->
    Format.fprintf fmt "%s" s)) provers_list
    
(* let _ = Why3.Debug.set_flag Why3.Call_provers.debug *)
 
let get_prover name =
  try List.find (fun (s,_,_) -> s = name) provers_list
  with Not_found -> user_error "can not find prover %s" name 

let check_prover_name name =
    if not (Util.Mstr.mem name provers) then
      user_error "Can not find the prover %s" name

open Call_provers

let nb_file = ref 0 

let print_failure goal_name task = 
  incr nb_file;
  let (_s,_pr,dr) = get_prover "coq" in  
  let fname = Filename.temp_file ("easycrypt_"^goal_name) ".v" in
  let out = open_out fname in
  let fmt = Format.formatter_of_out_channel out in
  Driver.print_task dr fmt task;
  close_out out;
  fname
   
let wait_on_call prover timelimit pp_failure goal_name task = 
  let trans = Trans.lookup_transform "simplify_trivial_quantification" env in
  let task = Trans.apply trans task in
  let (s,pr,dr) = get_prover prover in
  let res = 
    Call_provers.wait_on_call
      (Driver.prove_task ~command:pr.Whyconf.command ~timelimit
         dr task ()) () in
  let ans = res.pr_answer = Valid in
  if not ans && pp_failure then 
    begin 
      let fname = print_failure goal_name task in
      EcUtil.verbose
        "Prover %s returned %a for goal '%s' in file %s"
        s print_prover_answer res.pr_answer goal_name fname
    end;
  ans
    
let para_call provers timelimit pp_failure goal_name task =
  let trans = Trans.lookup_transform "simplify_trivial_quantification" env in
  let task = 
    try Trans.apply trans task 
    with _ -> task in 
  (*verbose "para_call %s : %a" goal_name Why3.Pretty.print_task task;*)
  let start_prover s =
    let (_,pr,dr) = get_prover s in
    s, Driver.prove_task ~command:pr.Whyconf.command ~timelimit
           dr task () in
  let kill (_s, p) = Call_provers.kill p 9 in
  let print_answer s ans = 
    let msg = 
      match ans with
      | Valid -> "valid"
      | Invalid ->  "invalid"
      | Timeout -> "timeout"
      | Unknown _ -> "unknown"
      | _ -> "failure" in
    EcUtil.verbose "prover %s returned %s for goal %s" s msg goal_name in
  let max_time = 
    Unix.gettimeofday () +. 0.9 *. float (timelimit * List.length provers) in
  let rec loop l =
    if l = [] then begin
      if pp_failure then begin
        let fname = print_failure goal_name task in 
        EcUtil.verbose
          "None of the provers is able to prove goal '%s', coq file %s"
          goal_name fname
      end; false
    end else begin
      (*Unix.pause ();*)
      if Unix.gettimeofday () >= max_time then 
        (List.iter kill l;loop [])
      else get_result [] l
    end
  and get_result r l = 
     match l with
    | [] -> loop r
    | (s,p as sp) :: l ->
        match Call_provers.query_call p with
        | Some fa ->
            let a = fa () in
            if pp_failure || a.pr_answer = Valid then print_answer s a.pr_answer;
            begin match a.pr_answer with
            | Valid | Invalid ->
                List.iter kill r;
                List.iter kill l;
                a.pr_answer = Valid
            | _ -> get_result r l
            end
        | None -> get_result (sp::r) l in 
  let fmla = Task.task_goal_fmla task in
  if Term.t_equal fmla Term.t_true then 
    (verbose "goal %s is trivial" goal_name; true)
  else loop (List.map start_prover provers)

