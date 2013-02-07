open EcLocation
open EcUtils
open EcMaps

exception UnknownSubgoal of int
exception NotAnOpenGoal of int option
exception InvalidNumberOfTactic of int * int

let pp_error fmt = function
  | UnknownSubgoal i ->
      Format.fprintf fmt "Unknown subgoal %i, please report" i
  | NotAnOpenGoal (Some i) ->
      Format.fprintf fmt "Not a open goal %i, please report" i
  | InvalidNumberOfTactic(i1,i2) -> 
      Format.fprintf fmt 
        "Invalid number of tactic, %i tactics expected, %i given" i1 i2 
  | e -> raise e

let _ = EcPexception.register pp_error

  
        
        
      
      
type ('rn,'rd) rule = {
    r_name : 'rn;
    r_hyps : ('rn,'rd) judgment list;
  }
          
and ('rn,'rd) judgment = {
    j_decl : 'rd;
    j_rule : ('rn,'rd) rule
  }

type 'rn pre_rule = {
    pr_name : 'rn;
    pr_hyps : int list
  }
          
type ('rn,'rd) pre_judgment = {
    pj_decl : 'rd;
    pj_rule : (bool * 'rn pre_rule) option; (* true means all subgoal are done *)
  }

type ('rn, 'rd) judgment_uc = {
    juc_count  : int;
    juc_map    : ('rn,'rd) pre_judgment Mint.t;
  }

type ('rn,'rd) goal  = ('rn,'rd) judgment_uc * int
type ('rn,'rd) goals = ('rn,'rd) judgment_uc * int list

module Tactic = 
  struct
    let new_goal juc decl =
      let n = juc.juc_count in
      let pj = { pj_decl = decl; pj_rule = None; } in
      let juc = 
        { juc_count = n + 1;
          juc_map   = Mint.add n pj juc.juc_map } in
      juc, n
        
    let open_juc decl = 
      new_goal { juc_count = 0; juc_map = Mint.empty } decl
        
    let close_juc juc =
      let rec close_n n = 
        let j = try Mint.find n juc.juc_map with _ -> assert false in
        close j 
      and close j = 
        let r = 
          match j.pj_rule with
          | None -> assert false 
          | Some(_, r) -> 
              { r_name = r.pr_name; r_hyps = List.map close_n r.pr_hyps } in
        { j_decl  = j.pj_decl;
          j_rule  = r } in
      close_n 0
 
    let get_goal (juc,n) =
      try Mint.find n juc.juc_map 
      with Not_found -> raise (UnknownSubgoal n)
          
    let get_open_goal (juc,n) = 
      let g = get_goal (juc,n) in
      if g.pj_rule <> None then raise (NotAnOpenGoal (Some n));
      g
    
    let upd_juc_map juc n pj = 
      { juc with juc_map = Mint.add n pj juc.juc_map }
    
    let upd_done juc =
      let is_done juc n = 
        match (get_goal (juc,n)).pj_rule with
        | Some(true, _) -> true
        | _ -> false in
      let rec upd juc n =
        let pj = get_goal (juc, n) in
        match pj.pj_rule with
        | None | Some(true, _) -> juc
        | Some(false,r) ->
            let juc = List.fold_left upd juc r.pr_hyps in
            if List.for_all (is_done juc) r.pr_hyps then 
              upd_juc_map juc n { pj with pj_rule = Some(true,r)}
            else juc in
      upd juc 0

    let get_first_goal juc = 
      let rec aux n = 
        let pj = get_goal (juc, n) in
        match pj.pj_rule with
        | None -> juc, n 
        | Some(d, r) -> if d then raise (NotAnOpenGoal None) else auxs r.pr_hyps
      and auxs ns = 
        match ns with
        | [] -> raise (NotAnOpenGoal None) 
        | n::ns -> try aux n with _ -> auxs ns in
      aux 0 

    let find_all_goals juc = 
      let juc = upd_done juc in
      let rec aux ns n = 
        let pj = get_goal (juc, n) in
        match pj.pj_rule with
        | None -> n :: ns
        | Some(d, r) -> if d then ns else List.fold_left aux ns r.pr_hyps in
      juc, List.rev (aux [] 0)

    let upd_rule (juc,n as g) d pr = 
      let pj = get_open_goal g in
      upd_juc_map juc n { pj with pj_rule = Some(d, pr) }, pr.pr_hyps

    let upd_rule_done g pr = upd_rule g true pr
    let upd_rule g pr = upd_rule g false pr

    let t_id (juc,n) = juc,[n]
    
    let t_on_goals t (juc,ln) = 
      let juc,ln = 
        List.fold_left (fun (juc,ln) n ->
          let juc,ln' = t (juc,n) in
          juc,List.rev_append ln' ln) (juc,[]) ln in
      juc,List.rev ln
        
    let t_seq t1 t2 g = t_on_goals t2 (t1 g)
        
    let rec t_lseq lt = 
      match lt with
      | [] -> t_id 
      | t1::lt -> t_seq t1 (t_lseq lt)

    let t_subgoal lt (juc,ln) =
      let len1 = List.length lt in
      let len2 = List.length ln in
      if len1 <> len2 then raise (InvalidNumberOfTactic(len2, len1));
      let juc, ln = 
        List.fold_left2 (fun (juc,ln) t n ->
          let juc, ln' = t (juc, n) in
          juc, List.rev_append ln' ln) (juc,[]) lt ln in
      juc, List.rev ln

    let t_on_nth t n (juc,ln) = 
      let r,n,l = try List.split_n n ln with _ -> assert false in
      let juc,ln = t (juc,n) in
      juc, List.rev_append r (List.append ln l)
        
    let t_on_first (_,ln as gs) t = 
      assert (ln <> []);
      t_on_nth t 0 gs 
        
    let t_on_last (_,ln as gs) t = 
      assert (ln <> []);
      t_on_nth t (List.length ln - 1) gs 

    let t_seq_subgoal t lt g = t_subgoal lt (t g)
     

end

