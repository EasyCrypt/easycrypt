(* -------------------------------------------------------------------- *)
open EcIdent
open EcModules
open EcLogic

(* -------------------------------------------------------------------- *)
type 'a sdestr_t  = string -> stmt -> 'a * stmt
type 'a sdestr2_t = string -> stmt -> stmt -> 'a * 'a * stmt * stmt

(* -------------------------------------------------------------------- *)
let s_first proj error s =
  match s.s_node with
  | [] -> error ()
  | i :: r -> try (proj i, stmt r) with Not_found -> error ()

let s_first2 proj error sl sr =
  let hl,tl = s_first proj error sl in
  let hr,tr = s_first proj error sr in
    (hl, hr, tl, tr)

let first_error si st () = 
  cannot_apply st (Printf.sprintf "invalid first instruction: expected [%s]" si)

let s_first_asgn    st = s_first  destr_asgn   (first_error "asgn"   st)
let s_first_asgns   st = s_first2 destr_asgn   (first_error "asgn"   st)
let s_first_rnd     st = s_first  destr_rnd    (first_error "rnd"    st)
let s_first_rnds    st = s_first2 destr_rnd    (first_error "rnd"    st)
let s_first_call    st = s_first  destr_call   (first_error "call"   st)
let s_first_calls   st = s_first2 destr_call   (first_error "call"   st)
let s_first_if      st = s_first  destr_if     (first_error "if"     st)
let s_first_ifs     st = s_first2 destr_if     (first_error "if"     st)
let s_first_while   st = s_first  destr_while  (first_error "while"  st)
let s_first_whiles  st = s_first2 destr_while  (first_error "while"  st)
let s_first_assert  st = s_first  destr_assert (first_error "assert" st)
let s_first_asserts st = s_first2 destr_assert (first_error "assert" st)

(* -------------------------------------------------------------------- *)
let s_last proj error s =
  match List.rev s.s_node with
  | [] -> error ()
  | i :: r -> try (proj i, rstmt r) with Not_found -> error ()

let s_last2 destr_i error sl sr =
  let hl,tl = s_last destr_i error sl in
  let hr,tr = s_last destr_i error sr in
    (hl, hr, tl, tr)

let last_error si st () = 
  cannot_apply st (Printf.sprintf "invalid last instruction: expected [%s]" si)

let s_last_asgn    st = s_last  destr_asgn   (last_error "asgn"   st)
let s_last_asgns   st = s_last2 destr_asgn   (last_error "asgn"   st)
let s_last_rnd     st = s_last  destr_rnd    (last_error "rnd"    st)
let s_last_rnds    st = s_last2 destr_rnd    (last_error "rnd"    st)
let s_last_call    st = s_last  destr_call   (last_error "call"   st)
let s_last_calls   st = s_last2 destr_call   (last_error "call"   st)
let s_last_if      st = s_last  destr_if     (last_error "if"     st)
let s_last_ifs     st = s_last2 destr_if     (last_error "if"     st)
let s_last_while   st = s_last  destr_while  (last_error "while"  st)
let s_last_whiles  st = s_last2 destr_while  (last_error "while"  st)
let s_last_assert  st = s_last  destr_assert (last_error "assert" st)
let s_last_asserts st = s_last2 destr_assert (last_error "assert" st)
