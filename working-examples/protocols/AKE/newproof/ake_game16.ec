include "ake_game15.ec".

(*pop pick_except : (int, int, int) -> int.

aspec pick_spec(lb : int, ub : int, x : int) : y = pick_except(lb,ub,x) : 
lb < ub && lb <= x && x <= ub ==>
lb <= y && y <= ub && x <> y.*)


(*pop pick : (int, int) -> int * int.

aspec pick_spec(lb : int, ub : int) : p = pick(lb,ub) : 
lb < ub ==>
let x = fst(p) in
let y = snd(p) in
lb <= x && x <= ub && lb <= y && y <= ub && x <> y.*)

game AKE16 =
AKE15
var indexA : int
var indexB : int
where Main = {
 var res : session_id * session_string;
 indexA = [0..qPart];
 indexB = [0..qPart];
 complete_sessions = empty_map;
 incomplete_sessions = empty_map;
 corrupt = empty_map;
 pkey = empty_map;
 skey = empty_map;
 seed = empty_map;
 msg_seeds = empty_map;
 sess = 0;
 part = 0;
 posPart = empty_map;
 res = B();
 return res;
 }.