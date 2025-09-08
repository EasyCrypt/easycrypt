require import AllCore List.
require import Distr DBool DList.
(*---*) import Biased.
require import StdBigop.
(*---*) import Bigreal Bigreal.BRA.

type t.

op test : t -> bool.
op D : t distr.

axiom D_ll : is_lossless D.

module B = {
  proc f() : bool = {
    var x: bool;
    x <$ dbiased (mu D test);
    return x;
  }
  proc g() : t = {
    var l: t;
    l <$ D;
    return l;
  }
}.

op c : (bool * t) distr = dmap D (fun x => (test x, x)).
  
lemma B_coupling:
  equiv [ B.f ~ B.g : true ==> res{1} = test res{2} ].
proof.
(* bypr res{1} (test res{2}). *)
(* + smt(). *)
(* + move => &1 &2 b. *)
(*   have ->: Pr[B.f() @ &1 : res = b] = mu1 (dbiased (mu D test)) b. *)
(*   + byphoare => //. *)
(*     proc; rnd; skip => />. *)
(*   have -> //: Pr[B.g() @ &2 : test res = b] = mu1 (dbiased (mu D test)) b. *)
(*   + byphoare => //. *)
(*     proc; rnd; skip => />. *)
(*     rewrite dbiased1E. *)
(*     rewrite clamp_id. *)
(*     + exact mu_bounded. *)
(*     case b => _. *)
(*     + apply mu_eq => x /#. *)
(*     rewrite (mu_eq _ _ (predC test)). *)
(*     + by smt(). *)
(*     by rewrite mu_not D_ll.  *)  
proc.
rndpp c.
+ move => a b />.
  by rewrite /c => /supp_dmap [x] />.
rewrite /iscoupling; split; last first.
+ by rewrite /c dmap_comp /(\o) /= dmap_id.
rewrite /c dmap_comp /(\o) /=.
apply eq_distr => b.
rewrite dbiased1E.
rewrite clamp_id.
+ exact mu_bounded.
rewrite dmap1E /pred1 /(\o) /=.
case b => _.
+ by apply mu_eq => x /#.
rewrite (mu_eq _ _ (predC test)).
+ by smt().
by rewrite mu_not D_ll.
qed.
