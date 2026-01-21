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
    var garbage: int;
    (* put some garbage to avoid the random sampling being the only instruction in a procedure *)
    garbage <- 0; 
    x <$ dbiased (mu D test);
    return x;
  }
  proc g() : t = {
    var l: t;
    var garbage: int;
    garbage <- 0;
    l <$ D;
    return l;
  }
}.

op c : (bool * t) distr = dmap D (fun x => (test x, x)).
      
(* prove the lemma by directly providing a coupling *)
lemma B_coupling:
  equiv [ B.f ~ B.g : true ==> res{1} = test res{2} ].
proof.
proc.
coupling c.
wp; skip => /=; split; last first.
+ move => a b.
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

(* prove the lemma by bypr, which means we compute the probability at each side separately. *)
lemma B_coupling_bypr:
  equiv [ B.f ~ B.g : true ==> res{1} = test res{2} ].
proof.
bypr res{1} (test res{2}).
+ smt().
+ move => &1 &2 b.
  have ->: Pr[B.f() @ &1 : res = b] = mu1 (dbiased (mu D test)) b.
  + byphoare => //.
    proc; rnd; wp; skip => />.
  have -> //: Pr[B.g() @ &2 : test res = b] = mu1 (dbiased (mu D test)) b.
  + byphoare => //.
    proc; rnd; sp; skip => />.
    rewrite dbiased1E.
    rewrite clamp_id.
    + exact mu_bounded.
    case b => _.
    + apply mu_eq => x /#.
    rewrite (mu_eq _ _ (predC test)).
    + by smt().
    by rewrite mu_not D_ll.  
qed.

op f (x : t) : bool = test x.

lemma B_compress:
  equiv [ B.g ~ B.f : true ==> test res{1} = res{2} ].
proof.
proc.
coupling{1} f.
wp; skip => @/predT /=.
+ split.
  + apply eq_distr => b.
    rewrite dbiased1E.
    rewrite clamp_id.
    + exact mu_bounded.
    rewrite dmap1E /pred1 /(\o) /=.
    case b => _.
    + by apply mu_eq => x /#.
    rewrite (mu_eq _ _ (predC test)).
    + by smt().
    by rewrite mu_not D_ll.
  + by move => @/f * //=.
qed.

lemma B_compress_reverse:
  equiv [ B.f ~ B.g : true ==> test res{2} = res{1} ].
proof.
proc.
coupling{2} f.
wp; skip => @/predT /=.
+ split.
  + apply eq_distr => b.
    rewrite dbiased1E.
    rewrite clamp_id.
    + exact mu_bounded.
    rewrite dmap1E /pred1 /(\o) /=.
    case b => _.
    + by apply mu_eq => x /#.
    rewrite (mu_eq _ (fun (x : t) => f x = false) (predC test)).
    + by smt().
    by rewrite mu_not D_ll.
  + by move => @/f //.
qed.
