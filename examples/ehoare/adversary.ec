require import AllCore List StdOrder Distr Real Int RealExp.
(*---*) import RealOrder.
require import Xreal RealSeries.
(*---*) import StdBigop.Bigreal.

type r.
op [lossless] dr : r distr.

op test : r -> bool.

op p = mu dr test.
axiom dr_mu_test : 0%r < p.

op eps : real.
axiom dr_mu1 : forall (x:r), mu1 dr x <= eps.

lemma eps_ge0: 0%r <= eps. by smt(dr_mu1 mu_bounded). qed.

module type Oracle = { 
  proc o () : unit 
}.

module type Adv (O:Oracle) = {
  proc adv () : unit
}.

op Q : int.
axiom Q_nneg : 0 <= Q.

module O = {

  var c : int 
  var log : r list
  var bad : bool

  proc extend_log () = {
    var t, r;
    t <- false;
    while (!t) {
      r <$ dr;
      log <- r :: log;
      t <- test r; 
    }
  }

  proc o () = {
    var r;
    c <- c + 1;
    extend_log ();
    if (c = Q) {
      r <$ dr;
      bad <- r \in log;
    }
  }
}.

module Main(A:Adv) = {
  proc main () = {
    O.bad <- false;
    O.c <- 0;
    O.log <- [];
    A(O).adv();
  }
}.

(* extend-log increases log on average by 1/p *)
ehoare extend_log_size : O.extend_log : (inv p)%xr + (size O.log)%xr ==> (size O.log)%xr.
proof.
  proc.
  while ((b2r (!t) / p)%xr + (size O.log)%xr).
  + move => &hr; apply xle_cxr_r => |>.
  + wp; skip; move => &hr; move: (t{hr}) (O.log{hr}) => {&hr} t log; apply xle_cxr_r => ntest.
    rewrite ntest => /=.
    rewrite (eq_Ep _ _
       ((fun r => (inv p)%xr * (! test r)%xr) + (fun r => (1 + size log)%xr))).
    + move => x xx /=. rewrite of_realM; 1,2:smt(of_realM invr_ge0 ge0_mu). smt().
    rewrite EpD EpC EpZ /=; 1: smt(invr_gt0 dr_mu_test of_realK).
    rewrite Ep_mu mu_not dr_ll /= -/p.
    rewrite !to_pos_pos; 1,2,3,4:smt(mu_bounded dr_mu_test size_ge0).
  by auto.
qed.

ehoare o_bad : O.o:
    (O.bad => Q <= O.c) `|` if Q <= O.c then O.bad%xr else  (size O.log)%xr * eps%xr + (Q - O.c)%xr * (eps/p)%xr
    ==> (O.bad => Q <= O.c)  `|` if Q <= O.c then O.bad%xr else (size O.log)%xr * eps%xr + (Q - O.c)%xr * (eps/p)%xr.
proof.
  proc.
  wp.
  call /(fun x => (O.bad => Q <= O.c)
          `|` if Q < O.c then O.bad%xr else x * eps%xr + (Q - O.c)%xr * (eps/p)%xr) extend_log_size.
  + auto => &hr /=.
    case: (O.c{hr} = Q) => [ -> /= | *].
    + rewrite Ep_mu (:(fun (a : r) => a \in O.log{hr}) = mem O.log{hr}); 1: by auto.
      rewrite -of_realM /=; smt(mu_mem_le_mu1 size_ge0 eps_ge0 dr_mu1).
    case: (Q < O.c{hr}); by smt().
  auto => &hr /=; apply xle_cxr => *; split; 1:smt().
  have -> /=: (Q < O.c{hr} + 1) = (Q <= O.c{hr}) by smt().
  case (Q <= O.c{hr}); 1:smt().
  by smt(of_realM of_realD dr_mu_test).
qed.

lemma pr_bad &m (A<:Adv{-O}) : Pr[Main(A).main() @ &m : O.bad] <= eps * Q%r * (inv p).
  byehoare.
  + proc.
    call (: (O.bad => Q <= O.c)`|` if Q <= O.c then O.bad%xr else (size O.log)%xr * eps%xr + (Q - O.c)%xr * (eps/p)%xr ==> O.bad%xr).
    + proc ((O.bad => Q <= O.c)`|` if Q <= O.c then O.bad%xr else (size O.log)%xr * eps%xr + (Q - O.c)%xr * (eps/p)%xr).
      + move => &hr; apply xle_cxr => *; split; 1:smt(). by auto.
      + move => &hr; apply xle_cxr_r => *.
        by case: (O.bad{hr}) => [ /# |*]; smt(xle0x).
      by apply o_bad.
    by wp; auto; move => *; case (Q <= 0); smt(xle0x).
  + auto.
  auto.
qed.
