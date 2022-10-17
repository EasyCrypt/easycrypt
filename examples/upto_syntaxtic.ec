require import AllCore Distr StdOrder.

module M = { 
  var bad : bool

  proc set_bad () = { 
    var r; 
    r <- 0;
    bad <- true;
    r <- r + 1;
    return r;
  }

  proc set_bad_if (x:int) = { 
    var r; 
    r <- 0;
    if (x = 0) {
      bad <- true;
      r <@ set_bad ();
      r <- r + 1;
    }
    return r;
  }

  proc set_bad_while (x:int) = {
    var r, i;
    r <- 0;
    i <- 0;
    while (i <= 10) {
      r <@ set_bad();
      r <@ set_bad_if(r);
      if (i = x) {
        bad <- true;
        r <- 100;
      }
    }
    return r;
  }

  proc main() = { 
    var x;
    x <- 0;
    bad <- false; 
    x <- 1;
    x <@ set_bad(); 
    set_bad_if(100);
    set_bad_while(x);
    return x;
  }

  proc main_noinit (x:int) = {
    x <@ set_bad();
    set_bad_if(100);
    set_bad_while(x);
    return x;
  } 

}.

module M' = { 
  import var M

  proc set_bad () = { 
    var r; 
    r <- 0;
    bad <- true;
    return r;
  }

  proc set_bad_if (x:int) = { 
    var r; 
    r <- 0;
    if (x = 0) {
      bad <- true;
      r <@ set_bad ();
      r <- r + 2;
      r <- r + 10;
      r <@ set_bad();
    }
    return r;
  }

  proc set_bad_while (x:int) = {
    var r, i;
    r <- 0;
    i <- 0;
    while (i <= 10) {
      r <@ set_bad();
      r <@ set_bad_if(r);
      if (i = x) {
        bad <- true;
      }
    }
    return r;
  }

  proc main() = { 
    var x;
    x <- 0;
    bad <- false; 
    x <- 1;
    x <@ set_bad(); 
    set_bad_if(100);
    set_bad_while(x); 

    return x;
  }

  proc main_noinit (x:int) = {
    x <@ set_bad();
    set_bad_if(100);
    set_bad_while(x);
    return x;
  } 

}.

lemma Pr_main_E &m : 
   Pr[M.main() @ &m : res = 0 /\ !M.bad] = Pr[M'.main() @ &m : res = 0 /\ !M.bad].
proof. byupto. qed.

lemma Pr_main_nbad &m : 
   Pr[M.main() @ &m : !M.bad] = Pr[M'.main() @ &m : !M.bad].
proof. byupto. qed.

lemma Pr_noinit_E &m : 
   Pr[M.main_noinit(10) @ &m : res = 0 /\ !M.bad] = Pr[M'.main_noinit(10) @ &m : res = 0 /\ !M.bad].
proof. byupto. qed.

lemma Pr_noinit_nbad &m : 
   Pr[M.main_noinit(7) @ &m : !M.bad] = Pr[M'.main_noinit(7) @ &m : !M.bad].
proof. byupto. qed.

module type OT = {
  proc set_bad () : int
  proc set_bad_if (x:int) : int 
  proc set_bad_while (x:int) : int
}.

module type Adv (O:OT) = { 
  proc main () : int 
}.

lemma test (A<:Adv) &m : 
   Pr[A(M).main () @ &m : res = 100 /\ !M.bad] = Pr[A(M').main () @ &m : res = 100 /\ !M.bad].
proof. byupto. qed.


(* ------------------------------------------- *)

lemma abs_upto1 &m : 
   Pr[M.main() @ &m : res = 0] - Pr[M'.main() @ &m : res = 0] <= Pr[M.main() @ &m : res = 0 /\ M.bad].
proof.
  rewrite Pr[mu_split M.bad].
  have -> : Pr[M'.main() @ &m : res = 0] = 
         Pr[M'.main() @ &m : res = 0 /\ M.bad] + Pr[M'.main() @ &m : res = 0 /\ !M.bad] by rewrite Pr[mu_split M.bad].
  have -> : Pr[M'.main() @ &m : res = 0 /\ !M.bad] = Pr[M.main() @ &m : res = 0 /\ !M.bad].
  + byupto.
  smt(mu_bounded).
qed.

(* remove [res = 0] *)
lemma abs_upto2 &m : 
   Pr[M.main() @ &m : res = 0] - Pr[M'.main() @ &m : res = 0] <= Pr[M.main() @ &m : M.bad].
proof.
  rewrite Pr[mu_split M.bad].
  have -> : Pr[M'.main() @ &m : res = 0] = 
         Pr[M'.main() @ &m : res = 0 /\ M.bad] + Pr[M'.main() @ &m : res = 0 /\ !M.bad] by rewrite Pr[mu_split M.bad].
  have -> : Pr[M'.main() @ &m : res = 0 /\ !M.bad] = Pr[M.main() @ &m : res = 0 /\ !M.bad].
  + byupto.
  have : Pr[M.main() @ &m : res = 0 /\ M.bad] <= Pr[M.main() @ &m : M.bad]. 
  + by rewrite Pr[mu_sub].
  smt(mu_bounded).
qed.

require import StdOrder.
import RealOrder.

(* abs value *)
lemma abs_upto_max1 &m : 
  `| Pr[M.main() @ &m : res = 0] - Pr[M'.main() @ &m : res = 0]| <= 
    maxr Pr[M.main() @ &m : res = 0 /\ M.bad] Pr[M'.main() @ &m : res = 0 /\ M.bad].
proof.
  rewrite Pr[mu_split M.bad].
  have -> : Pr[M'.main() @ &m : res = 0] = 
         Pr[M'.main() @ &m : res = 0 /\ M.bad] + Pr[M'.main() @ &m : res = 0 /\ !M.bad] by rewrite Pr[mu_split M.bad].
  have -> : Pr[M'.main() @ &m : res = 0 /\ !M.bad] = Pr[M.main() @ &m : res = 0 /\ !M.bad].
  + byupto.
  smt(mu_bounded).
qed.

(* abs value : remove [res = 0] *)
lemma abs_upto_max2 &m : 
  `| Pr[M.main() @ &m : res = 0] - Pr[M'.main() @ &m : res = 0]| <= 
    maxr Pr[M.main() @ &m : M.bad] Pr[M'.main() @ &m : M.bad].
proof.
  have := abs_upto_max1 &m.
  have : Pr[M.main() @ &m : res = 0 /\ M.bad] <= Pr[M.main() @ &m : M.bad] by rewrite Pr[mu_sub].
  have /#: Pr[M'.main() @ &m : res = 0 /\ M.bad] <= Pr[M'.main() @ &m : M.bad] by rewrite Pr[mu_sub].
qed.

(* This is the core tactic *)
(* [1: E /\ !bad] = [2: E /\ !bad] *)
lemma test1 &m : 
   Pr[M.main() @ &m : res = 0 /\ !M.bad] =  Pr[M'.main() @ &m : res = 0 /\ !M.bad].
byupto.
qed.

(* This are build on top of the core tactic *)

lemma test1_sub &m : 
   Pr[M.main() @ &m : res = 0] - Pr[M'.main() @ &m : res = 0]  =
   Pr[M.main() @ &m : res = 0 /\ M.bad] - Pr[M'.main() @ &m : res = 0 /\ M.bad].
byupto.
qed.

(* [1: E] <= [1: E /\ !BAD] + [1: E /\ BAD] *)
lemma test2 &m : 
  Pr[M.main() @ &m : res = 0] <= 
  Pr[M.main() @ &m : res = 0 /\ !M.bad] + Pr[M.main() @ &m : res = 0 /\ M.bad].
byupto.
qed.

(* [1: E] <= [2: E /\ !BAD] + [1: E /\ BAD] *)
lemma test3 &m : 
  Pr[M.main() @ &m : res = 0] <= 
  Pr[M'.main() @ &m : res = 0 /\ !M.bad] + Pr[M.main() @ &m : res = 0 /\ M.bad].
byupto.
qed.

(* [1: E] <= [2: E] + [1: E /\ BAD] *)
lemma test4 &m : 
  Pr[M.main() @ &m : res = 0] <= 
  Pr[M'.main() @ &m : res = 0] + Pr[M.main() @ &m : res = 0 /\ M.bad].
byupto.
qed.

(* [1: E] <= [2: E /\ !BAD] + [1:BAD] *)
lemma test5 &m : 
  Pr[M.main() @ &m : res = 0] <= 
  Pr[M'.main() @ &m : res = 0 /\ !M.bad] + Pr[M.main() @ &m : M.bad].
byupto.
qed.

(* [1: E] <= [2: E] + [1:BAD] *)
lemma test6 &m : 
  Pr[M.main() @ &m : res = 0] <= 
  Pr[M'.main() @ &m : res = 0] + Pr[M.main() @ &m : M.bad].
byupto.
qed.

(* `| [1: E] - [2: E]| < `| [1: E /\ bad] - [2: E /\ bad]| *)
lemma test7 &m : 
  `| Pr[M.main() @ &m : res = 0] - Pr[M'.main() @ &m : res = 0] | <=
  `| Pr[M.main() @ &m : res = 0 /\ M.bad] - Pr[M'.main() @ &m : res = 0 /\ M.bad ] |.
byupto.
qed.

(* `| [1: E] - [2: E]| < maxr [1: E /\ bad]  [2: E /\ bad] *)
lemma test8 &m : 
  `| Pr[M.main() @ &m : res = 0] - Pr[M'.main() @ &m : res = 0] | <=
  maxr  Pr[M.main() @ &m : res = 0 /\ M.bad] Pr[M'.main() @ &m : res = 0 /\ M.bad ].
byupto.
qed.

(* `| [1: E] - [2: E]| < maxr [1: bad]  [2: E /\ bad] *)
lemma test9 &m : 
  `| Pr[M.main() @ &m : res = 0] - Pr[M'.main() @ &m : res = 0] | <=
  maxr  Pr[M.main() @ &m : M.bad] Pr[M'.main() @ &m : res = 0 /\ M.bad ].
byupto.
qed.

(* `| [1: E] - [2: E]| < maxr [1: E /\ bad]  [2: bad] *)
lemma test10 &m : 
  `| Pr[M.main() @ &m : res = 0] - Pr[M'.main() @ &m : res = 0] | <=
  maxr  Pr[M.main() @ &m : res = 0 /\ M.bad] Pr[M'.main() @ &m : M.bad ].
byupto.
qed.

(* `| [1: E] - [2: E]| < maxr [1: E]  [2: bad] *)
lemma test12 &m : 
  `| Pr[M.main() @ &m : res = 0] - Pr[M'.main() @ &m : res = 0] | <=
  maxr  Pr[M.main() @ &m : M.bad] Pr[M'.main() @ &m : M.bad ].
byupto.
qed.
















    




     
 




