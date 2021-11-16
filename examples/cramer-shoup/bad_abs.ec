require import AllCore Distr.

type input_a.  
type output_a.  

module type Adv = {
  proc a(x:input_a) : output_a
}.

type input_m.

module type Main(A:Adv) = {
  proc main(x:input_m): bool
}.  

module type NegA (A:Adv) = {
  proc a(x:input_a) : output_a {A.a}
}.

section TEST.


   declare module M1 <: Main.
   declare module M2 <: Main.
   declare module N <: NegA.
   declare module A <: Adv.

   lemma test : 
     forall (pre : input_m -> input_m -> glob M1 -> glob M2 -> bool)
            (E1: glob M1 -> glob A -> bool -> bool) 
            (E2: glob M2 -> glob A -> bool -> bool) 
            (B : glob M2 -> glob A -> bool),
       (equiv [M1(A).main ~ M2(A).main : pre x{1} x{2} (glob M1){1} (glob M2){2} /\ ={glob A} ==> 
                       !(B (glob M2) (glob A)){2} => 
                          (E1 (glob M1) (glob A) res){1} = (E2 (glob M2) (glob A) res){2}]) =>
       (equiv [M1(N(A)).main ~ M2(N(A)).main : pre x{1} x{2} (glob M1){1} (glob M2){2} /\ ={glob A} ==> 
                       !(B (glob M2) (glob A)){2} => 
                          (E1 (glob M1) (glob A) res){1} = (E2 (glob M2) (glob A) res){2}]) =>
       (forall &m vx,  Pr[M1(N(A)).main(vx) @ &m : E1 (glob M1) (glob A) res] =
                       1%r - Pr[M1(A).main(vx) @ &m : E1 (glob M1) (glob A) res]) =>
       (forall &m vx,  Pr[M2(N(A)).main(vx) @ &m : E2 (glob M2) (glob A) res] = 
                       1%r - Pr[M2(A).main(vx) @ &m : E2 (glob M2) (glob A) res]) =>
       (forall &m vx,  Pr[M2(N(A)).main(vx) @ &m : B (glob M2) (glob A)] = Pr[M2(A).main(vx) @ &m : B (glob M2) (glob A)]) =>
       forall &m1 &m2 vx1 vx2, pre vx1 vx2 (glob M1){m1} (glob M2){m2} => (glob A){m1} = (glob A){m2} => 
         `|Pr[M1(A).main(vx1) @ &m1 : E1 (glob M1) (glob A) res] - Pr[M2(A).main(vx2) @ &m2 : E2 (glob M2) (glob A) res] | <=
          Pr[M2(A).main(vx2) @ &m2 : B (glob M2) (glob A)].
   proof.
     move=> pre E1 E2 B eA eNA N1 N2 NB &m1 &m2 vx1 vx2 Hpre HglobA. 
     case: (Pr[M1(A).main(vx1) @ &m1 : E1 (glob M1) (glob A) res] <= 
            Pr[M2(A).main(vx2) @ &m2 : E2 (glob M2) (glob A) res]) => Hle.
     have ->: 
      `|Pr[M1(A).main(vx1) @ &m1 : E1 (glob M1) (glob A) res] - Pr[M2(A).main(vx2) @ &m2 : E2 (glob M2) (glob A) res]| = 
      Pr[M2(A).main(vx2) @ &m2 : E2 (glob M2) (glob A) res] - Pr[M1(A).main(vx1) @ &m1 : E1 (glob M1) (glob A) res] by smt ().     
     have : Pr[M1(N(A)).main(vx1) @ &m1 : E1 (glob M1) (glob A) res] <= 
            Pr[M2(N(A)).main(vx2) @ &m2 : E2 (glob M2) (glob A) res \/ B (glob M2) (glob A)].
     + by byequiv eNA => // &1 &2 /#. 
     rewrite Pr [mu_or]; rewrite (N1 &m1 vx1) (N2 &m2 vx2) (NB &m2 vx2); smt (mu_bounded).
     have ->: 
      `|Pr[M1(A).main(vx1) @ &m1 : E1 (glob M1) (glob A) res] - Pr[M2(A).main(vx2) @ &m2 : E2 (glob M2) (glob A) res]| = 
      Pr[M1(A).main(vx1) @ &m1 : E1 (glob M1) (glob A) res] -Pr[M2(A).main(vx2) @ &m2 : E2 (glob M2) (glob A) res] by smt ().  
     have : Pr[M1(A).main(vx1) @ &m1 : E1 (glob M1) (glob A) res] <= 
            Pr[M2(A).main(vx2) @ &m2 : E2 (glob M2) (glob A) res \/ B (glob M2) (glob A)].
     + by byequiv eA => // &1 &2 /#. 
     rewrite Pr [mu_or]; smt (mu_bounded).
   qed.
  
end section TEST.

section TEST1.


   declare module M1 <: Main.
   declare module M2 <: Main.
   declare module N <: NegA.
   declare module A <: Adv.

   lemma test1 : 
     forall (pre : input_m -> input_m -> glob M1 -> glob M2 -> bool)
            (E1: glob M1 -> glob A -> bool -> bool) 
            (E2: glob M2 -> glob A -> bool -> bool) 
            (B : glob M2 -> glob A -> bool),
       (equiv [M1(A).main ~ M2(A).main : pre x{1} x{2} (glob M1){1} (glob M2){2} /\ ={glob A} ==> 
                       !(B (glob M2) (glob A)){2} => 
                          (E1 (glob M1) (glob A) res){1} = (E2 (glob M2) (glob A) res){2}]) =>
       (equiv [M1(N(A)).main ~ M2(N(A)).main : pre x{1} x{2} (glob M1){1} (glob M2){2} /\ ={glob A} ==> 
                       !(B (glob M2) (glob A)){2} => 
                          (E1 (glob M1) (glob A) res){1} = (E2 (glob M2) (glob A) res){2}]) =>
       (equiv [ M1(N(A)).main ~ M1(A).main : ={glob M1, glob A}  ==> (E1 (glob M1) (glob A) res){1} = !(E1 (glob M1) (glob A) res){2}]) =>
       (equiv [ M2(N(A)).main ~ M2(A).main : ={glob M2, glob A}  ==> (E2 (glob M2) (glob A) res){1} = !(E2 (glob M2) (glob A) res){2} /\
                                                                     (B (glob M2) (glob A)){1} = (B (glob M2) (glob A)){2}]) => 
       islossless M1(A).main =>
       islossless M2(A).main =>
       forall &m1 &m2 vx1 vx2, pre vx1 vx2 (glob M1){m1} (glob M2){m2} => (glob A){m1} = (glob A){m2} => 
         `|Pr[M1(A).main(vx1) @ &m1 : E1 (glob M1) (glob A) res] - Pr[M2(A).main(vx2) @ &m2 : E2 (glob M2) (glob A) res] | <=
          Pr[M2(A).main(vx2) @ &m2 : B (glob M2) (glob A)].
   proof.
     move=> pre E1 E2 B eA eNA e1 e2 ll1 ll2 &m1 &m2 vx1 vx2 Hpre HglobA. 
     apply (test M1 M2 N A pre E1 E2 B eA eNA _ _ _ &m1 &m2 vx1 vx2 Hpre HglobA).
     + move=> &m vx. 
       have -> : Pr[M1(N(A)).main(vx) @ &m : E1 (glob M1) (glob A) res] = Pr[M1(A).main(vx) @ &m : !E1 (glob M1) (glob A) res].
       + byequiv e1 => // /#. 
       by rewrite Pr [mu_not];congr;byphoare ll1.
     + move=> &m vx. 
       have -> : Pr[M2(N(A)).main(vx) @ &m : E2 (glob M2) (glob A) res] = Pr[M2(A).main(vx) @ &m : !E2 (glob M2) (glob A) res].
       + byequiv e2 => // /#. 
       by rewrite Pr [mu_not];congr;byphoare ll2.
     by move=> &m vx;byequiv e2 => // /#.
   qed.

end section TEST1.

