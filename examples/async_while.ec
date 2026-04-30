require import AllCore.

   module M = {
     proc up_to_10(x : int) : int = {
       while (x < 10) {
         x <- x + 1;
       }
       return x;
     }
     proc up_to_10_by_2(x : int) : int = {
       while (x < 10) {
         x <- x + 1;
         if ( x < 10)  x <- x + 1;
       }
       return x;
     }

   }.

   lemma asynctwhile_example :
   equiv[M.up_to_10 ~ M.up_to_10_by_2 : ={x} ==> ={res}].
   proof.
     proc.
     async while
     [ (fun r => x <= r + 1), (x{1} ) ]
     [ (fun r => x <= r ), (x{2} ) ]
     (!(x{1} < 10)) (!(x{2} < 10))
     :  (x{1} = x{2}).
       + move=> &1 &2 => /#.
       + move => v1 v2 //=.
         unroll {1} 1.
         unroll {1} 2.
         unroll {2} 1.
         rcondt {1} 1; auto.
         rcondt {2} 1; auto.
         sp 1 1.
         if => //.
         sp 1 1.
         while (!(x{1} < 10 /\ (x{1} < 10 /\ (x{1} <= v1 + 1))) /\
         !(x{2} < 10 /\ (x{2} < 10 /\ (x{2} <= v2 )))  /\ ={x}); auto => /#.
         while (!(x{1} < 10 /\ (x{1} < 10 /\ (x{1} <= v1 + 1))) /\
         !(x{2} < 10 /\ (x{2} < 10 /\ (x{2} <= v2 )))  /\ ={x}); auto => /#.
       + move => &2; exfalso=> &1 ? /#.
       + move => &1; exfalso=> &2 ? /#.
       + exfalso => /#.
       + exfalso  => /#.
       + by auto.
   qed.

 module M1 = {
  proc spin_once(i1:bool): bool = {
    while (i1) {
      i1 <- !i1;
    }
    return i1;
  }

  proc spin(i2:bool): bool = {
    while (i2) {
    }
    return i2;
  }
}.

op b0:bool.
op b1:bool.
op b2:bool.
op b3:bool.
op b4:bool.
op f1:int -> bool.
op n1:int.
op f2:int -> bool.
op n2:int.

equiv L: M1.spin_once ~ M1.spin:
  b0 ==> b4.
proof.
proc.
  async while [f1,n1] [f2,n2] (b1) (b2) : (b3).
  - admit. (* soundness condition*)
  - admit. (*left*)
  - admit. (*right*)
  - admit. (*lockstep equiv*)
  - admit. (*losless left*)
  - admit. (*losless right*)
  - admit. (*invariant implies post*)
qed.
