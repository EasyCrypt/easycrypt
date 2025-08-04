require import AllCore.

exception assume.
exception assert.

module M' ={
  proc truc (x:int) : int = {
    if (x = 3)  {
       raise assume;
    }
    if (x=3) {
        raise assert;
      }
  return x;
  }
}.

op p7: bool.
op p1: bool.
op p2: bool.
op p3: bool.

lemma assume_assert :
hoare [M'.truc : p7 ==> p3 | assume:p1 |assert: p2 ].
    proof.
admitted.

op p8: bool.
op q1: bool.
op q2: bool.
op q3: bool.

lemma assert_assume :
hoare [M'.truc : p8 ==> q3 | assume:q1 |assert: q2 ].
    proof.
admitted.

op p4: bool.
op p5: bool.
op p6: bool.
op p9: bool.
lemma assert_assume' :
hoare [M'.truc : p9 ==> p4 | assume:p6 |assert: p5 ].
    proof.
      conseq (assume_assert) (assert_assume).
      + admit.
      + admit.
      + admit.
      + admit.
    qed.

exception e1.
exception e2.
exception e3.

module M ={
  proc f1 (x:int) : int = {
    if (x = 3)  {
       raise e1;
    } else {
        x <- 5;
    }
    return x;
  }

 proc f2 (x:int) : int = {
    if (x = 3)  {
      x <- x;
      x <@ f1(x);
    } else {
      x <@ f1(x);
    }
    return x;
  }
}.


(* Multiple time post for the same exception *)

lemma l_f1 (_x: int):
hoare [M.f1 : _x = x ==> (4 < res) | e1:_x = 3 | e2:false ].
    proof.
      proc.
       conseq (: _ ==> x = 5 | e1: p1 | e2: p2 ).
      + auto.
      + auto. admit.
      + admit.
      + admit.
    qed.

lemma l_f2 (_x: int):
hoare [M.f2 : p9 ==> p4 | e1: p2 | e2:p1 | e3: p6 ].
    proof.
      proc.
      if.
      + call (: p5 ==> p3 | e1 : p9 | e2: p7).
      proc.
      wp.
      admit.
      + admit.
      + call (l_f1 _x);auto. admit.
    qed.
