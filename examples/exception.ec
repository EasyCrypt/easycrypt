require import AllCore.

exception e1.
exception e2.

module M ={
  proc truc (x:int) : int = {
    if (x = 3)  {
       raise e1;
    } else { x <- 5; }
  return x;
  }
}.

lemma truc (_x: int):
hoare [M.truc : _x = x ==> (4 < res) | e1:_x = 3 | e2:false ].
    proof.
      proc.
       conseq (: _ ==> x = 5).
      + auto.
      + auto.
    qed.

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

(* lemma assume_assert : *)
(* hoare [M'.truc : true ==> true | assume:true |assert: false ]. *)
(*     proof. *)
(*       proc. *)
(*       wp. *)
(*     auto. *)
(*     qed. *)

(* lemma assert_assume : *)
(* hoare [M'.truc : x <> 3 ==> true | assume:false |assert: true ]. *)
(*     proof. *)
(*       proc. *)
(*       wp. *)
(*     auto. *)
(*     qed. *)

op p1: bool.
op p2: bool.
op p3: bool.
op p4: bool.
op p5: bool.
op p6: bool.
op p7: bool.
op p8: bool.
op p9: bool.

lemma assume_assert :
hoare [M'.truc : p7 ==> p3 | assume:p1 |assert: p2 ].
    proof.
admitted.

op q1: bool.
op q2: bool.
op q3: bool.


  lemma assert_assume :
hoare [M'.truc : p8 ==> q3 | assume:q1 |assert: q2 ].
    proof.
admitted.


  lemma assert_assume' :
hoare [M'.truc : p9 ==> p4 | assume:p6 |assert: p5 ].
    proof.
      conseq (assume_assert) (assert_assume).
      + admit.
      + admit.
      + admit.
      + admit.
    qed.
