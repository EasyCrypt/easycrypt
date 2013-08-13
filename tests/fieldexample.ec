(* -------------------------------------------------------------------- *)
require import Int.
require AlgTactic.

instance ring with int
  op rzero = Int.zero
  op rone  = Int.one
  op add   = Int.( + )
  op opp   = [-]
  op mul   = Int.( * )
  op expr  = Int.Power.( ^ )
  op sub   = Int.(-)

  proof oner_neq0 by smt
  proof addr0     by smt
  proof addrA     by smt
  proof addrC     by smt
  proof addrN     by smt
  proof mulr1     by smt
  proof mulrA     by smt
  proof mulrC     by smt
  proof mulrDl    by smt
  proof expr0     by smt
  proof exprS     by smt
  proof subrE     by smt.

lemma b25  (a b : int):
  (a + b) ^ 25 = ((((((((((((((((((((((((b + 25 * a) * b + 300 * a ^ 2) * b + 2300 * a ^ 3) *
                     b + 12650 * a ^ 4) *
                    b + 53130 * a ^ 5) *
                   b + 177100 * a ^ 6) *
                  b + 480700 * a ^ 7) *
                 b + 1081575 * a ^ 8) *
                b + 2042975 * a ^ 9) *
               b + 3268760 * a ^ 10) *
              b + 4457400 * a ^ 11) *
             b + 5200300 * a ^ 12) *
            b + 5200300 * a ^ 13) *
           b + 4457400 * a ^ 14) *
          b + 3268760 * a ^ 15) *
         b + 2042975 * a ^ 16) *
        b + 1081575 * a ^ 17) *
       b + 480700 * a ^ 18) *
      b + 177100 * a ^ 19) *
     b + 53130 * a ^ 20) *
    b + 12650 * a ^ 21) *
   b + 2300 * a ^ 22) *
  b + 300 * a ^ 23) *
 b + 25 * a ^ 24) *
b + (a ^ 25).
proof. by ring. qed.

lemma binom (x y : int): ((x+y) ^2) = (x^2 + 2* x * y + y^2).
proof. by ring. qed.

(*
require import Prime_field.

const k : int.

axiom k_pos : 0 <= k.

clone import Prime_field as Zq with op q = k.

type zq = Zq.gf_q.

op uint : zq distr = Zq.Dgf_q.dgf_q.

import Zq.

op ( ^^ ) : zq -> int -> zq.
axiom pow1 : forall (a : zq), forall ( i : int), i > 0 => a ^^ i = Zq.( * ) a (a ^^ (i-1)).
axiom pow0 : forall (a : zq), a <> Zq.gf_q0 =>  a ^^ 0 = Zq.gf_q1.
axiom pow00 : forall ( i : int), Zq.gf_q0 ^^ i = Zq.gf_q0.

lemma rbinom : forall (x y : zq),
    Zq.( * ) ((Zq.(-) x y) ^^ 2 ) (Zq.(+) Zq.gf_q1 Zq.gf_q1) = 
    Zq.( * ) ( Zq.(-) (Zq.(+) ( x ^^ 2) (y ^^ 2)) ( Zq.( * ) (Zq.(+) x x) y)) (Zq.(+) Zq.gf_q1 Zq.gf_q1).
proof.
intros x y.
(*ring Zq.(+) Zq.( * ) ( ^^ ) Zq.(-) Zq.gf_q0 Zq.gf_q1 ( = ).*)
field Zq.(+) Zq.( * ) ( ^^ ) Zq.inv Zq.(-) Zq.(/) Zq.gf_q0 Zq.gf_q1 (=).
qed.

lemma b24 : forall (a b c: zq) ,
    a = b =>
    c = (Zq.( * ) (Zq.(+) Zq.gf_q1 Zq.gf_q1) a) =>
    (Zq.( * ) c c) = Zq.( * )(Zq.( * ) b b) (Zq.(+) (Zq.(+) Zq.gf_q1  Zq.gf_q1) (Zq.(+) Zq.gf_q1  Zq.gf_q1)).
proof.
intros a b c T U.
ring_simplify Zq.(+) Zq.( * ) (^^) Zq.(-) Zq.gf_q0 Zq.gf_q1 (=) T U.
qed.

lemma fb24 : forall (a b c: zq) ,
    a = b =>
    c = (Zq.( * ) (Zq.(+) Zq.gf_q1 Zq.gf_q1) a) =>
    (Zq.( * ) c c) = Zq.( * )(Zq.( * ) b b) (Zq.(+) (Zq.(+) Zq.gf_q1  Zq.gf_q1) (Zq.(+) Zq.gf_q1  Zq.gf_q1)).
proof.
intros a b c T U.
field Zq.(+) Zq.( * ) ( ^^ ) Zq.inv Zq.(-) Zq.(/) Zq.gf_q0 Zq.gf_q1 (=) T U.
qed.

lemma b25 : forall (a b : int) , (a + b) ^ 25 = ((((((((((((((((((((((((b + 25 * a) * b + 300 * a ^ 2) * b + 2300 * a ^ 3) *
                     b + 12650 * a ^ 4) *
                    b + 53130 * a ^ 5) *
                   b + 177100 * a ^ 6) *
                  b + 480700 * a ^ 7) *
                 b + 1081575 * a ^ 8) *
                b + 2042975 * a ^ 9) *
               b + 3268760 * a ^ 10) *
              b + 4457400 * a ^ 11) *
             b + 5200300 * a ^ 12) *
            b + 5200300 * a ^ 13) *
           b + 4457400 * a ^ 14) *
          b + 3268760 * a ^ 15) *
         b + 2042975 * a ^ 16) *
        b + 1081575 * a ^ 17) *
       b + 480700 * a ^ 18) *
      b + 177100 * a ^ 19) *
     b + 53130 * a ^ 20) *
    b + 12650 * a ^ 21) *
   b + 2300 * a ^ 22) *
  b + 300 * a ^ 23) *
 b + 25 * a ^ 24) *
b + (a ^ 25).
proof.
intros a b.
ring Int.(+) Int.( * ) (^) Int.(-) 0 1 ( = ).
qed.

lemma binom : forall (x y : int), ((x+y) ^2) = (x^2 + 2* x * y + y^2).
proof.
intros x y.
ring Int.(+) Int.( * ) (^) Int.(-) 0 1 ( = ).
(*field (+) ( * ) ( ^ ) inv (-) (/) 0 1 (=).*)
qed.

(* OT examples*)

lemma check : forall (a b c d r s : int),
       a * ( c * s + r) + c * d - c * (a * s +b * r + d) = r * (a - b * c).
proof.
intros a b c d r s.
ring_simplify Int.(+) Int.( * ) (^) Int.(-) 0 1 ( = ).
qed.

lemma bij1_fst:
forall (a b c d : zq),Zq.(-) a (Zq.( * ) b c) <> Zq.gf_q0 =>
  forall (r s : zq),
    Zq.(/) (Zq.(-) (Zq.(+)
      (Zq.( * ) a  (Zq.( + ) (Zq.( * ) c s)  r))
       (Zq.( * ) c d)) 
       (Zq.( * ) c (Zq.(+) (Zq.( * ) a s) (Zq.(+) (Zq.( * ) b r) d))))
          (Zq.(-) a  (Zq.( * ) b c)) = r.
proof.
intros a b c d H r s.
field Zq.(+) Zq.( * ) ( ^^ ) Zq.inv Zq.(-) Zq.(/) Zq.gf_q0 Zq.gf_q1 (=).
qed.

lemma bij1_snd:
forall (a b c d : zq), Zq.(-) a  (Zq.( * ) b c) <> Zq.gf_q0 =>
  forall (r s : zq),
   Zq.(/) (
      Zq.(-) 
      (Zq.(-) (Zq.(+) (Zq.( * ) a s) (Zq.(+) (Zq.( * ) b r) d)) d)
        (Zq.( * ) b (Zq.(+) (Zq.( * ) c s) r)))
 (Zq.(-) a  (Zq.( * ) b c)) = s.
proof.
intros a b c d H r s.
field Zq.(+) Zq.( * ) ( ^^ ) Zq.inv Zq.(-) Zq.(/) Zq.gf_q0 Zq.gf_q1 (=).
qed.

lemma bij1:
forall (a b c d : zq), Zq.(-) a  (Zq.( * ) b c) <> Zq.gf_q0 =>
  forall (r s : zq),
    let (u,v) = (Zq.(+) (Zq.(+) (Zq.( * ) a s) (Zq.( * ) b r)) d,Zq.(+) (Zq.( * ) c s) r) in 
    ( Zq.(/) (Zq.(-) (Zq.(+) (Zq.( * ) a v) (Zq.( * ) c d)) (Zq.( * ) c u)) (Zq.(-) a (Zq.( * ) b c)), Zq.(/) (Zq.(-) (Zq.(-) u d) (Zq.( * ) b v)) (Zq.(-) a (Zq.( * ) b c))) = (r,s).
proof.
intros a b c d H r s.
split.
field Zq.(+) Zq.( * ) ( ^^ ) Zq.inv Zq.(-) Zq.(/) Zq.gf_q0 Zq.gf_q1 (=).
field Zq.(+) Zq.( * ) ( ^^ ) Zq.inv Zq.(-) Zq.(/) Zq.gf_q0 Zq.gf_q1 (=).
qed.

lemma bij2_fst:
forall (a b c d : zq), Zq.(-) a  (Zq.( * ) b c) <> Zq.gf_q0 =>
  forall (u  v : zq),
    Zq.(+) (Zq.(/) (Zq.( * ) a ( Zq.(-) (Zq.(-) u d) (Zq.( * ) b v)))  (Zq.(-) a (Zq.( * ) b c))) (Zq.(+) ( Zq.( * ) b (Zq.(/) (Zq.(-) (Zq.(+) (Zq.( * ) a v) (Zq.( * ) c d)) (Zq.( * ) c u)) (Zq.(-) a (Zq.( * ) b  c)))) d) = u.
proof.
intros a b c d H u v.
field Zq.(+) Zq.( * ) ( ^^ ) Zq.inv Zq.(-) Zq.(/) Zq.gf_q0 Zq.gf_q1 (=).
qed.

lemma bij2_snd:
forall (a b c d : zq), Zq.(-) a (Zq.( * ) b c) <> Zq.gf_q0 =>
  forall (u  v : zq),
   Zq.(+) (Zq.(/) (Zq.( * ) c ( Zq.(-) (Zq.(-) u d) (Zq.( * ) b v))) (Zq.(-) a (Zq.( * ) b c))) (Zq.(/) (Zq.(-) (Zq.(+) (Zq.( * ) a v) (Zq.( * ) c d)) (Zq.( * ) c u)) (Zq.(-) a (Zq.( * ) b c))) = v.
proof.
intros a b c d H u v.
field Zq.(+) Zq.( * ) ( ^^ ) Zq.inv Zq.(-) Zq.(/) Zq.gf_q0 Zq.gf_q1 (=).
qed.

lemma bij2:
forall (a b c d : zq), Zq.(-) a (Zq.( * ) b c) <> Zq.gf_q0 =>
  forall (u  v : zq),
   let (r,s) = (Zq.(/) (Zq.(-) (Zq.(+) (Zq.( * ) a v) (Zq.( * ) c d)) (Zq.( * ) c u)) (Zq.(-) a (Zq.( * ) b c)),Zq.(/) ( Zq.(-) (Zq.(-) u d) (Zq.( * ) b v)) (Zq.(-) a (Zq.( * ) b  c))) in 
   ( Zq.(+) (Zq.(+) (Zq.( * ) a s) (Zq.( * ) b r)) d,Zq.(+) (Zq.( * ) c s) r) = (u,v).
proof.
intros a b c d H u v.
split.
field Zq.(+) Zq.( * ) ( ^^ ) Zq.inv Zq.(-) Zq.(/) Zq.gf_q0 Zq.gf_q1 (=).
field Zq.(+) Zq.( * ) ( ^^ ) Zq.inv Zq.(-) Zq.(/) Zq.gf_q0 Zq.gf_q1 (=).
qed.
*)
