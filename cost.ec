require import Distr DBool Int List CHoareTactic StdBigop.
import Bigint IntExtra.
require BitWord ROM.

(*****************)
(* Example BR93: *)
(*****************)

(* Plaintexts                                                           *)
op k : { int | 0 < k } as gt0_k.

clone import BitWord as Plaintext with
  op n <- k
proof gt0_n by exact/gt0_k
rename
  "word" as "ptxt"
  "dunifin" as "dptxt".
import DWord.

(* Nonces                                                               *)
op l : { int | 0 < l } as gt0_l.

clone import BitWord as Randomness with
  op n <- l
proof gt0_n by exact/gt0_l
rename
  "word" as "rand"
  "dunifin" as "drand".
import DWord.

(* Ciphertexts                                                          *)
op n = l + k.
lemma gt0_n: 0 < n by smt(gt0_k gt0_l).

clone import BitWord as Ciphertext with
  op n <- n
proof gt0_n by exact/Self.gt0_n
rename "word" as "ctxt".

(* Parsing and Formatting                                               *)
op (||) (r:rand) (p:ptxt) : ctxt = mkctxt ((ofrand r) ++ (ofptxt p)).

op parse (c:ctxt): rand * ptxt =
  (mkrand (take l (ofctxt c)),mkptxt (drop l (ofctxt c))).

lemma parseK r p: parse (r || p) = (r,p).
proof.
rewrite /parse /(||) ofctxtK 1:size_cat 1:size_rand 1:size_ptxt //=.
by rewrite take_cat drop_cat size_rand take0 drop0 cats0 mkrandK mkptxtK.
qed.

lemma formatI (r : rand) (p : ptxt) r' p':
  (r || p) = (r' || p') => (r,p) = (r',p').
proof. by move=> h; rewrite -(@parseK r p) -(@parseK r' p') h. qed.

(* A set `pkey * skey` of keypairs, equipped with                       *)
(*                         a lossless, full, uniform distribution dkeys *)
type pkey, skey.
op dkeys: { (pkey * skey) distr |    is_lossless dkeys
                                  /\ is_funiform dkeys } as dkeys_llfuni.

(* A family `f` of trapdoor permutations over `rand`,                   *)
(*        indexed by `pkey`, with inverse family `fi` indexed by `skey` *)
op f : pkey -> rand -> rand.
op fi: skey -> rand -> rand.
axiom fK pk sk x: (pk,sk) \in dkeys => fi sk (f pk x) = x.


(* Random Oracle                                                        *)
clone import ROM.Lazy as H with
  type from      <- rand,
  type to        <- ptxt,
  op   dsample _ <- dptxt.

(************************************************************************)
(* Costs of various operators. *)
schema cost_cons ['a] {e : 'a} {l : 'a list} : 
    cost[true : e :: l] =   
    cost[true : e] + cost[true : l] + 1.

schema cost_nil ['a] : cost[true : [<:'a>]] = 1.

schema cost_pp {r : rand} {p : ptxt} :
  cost[true : r || p] = 
  cost[true : r] + cost[true : p] + 1.

schema cost_dptxt : cost[true : dptxt] = 1.

schema cost_pos ['a] {e : 'a} : 0 <= cost[true : e].

hint simplify cost_cons.
hint simplify cost_nil.
hint simplify cost_pp.
hint simplify cost_dptxt.

(************************************************************************)
module type Oracle = {
  proc init () : unit
  proc o (x : rand) : ptxt
}.

module type AOracle = {
  proc o (x : rand) : ptxt
}.

op k1 : int.
op k2 : int.

axiom k1p : 0 <= k1.
axiom k2p : 0 <= k2.

module type Adv (H : AOracle) = {
  proc a1(p:pkey): (ptxt * ptxt)
  proc a2(c:ctxt): bool         
}.

(*****************************************)
(* Other example, of the accepted syntax *)

(* We have two possibility to give module restrictions. *)
(* We can give the restrictions function by function, e.g.: *)
module type OAdv (H1 : Oracle) (H : AOracle) = {
  proc a1(x : pkey) : ptxt * ptxt {H.o : k1, H1.o : 1} 
  proc a2(x : ctxt) : bool        {H.o : k2, H1.o : 3} 
}.

(* Or we can  give the restrictions at the top-level, e.g.: *)
module type OAdvBis (H1 : Oracle, H : AOracle) 
  [a1 : {H.o, H1.o; H.o : k1, H1.o : 1 },
   a2 : {H.o, H1.o; H.o : k2, H1.o : 3 }]
 = {
  proc a1(p:pkey): (ptxt * ptxt)
  proc a2(c:ctxt): bool
}.
(*****************************************)

(* Inverter *)
module I (A : Adv) (H : Oracle) = {
  var qs : rand list

  module QRO = {
    proc o (x : rand) = {
      var r;
      qs <- x :: qs;
      r <- H.o(x);
      return r;
    }
  }
  module A0 = A(QRO)

  proc invert(pk : pkey, y : rand) : rand = {
    var x, m0, m1, h, b;

    qs <- [];
    H.init();
    (m0,m1) <- A0.a1(pk);  
    h <$ dptxt;
    b <- A0.a2(y || h);
    x <- nth witness qs (find (fun p => f pk p = y) qs);
    return  x;
  }
}.

(* Same as I, but using a while-loop to find the element in the list. *)
module IW (A : Adv) (H : Oracle) = {
  var qs : rand list

  module QRO = {
    proc o (x : rand) = {
      var r;
      qs <- x :: qs;
      r <- H.o(x);
      return r;
    }
  }
  module A0 = A(QRO)

  proc invert(pk : pkey, y : rand) : rand = {
    var r, x, m0, m1, h, b;
    var qs0;

    qs <- [];
    H.init();
    (m0,m1) <- A0.a1(pk);  
    h <$ dptxt;
    b <- A0.a2(y || h);

    r <- witness; 
    qs0 <- qs;
    while (qs0 <> []){
      x = head witness qs0; 
      if (f pk x = y) {
        r <- x; qs0 <- [];
      } else {
        qs0 <- drop 1 qs0;
      }
    }
    return  r;
  }
}.

section.
  declare module H : Oracle {-I, -IW}. 
  declare module A : Adv {-I, -IW, -H} [a1 : {#H.o : k1}, a2 : {#H.o : k2}].

  local module I0  = I(A,H).
  local module IW0 = IW(A,H).

  local equiv eq_I_IW: I0.invert ~ IW0.invert:
    ={arg} /\ ={glob H, glob A} ==> ={res}.
  proof.
    proc.  
    seq 5 5 : (={glob H, glob A, b,h, pk, y} /\ I.qs{1} = IW.qs{2}); first by sim. 
    while {2} (
      if qs0 = [] then 
         r = nth witness IW.qs (find (fun (p0 : rand) => f pk p0 = y) IW.qs)
      else 
       exists i, r = witness /\ 0 <= i < size IW.qs /\ qs0 = drop i IW.qs /\ !has (fun x => f pk x = y) (take i IW.qs)){2}
     (size qs0{2}).
    + move=> &1 z; auto => &2 />.
      case: (qs0{2}) => //= hd qs0 [i />] h0i hi hdr hhas.
      have heq : IW.qs{2} = take i IW.qs{2} ++ hd :: qs0.
      + by rewrite hdr cat_take_drop.
      rewrite heq; move: hhas; (pose tk := take i IW.qs{2}) => hhas.
      have heq1 : 
       nth witness (tk ++ hd :: qs0) (find (fun (p0 : rand) => f pk{2} p0 = y{2}) (tk ++ hd :: qs0)) =
       nth witness (hd :: qs0) (find (fun (p0 : rand) => f pk{2} p0 = y{2}) (hd :: qs0)).
      + by rewrite find_cat hhas /= nth_cat; smt (find_ge0).
      split. 
      + by move=> heq2;rewrite heq2 heq1 /= heq2 /=; smt (size_ge0).  
      rewrite heq1 drop0 => hy; split;2:smt().
      split.
      + by move=> />;rewrite hy.
      move=> hqs; exists (i + 1).
      rewrite size_cat /= -cat_rcons.
      have -> : i + 1 = size (rcons tk hd).
      + by rewrite size_rcons size_take // hi.
      rewrite drop_size_cat // take_size_cat // size_rcons -cats1 has_cat /=.
      smt (size_ge0).
    auto => /> &2;split.
    + move=> ?;exists 0;rewrite drop0 take0 /=.
      smt (size_eq0 size_ge0).
    smt (size_eq0 size_ge0).
  qed.

  local lemma bound_i :     
    choare[I0.invert: true ==> true] 
    time [3 + 2 * k1 + 2 * k2; 
          I0.A0.a1 : 1; 
          I0.A0.a2 : 1; 
          H.o : k1 + k2;
          H.init : 1].
  proof.
  proc.
  seq 5 : (size I.qs <= k1 + k2) [k1 + k2].
  call (_: true ;
    (I(A, H).QRO.o : size I.qs - k1)
    time
    (I(A, H).QRO.o : [fun _ => 1; H.o : fun _ => 1]))
  => * /=.

  (* The invariant is preserved by calls to the oracle QRO. *)
  proc; call (_: true; time); wp; skip => * /=; first by smt.

  rnd. 
  call (_: true;
    (I(A, H).QRO.o : size I.qs)
    time
    (I(A, H).QRO.o : [fun _ => 1; H.o : fun _ => 1]))
  => * /=.

  (* The invariant is preserved by calls to the oracle QRO. *)
  proc; call (_: true; time); wp; skip => * => /=; [1: by smt].

  call (_: true; time); wp; skip; move => /=.

  split; move => * /=; first by smt.
  
  (* We have enough time *)
  split; rewrite !big_constz !count_predT !size_range.  
    by smt (k1p k2p).
    by smt (k1p k2p).

  (* finally, we bound the list lookup time. *)
  wp : (size I.qs <= k1 + k2) => //; skip => */=.  
  admit.
qed.

module A = { 
  proc g (x, y) : int = {
    var r : int;
    r <- x + y;
    r <- r * x;
    return r * r;
  }

  proc f (x : int) : int = {
    var a : int;
    a <- x + 1;
    a <@ g(a,x);
  return a;
  }
}.

lemma foo : choare[A.g : true ==> true] time [3].
proof.
proc.
wp; skip => *; split => //.
admit.
qed.

lemma foo3 : choare[A.f : true ==> true] time [4].
proof.
proc.
call foo.
(* Alternatively, we can do: *)
(* call (_: true ==> true time [1]). *)
(* apply foo. *)
wp; skip => *; split =>//.
admit.
qed.

module B = { 
  proc f (x, y) : int = {
    var r : int;
    if (y < x) {
      r <- 1 + 1;
      r <- 1 + 1;
     } else {
      r <- 2 + 1;
      r <- 2 + 1;
    }
    return r;
  }
}.

(* For if statements, we add the cost of both branches. *)
lemma foo4 : choare[B.f : true ==> true] time [5].
proof.
proc.
wp; skip => *; split => //.
admit.
qed.

module C = { 
  var g : int

  proc f (x, y) : int = {
    while (x < y) {
      x <- x + 1;
    }
    return x;
  }
}.

lemma foo5 : forall (a : int) (b : int), 
0 <= a /\ 0 <= b =>
choare[C.f : x = a /\ y = b /\ x < y ==> true] time [2 * (a - b) + 1].
proof.
move => a b p => /=.
proc.
(* - invariant, 
   - increasing quantity starting from zero
   - number of loop iterations
   - cost of one loop body. *)
while (x <= y /\ y = b) (x - a) (b - a) [fun _ => 1] => *.

(* prove that the loop body preserves the invariant, and cost what was stated. *)
wp; skip => * /=.
split; [1: by smt].
admit.

(* prove that the invariant and loop condition implies that we have not reached 
  the maximal number of steps.  *)
by smt.

(* We prove that the invariant implies the post, and that the cost of all
  iterations is smaller than the final cost. *)
skip => * => //; split; [1: by smt].
rewrite !big_constz !count_predT !size_range. 
print list_ind.
admit.
qed.
