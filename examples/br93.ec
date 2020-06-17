(* -------------------------------------------------------------------- *)
require import AllCore List FSet SmtMap.
require import Distr DBool.
require (*--*) BitWord OW ROM PKE_CPA CHoareTactic.
(*---*) import StdBigop.Bigint BIA.
(* ---------------- Sane Default Behaviours --------------------------- *)
pragma -oldip.
pragma +implicits.

(* -------------------------------------------------------------------- *)
(* We start by proving Bellare and Rogaway's algorithm IND-CPA secure   *)
(* on abstract datatypes with minimal structure. We then instantiate to *)
(* semi-concrete fixed-length bitstrings (with abstract lengths).       *)
(* -------------------------------------------------------------------- *)
abstract theory BR93.
(* -------------------------------------------------------------------- *)
(* Let us consider the following abstract scenario construction. Given: *)
(* -------------------------------------------------------------------- *)

(* A set `ptxt` of plaintexts, equipped with an nilpotent addition (+^) *)
type ptxt.

op (+^): ptxt -> ptxt -> ptxt.
axiom addA p1 p2 p3: (p1 +^ p2) +^ p3 = p1 +^ (p2 +^ p3).
axiom addC p1 p2: p1 +^ p2 = p2 +^ p1.
axiom addKp p1 p2: (p1 +^ p1) +^ p2 = p2.

lemma addpK p1 p2: p1 +^ p2 +^ p2 = p1.
proof. by rewrite addC -addA addC -addA addKp. qed.

(*                    and a lossless, full, uniform distribution dptxt; *)
op dptxt: { ptxt distr |    is_lossless dptxt
                         /\ is_full dptxt
                         /\ is_uniform dptxt } as dptxt_llfuuni.
lemma dptxt_ll: is_lossless dptxt by exact/(andWl _ dptxt_llfuuni).
lemma dptxt_uni: is_uniform dptxt by have [#]:= dptxt_llfuuni.
lemma dptxt_fu: is_full dptxt by have [#]:= dptxt_llfuuni.
lemma dptxt_funi: is_funiform dptxt
by exact/(is_full_funiform dptxt_fu dptxt_uni).
hint exact random : dptxt_ll dptxt_fu dptxt_funi.

(* Complexity of sampling in dptxt *)
op cdptxt : int.
schema cost_dptxt `{P} : cost [P: dptxt] = cdptxt.
hint simplify cost_dptxt.

(* A set `rand` of nonces, equipped with                                *)
(*                              a lossless, uniform distribution drand; *)
type rand.
op drand: { rand distr |    is_lossless drand
                         /\ is_uniform drand } as drand_lluni.
lemma drand_ll: is_lossless drand by exact/(andWl _ drand_lluni).
lemma drand_uni: is_uniform drand by exact/(andWr _ drand_lluni).
hint exact random : drand_ll drand_uni.

(* Complexity of testing equality on rand *)
op ceqrand : int.
schema cost_eqrand `{P} {r1 r2:rand} : cost[P: r1 = r2] = cost[P:r1] + cost[P:r2] + ceqrand.
hint simplify cost_eqrand.

schema cost_witness_rand `{P} : cost [P: witness<:rand>] = 0. 
hint simplify cost_witness_rand.


(* A set `ctxt` of ciphertexts defined as                               *)
(*                          the cartesian product of `rand` and `ptxt`; *)
type ctxt = rand * ptxt.

(* A set `pkey * skey` of keypairs, equipped with                       *)
(*                        a lossless, full, uniform distribution dkeys; *)
type pkey, skey.
op dkeys: { (pkey * skey) distr |    is_lossless dkeys
                                  /\ is_funiform dkeys } as dkeys_llfuni.
lemma dkeys_ll: is_lossless dkeys by exact/(andWl _ dkeys_llfuni).
lemma dkeys_funi: is_funiform dkeys by exact/(andWr _ dkeys_llfuni).

(* A family `f` of trapdoor permutations over `rand`,                   *)
(*       indexed by `pkey`, with inverse family `fi` indexed by `skey`; *)
op f : pkey -> rand -> rand.
op fi: skey -> rand -> rand.
axiom fK pk sk x: (pk,sk) \in dkeys => fi sk (f pk x) = x.

lemma fI pk x y: (exists sk, (pk,sk) \in dkeys) =>
  f pk x = f pk y => x = y.
proof. by move=> [sk] + fx_eq_fy - /fK ^ /(_ x) <- /(_ y) <-; congr. qed.

(* Complexity of f *)
op cf : int.
schema cost_f `{P} {pk:pkey, r:rand} : cost [P: f pk r] = cost[P:pk] + cost[P:r] + cf.
hint simplify cost_f.

(* A random oracle from `rand` to `ptxt`, modelling a hash function H;  *)
(* (we simply instantiate the generic theory of Random Oracles with     *)
(*    the types and output distribution declared above, discharging all *)
(*          assumptions on the instantiated parameters--there are none) *)
clone import ROM.Lazy as H with
  type from  <- rand,
  type to    <- ptxt,
  op dsample <- fun _ => dptxt
proof *.

clone import FMapCost as FMC with
  type from  <- rand.

module type HASH = {
  proc init(): unit
  proc hash(x:rand): ptxt
}.

(* Specializing and merging the hash function *)

module Hash = {
  var qs : rand list
  proc init(): unit = { RO.init(); qs <- []; }
  proc o(x:rand): ptxt = { var y; qs <- x::qs; y <@ RO.o(x); return y; }
  proc hash = RO.o
}.

(* We can define the Bellare-Rogaway 93 PKE Scheme.                     *)
(* BR93 is a module that, given access to an oracle H from type         *)
(*   `from` to type `rand` (see `print Oracle.`), implements procedures *)
(*   `keygen`, `enc` and `dec` as follows described below.              *)
module BR93 (H:HASH) = {
  (* `keygen` simply samples a key pair in `dkeys` *)
  proc kg() = {
    var kp;

    kp <$ dkeys;
    H.init();
    return kp;
  }

  (* `enc` samples a random string `r` in `drand` and uses it to       *)
  (*   produce a random mask `h` using the hash function, then returns *)
  (*      the image of `r` by permutation `f` and the plaintext masked *)
  (*                                                         with `h`. *)
  proc enc(pk, m) = {
    var r, h;

    r <$ drand;
    h <@ H.hash(r);
    return (f pk r,h +^ m);
  }

  (* `dec` parses its input as a nonce `r` and a masked plaintext `m` *)
  (*  before recovering the original random string from `r` using the *)
  (*      inverse permutation `fi` and computing its image `h` by the *)
  (*  random oracle. The original plaintext is recovered by unmasking *)
  (*                                                    `m` with `h`. *)
  proc dec(sk, c) = {
    var r, h, m;

    (r,m) <- c;
    r     <- fi sk r;
    h     <- H.hash(r);
    return h +^ m;
  }
}.

(* We instanciate the CPA game with the corresponding type *)
clone import PKE_CPA as PKE with
  type pkey <- pkey,
  type skey <- skey,
  type ptxt <- ptxt,
  type ctxt <- ctxt.

(* We can quickly prove it correct as a sanity check.                 *)
module Correctness = {
  proc main(m) = {
    var pk, sk, c, m';

    (pk,sk) <@ BR93(Hash).kg();
    c       <@ BR93(Hash).enc(pk,m);
    m'      <@ BR93(Hash).dec(sk,c);
    return (m = m');
  }
}.

lemma BR93_correct &m m: Pr[Correctness.main(m) @ &m: res] = 1%r.
proof.
byphoare=> //; conseq (: _ ==> true) (: _ ==> res)=> //.
+ proc; inline *.
  rcondf 19.
  + auto=> /> [pk sk] kp_in_dkeys r _ y _ /=.
    rewrite fK //; split=> [_ _ _|-> //].
    by rewrite mem_set.
  auto=> /> &hr [pk sk] kp_in_dkeys r _ y _ /=.
  rewrite fK //; split=> [_ y' _|].
  + by rewrite get_set_sameE -addA addKp.
  + by rewrite mem_empty.
by proc; inline *; auto=> />; rewrite dkeys_ll drand_ll dptxt_ll.
qed.

(* However, what we are really interested in is proving that it is      *)
(* IND-CPA secure if `f` is a one-way trapdoor permutation.             *)

(* We use cloning to get definitions for OWTP security                  *)
clone import OW as OW_rand with
  type D           <- rand,
  type R           <- rand,
  type pkey        <- pkey,
  type skey        <- skey,
  op   dkeys       <- dkeys,
  op   challenge _ <- drand,
  op   f           <- f,
  op   finv        <- fi
proof dkeys_ll, finvof, challenge_ll, challenge_uni.
realize dkeys_ll by exact/dkeys_ll.
realize challenge_ll by move=> _ _; exact/drand_ll.
realize challenge_uni by move=> _ _; exact/drand_uni.
realize finvof by move=> pk sk x /fK ->.

module type Adv (ARO: ARO)  = {
  proc choose(p:pkey): (ptxt * ptxt)
  proc guess(c:ctxt): bool
}.

(* We want to prove the following:                                      *)
(*   forall (valid) CPA adversary A which makes at most q queries to H, *)
(*     there exists a OW adversary I such that                          *)
(*          `|Pr[CPA(BR, A): res] - 1/2| <= Pr[OW_f(I): res]             *)
(* We construct I as follows, using A.a1 and A.a2 as black boxes        *)
module I(A:Adv): Inverter = {
  proc invert(pk:pkey,y:rand): rand = {
    var m0, m1, h, b, x;

               Hash.init();
    (m0,m1) <@ A(Hash).choose(pk);
    h       <$ dptxt;
    b       <@ A(Hash).guess(y,h);
    x       <- nth witness Hash.qs (find (fun p => f pk p = y) Hash.qs);

    return x;
  }
}.

(* We now prove the result using a sequence of games                    *)
section.
(* All lemmas in this section hold for all (valid) CPA adversary A      *)
declare module A : Adv { -Hash }.

axiom A_guess_ll (O <: ARO {-A}): islossless O.o => islossless A(O).guess.

(* Step 1: replace RO call with random sampling                         *)
local module Game1 = {
  var r: rand

  proc main() = {
    var pk, sk, m0, m1, b, h, c, b';
                Hash.init();
    (pk,sk)  <$ dkeys;
    (m0,m1)  <@ A(Hash).choose(pk);
    b        <$ {0,1};

    r        <$ drand;
    h        <$ dptxt;
    c        <- ((f pk r),h +^ (b?m1:m0));

    b'       <@ A(Hash).guess(c);
    return b' = b;
  }
}.

local lemma pr_Game0_Game1 &m:
     Pr[CPA(BR93(Hash), A(Hash)).main() @ &m: res]
  <=   Pr[Game1.main() @ &m: res]
     + Pr[Game1.main() @ &m: Game1.r \in Hash.qs].
proof.
byequiv=> //; proc.
inline BR93(Hash).enc BR93(Hash).kg.
(* Until the replaced RO call, the two games are in sync.               *)
(*        In addition, the log's contents coincide with the RO queries. *)
call (_: Game1.r \in Hash.qs,
         (forall x, x \in Hash.qs{2} = x \in RO.m{2}) /\
         eq_except (pred1 Game1.r{2}) RO.m{1} RO.m{2}).
+ by apply A_guess_ll.
+ by proc; inline *; auto => /> &1 &2 hb; smt (eq_except_set_eq get_setE).
+ by move=> *; islossless.
+ by move=> /=; proc; call (_: true); 1: islossless; auto => />.
inline Hash.hash; auto => /=.
call (_: ={glob Hash} /\ (forall x, x \in Hash.qs{2} = x \in RO.m{2})).
+ by proc; inline *;auto => />; smt (get_setE).
by inline *;auto => />; smt (mem_empty eq_except_setl get_setE).
qed.

(* Step 2: replace h ^ m with h in the challenge encryption            *)
local module Game2 = {
  var r: rand

  proc main() = {
    var pk, sk, m0, m1, b, h, c, b';
                Hash.init();
    (pk,sk)  <$ dkeys;
    (m0,m1)  <@ A(Hash).choose(pk);
    r        <$ drand;
    h        <$ dptxt;
    c        <- ((f pk r),h);
    b'       <@ A(Hash).guess(c);
    b        <$ {0,1};
    return b' = b;
  }
}.

local equiv eq_Game1_Game2: Game1.main ~ Game2.main:
  ={glob A} ==> ={glob Hash, res} /\ Game1.r{1} = Game2.r{2}.
proof.
proc. swap{2} -4.
call (: ={glob Hash}); 1: by sim.
wp; rnd (fun x=> x +^ (b?m1:m0){2}).
auto; call (: ={glob Hash}); 1: by sim.
inline *; auto=> /> _ _ rR b _ rL _; split=> [|_].
+ by move=> hR _; rewrite addpK.
by move=> hL _; rewrite addpK.
qed.

local lemma pr_Game1_Game2 &m:
  Pr[Game1.main() @ &m: res] = Pr[Game2.main() @ &m: res].
proof. by byequiv eq_Game1_Game2. qed.

local lemma pr_bad_Game1_Game2 &m:
    Pr[Game1.main() @ &m: Game1.r \in Hash.qs]
  = Pr[Game2.main() @ &m: Game2.r \in Hash.qs].
proof. by byequiv eq_Game1_Game2. qed.

local lemma pr_Game2 &m: Pr[Game2.main() @ &m: res] <= 1%r / 2%r.
proof.
byphoare=> //=; proc.
by rnd (pred1 b'); conseq (: true) => // /> *; rewrite dbool1E.
qed.

(* Step 3: The reduction step -- if A queries the RO with the randomness *)
(*     used to encrypt the challenge, then I(A) inverts the OW challenge *)

local lemma pr_Game2_OW &m:
  Pr[Game2.main() @ &m: Game2.r \in Hash.qs]
  <= Pr[OW(I(A)).main() @ &m: res].
proof.
byequiv => //=; proc; inline *.
swap{1} 5 -1.
rnd{1}; wp.
call (_: ={glob Hash}); 1: by sim.
auto.
call (_: ={glob Hash}); 1: by sim.
auto => /> -[pk sk] hkeys r _ h _ qs _ _ hin.
pose P := fun p => f _ p = _.
apply/(fI pk); 1: by exists sk.
have <- // := (nth_find witness P qs _).
by rewrite hasP; exists r.
qed.

lemma Reduction &m:
  Pr[CPA(BR93(Hash), A(Hash)).main() @ &m : res] - 1%r/2%r
  <= Pr[OW(I(A)).main() @ &m: res].
proof.
smt(pr_Game0_Game1 pr_Game1_Game2 pr_bad_Game1_Game2 pr_Game2 pr_Game2_OW).
qed.

end section.

type adv_cost = {
  cchoose : int; (* cost *)
  ochoose : int; (* number of call to o *)
  cguess  : int; (* cost *)
  oguess  : int; (* number of call to o *)
}.

module Ifind(A:Adv) = {
  proc invert(pk:pkey,y:rand): rand = {
    var m0, m1, h, b, r, x;

               Hash.init();
    (m0,m1) <@ A(Hash).choose(pk);
    h       <$ dptxt;
    b       <@ A(Hash).guess(y,h);
    x <- witness; 
    while (Hash.qs <> []){
      r <- head witness Hash.qs; 
      if (f pk r = y) {
        x <- r; Hash.qs <- [];
      } else {
        Hash.qs <- drop 1 Hash.qs;
      }
    }
    return x;
  }
}.

lemma ex_Reduction (cA:adv_cost) (A<:Adv [choose : `{cA.`cchoose, #ARO.o : cA.`ochoose},
                                          guess  : `{cA.`cguess,  #ARO.o : cA.`oguess}] {-Hash}) &m:
  (0 <= cA.`cchoose /\ 0 <= cA.`ochoose /\ 0 <= cA.`cguess /\ 0 <= cA.`oguess) =>
  (forall (O <: ARO{-A}), islossless O.o => islossless A(O).guess) =>
  let qH = cA.`ochoose + cA.`oguess in
  let cB = 
    4 + (4 + cf + ceqrand) * (cA.`ochoose + cA.`oguess) + cdptxt + 
    (3 + cdptxt + cget qH + cset qH + cin qH) * (cA.`ochoose + cA.`oguess) +
    cA.`cguess + cA.`cchoose in
  exists (B <: Inverter [invert : `{cB} ]),
    Pr[CPA(BR93(Hash), A(Hash)).main() @ &m : res] - 1%r/2%r <= Pr[OW(B).main() @ &m: res].  
proof.
  move=> cA_pos A_choose_ll qH.
  exists (Ifind(A)); split.  
  (* Proof of the complexity *)
  + proc.
    seq 5 : (size Hash.qs <= cA.`ochoose + cA.`oguess) time [(4 + cf + ceqrand) * (cA.`ochoose + cA.`oguess) + 2].
    + wp.
      call (_: bounded RO.m (size Hash.qs);
           (Hash.o : size Hash.qs- cA.`ochoose) 
           time
           [(Hash.o : [fun _ => 3 + cdptxt + cget qH + cset qH + cin qH])]).
      + move=> zo hzo; proc; inline *.
        wp : (bounded RO.m qH).
        by auto => &hr />; rewrite dptxt_ll /=; smt (cset_pos bounded_set).
      auto; call (_: bounded RO.m (size Hash.qs);
           (Hash.o : size Hash.qs)
           time [(Hash.o : [fun _ => 3 + cdptxt + cget qH + cset qH + cin qH])]).
      + move=> zo hzo; proc; inline *.
        wp : (bounded RO.m qH).
        by auto => &hr />; rewrite dptxt_ll /=; smt(cset_pos bounded_set).
      inline *; auto => />; split => *.
      + smt (bounded_empty dptxt_ll size_ge0 size_eq0).
      rewrite !bigi_constz /= /#.
    while (true) (size Hash.qs) (cA.`ochoose + cA.`oguess) time [fun _ => 2 + cf + ceqrand].
    + move => z /=; auto => &hr H /=; smt (size_ge0).
    + move => &hr; smt (size_ge0 size_eq0). 
    by auto => /> &hr; rewrite bigi_constz /#.
  (* Proof of the bound *)
  have := Reduction A A_choose_ll &m.
  have -> //: Pr[OW(I(A)).main() @ &m : res] = Pr[OW(Ifind(A)).main() @ &m : res].
  + byequiv => //; proc; inline *; wp.
  while{2}  
   (if Hash.qs{2} = [] then 
       x0{2} = nth witness Hash.qs{1} (find (fun r => f pk0{2} r = y{2}) Hash.qs{1})
    else 
     exists i, x0{2} = witness /\ 0 <= i < size Hash.qs{1} /\ Hash.qs{2} = drop i Hash.qs{1} /\ 
               !has (fun r => f pk0{2} r = y{2}) (take i Hash.qs{1}))
   (size Hash.qs{2}).  
  + move=> &1 z; auto => &2 />.
    case: (Hash.qs{2}) => //= hd qs0 [i />] h0i hi hdr hhas.
    have heq : Hash.qs{1} = take i Hash.qs{1} ++ hd :: qs0.
    + by rewrite hdr cat_take_drop.
    rewrite heq; move: hhas; (pose tk := take i Hash.qs{1}) => hhas.
    have heq1 : 
     nth witness (tk ++ hd :: qs0) (find (fun (p0 : rand) => f pk0{2} p0 = y{2}) (tk ++ hd :: qs0)) =
     nth witness (hd :: qs0) (find (fun (p0 : rand) => f pk0{2} p0 = y{2}) (hd :: qs0)).
    + by rewrite find_cat hhas /= nth_cat; smt (find_ge0).
    split. 
    + move=> heq2;rewrite heq2 heq1 /= heq2 /=; smt (size_ge0).  
    rewrite heq1 drop0 => hy; split;2:smt().
    split.
    + by move=> />;rewrite hy.
    move=> hqs; exists (i + 1).
    rewrite size_cat /= -cat_rcons.
    have -> : i + 1 = size (rcons tk hd).
    + by rewrite size_rcons size_take // hi.
    rewrite drop_size_cat // take_size_cat // size_rcons -cats1 has_cat /=.
    smt (size_ge0).
  wp.
  conseq (: ={Hash.qs, pk0, x, y}).
  + move=> /> *; split; last by smt (size_eq0 size_ge0).
    by move=> *; exists 0; rewrite drop0 take0 /=; smt (size_eq0 size_ge0).
  by sim.
qed.

end BR93.

