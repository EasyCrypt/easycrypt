(* -------------------------------------------------------------------- *)
require import AllCore List FSet SmtMap.
require import Distr DBool CHoareTactic.
require (*--*) BitWord OW ROM PKE_CPA.
(*---*) import StdBigop.Bigint BIA.
(* ---------------- Sane Default Behaviours --------------------------- *)
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
schema cost_dptxt `{P} : cost [P: dptxt] = N cdptxt.
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
schema cost_eqrand `{P} {r1 r2:rand} : cost[P: r1 = r2] = cost[P:r1] + cost[P:r2] + N ceqrand.
hint simplify cost_eqrand.

schema cost_witness_rand `{P} : cost [P: witness<:rand>] = '0. 
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
schema cost_f `{P} {pk:pkey, r:rand} : cost [P: f pk r] = cost[P:pk] + cost[P:r] + N cf.
hint simplify cost_f.

(* A random oracle from `rand` to `ptxt`, modelling a hash function H;  *)
(* (we simply instantiate the generic theory of Random Oracles with     *)
(*    the types and output distribution declared above, discharging all *)
(*          assumptions on the instantiated parameters--there are none) *)
<<<<<<< HEAD
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
=======
clone import ROM as H with
  type in_t    <- rand,
  type out_t   <- ptxt,
  type d_in_t  <- unit,
  type d_out_t <- bool,
  op   dout _  <- dptxt.
import H.Lazy.
>>>>>>> origin/1.0-preview

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

<<<<<<< HEAD
    (pk,sk) <@ BR93(Hash).kg();
    c       <@ BR93(Hash).enc(pk,m);
    m'      <@ BR93(Hash).dec(sk,c);
=======
    (pk,sk) <@ BR93(LRO).keygen();
    c       <@ BR93(LRO).enc(pk,m);
    m'      <@ BR93(LRO).dec(sk,c);
>>>>>>> origin/1.0-preview
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
<<<<<<< HEAD
  + by rewrite mem_empty.
=======
  rewrite domE; case: (LRO.m{hr}.[r])=> [|p] //= _ _.
  by rewrite -addA addKp.
>>>>>>> origin/1.0-preview
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

<<<<<<< HEAD
module type Adv (ARO: ARO)  = {
  proc choose(p:pkey): (ptxt * ptxt)
  proc guess(c:ctxt): bool
=======
(* But we can't do it (yet) for IND-CPA because of the random oracle    *)
(*             Instead, we define CPA for BR93 with that particular RO. *)
module type Adv (ARO: POracle)  = {
  proc a1(p:pkey): (ptxt * ptxt)
  proc a2(c:ctxt): bool
}.

(* We need to log the random oracle queries made to the adversary       *)
(*                               in order to express the final theorem. *)
module Log (H:Oracle) = {
  var qs: rand list

  proc init() = {
    qs <- [];
          H.init();
  }

  proc o(x) = {
    var r;

    qs <- x::qs;
    r  <@ H.o(x);
    return r;
  }
}.

module BR93_CPA(A:Adv) = {
  proc main(): bool = {
    var pk, sk, m0, m1, c, b, b';

                Log(LRO).init();
    (pk,sk)  <@ BR93(LRO).keygen();
    (m0,m1)  <@ A(Log(LRO)).a1(pk);
    b        <$ {0,1};
    c        <@ BR93(LRO).enc(pk,b?m0:m1);
    b'       <@ A(Log(LRO)).a2(c);
    return b' = b;
  }
>>>>>>> origin/1.0-preview
}.

(* We want to prove the following:                                      *)
(*   forall (valid) CPA adversary A which makes at most q queries to H, *)
(*     there exists a OW adversary I such that                          *)
(*          `|Pr[CPA(BR, A): res] - 1/2| <= Pr[OW_f(I): res]             *)
(* We construct I as follows, using A.a1 and A.a2 as black boxes        *)
module I(A:Adv): Inverter = {
  proc invert(pk:pkey,y:rand): rand = {
    var m0, m1, h, b, x;

<<<<<<< HEAD
               Hash.init();
    (m0,m1) <@ A(Hash).choose(pk);
    h       <$ dptxt;
    b       <@ A(Hash).guess(y,h);
    x       <- nth witness Hash.qs (find (fun p => f pk p = y) Hash.qs);
=======
               Log(LRO).init();
    (m0,m1) <@ A(Log(LRO)).a1(pk);
    h       <$ dptxt;
    b       <@ A(Log(LRO)).a2(y,h);
    x       <- nth witness Log.qs (find (fun p => f pk p = y) Log.qs);
>>>>>>> origin/1.0-preview

    return x;
  }
}.

(* We now prove the result using a sequence of games                    *)
section.
(* All lemmas in this section hold for all (valid) CPA adversary A      *)
<<<<<<< HEAD
declare module A : Adv { -Hash }.

axiom A_guess_ll (O <: ARO {-A}): islossless O.o => islossless A(O).guess.
=======
declare module A : Adv { LRO, Log }.

axiom A_a1_ll (O <: POracle {A}): islossless O.o => islossless A(O).a1.
axiom A_a2_ll (O <: POracle {A}): islossless O.o => islossless A(O).a2.
>>>>>>> origin/1.0-preview

(* Step 1: replace RO call with random sampling                         *)
local module Game1 = {
  var r: rand

  proc main() = {
    var pk, sk, m0, m1, b, h, c, b';
<<<<<<< HEAD
                Hash.init();
    (pk,sk)  <$ dkeys;
    (m0,m1)  <@ A(Hash).choose(pk);
=======
                Log(LRO).init();
    (pk,sk)  <$ dkeys;
    (m0,m1)  <@ A(Log(LRO)).a1(pk);
>>>>>>> origin/1.0-preview
    b        <$ {0,1};

    r        <$ drand;
    h        <$ dptxt;
    c        <- ((f pk r),h +^ (b?m1:m0));

<<<<<<< HEAD
    b'       <@ A(Hash).guess(c);
=======
    b'       <@ A(Log(LRO)).a2(c);
>>>>>>> origin/1.0-preview
    return b' = b;
  }
}.

local lemma pr_Game0_Game1 &m:
     Pr[CPA(BR93(Hash), A(Hash)).main() @ &m: res]
  <=   Pr[Game1.main() @ &m: res]
     + Pr[Game1.main() @ &m: Game1.r \in Hash.qs].
proof.
byequiv=> //; proc.
<<<<<<< HEAD
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
=======
inline BR93(LRO).enc BR93(LRO).keygen.
(* Until the replaced RO call, the two games are in sync.               *)
(*        In addition, the log's contents coincide with the RO queries. *)
seq  8  5: (   ={glob A, glob LRO, glob Log, pk, sk, b}
            /\ pk0{1} = pk{2}
            /\ m{1} = (b?m0:m1){2}
            /\ r{1} = Game1.r{2}
            /\ (forall x, x \in Log.qs{1} <=> x \in LRO.m{1})).
+ auto; call (:   ={glob Log, glob LRO}
               /\ (forall x, x \in Log.qs{1} <=> x \in LRO.m{1})).
  + proc; inline LRO.o.
    by auto=> /> &2 log_is_dom y _; smt(@SmtMap).
  by inline *; auto=> /> _ _ x; rewrite mem_empty.
(* We now deal with everything that happens after the programs differ: *)
(*   - until r gets queried to the random oracle by the adversary      *)
(*     (and if it wasn't already queried by a1), we guarantee that the *)
(*     random oracles agree except on r                                *)
(*   - if the adversary queries r to the random oracle (or if it has   *)
(*     already done so in a1), we give up                              *)
(* Because we reason up to bad, we need to prove that bad is stable    *)
(* and that the adversary and its oracles are lossless                 *)
call (_: Game1.r \in Log.qs,
         eq_except (pred1 Game1.r{2}) LRO.m{1} LRO.m{2}).
+ exact/A_a2_ll.
+ proc; inline LRO.o.
  auto=> /> &1 &2 _ m1_eqe_m2 yL y_in_dptxt; split.
  + move=> x_notin_m; split.
    + by rewrite !get_set_sameE eq_except_set_eq.
    move: m1_eqe_m2 x_notin_m=> + + + r_neq_x.
    by rewrite eq_exceptP pred1E !domE=> /(_ x{2} r_neq_x) ->.
  move=> x_in_m; split.
  + move: m1_eqe_m2 x_in_m=> + + + r_neq_x.
    by rewrite eq_exceptP pred1E !domE=> /(_ x{2} r_neq_x) ->.
  by move: m1_eqe_m2=> + _ r_neq_x- /eq_exceptP /(_ x{2}); rewrite pred1E=> /(_ r_neq_x) ->.
+ by move=> &2 _; proc; call (LRO_o_ll _); auto=> /=; apply: dptxt_ll.
+ move=> _ /=; proc; inline *.
  conseq (: true ==> true: =1%r) (: Game1.r \in Log.qs ==> Game1.r \in Log.qs)=> //=.
  + by auto=> />.
  by auto=> />; exact/dptxt_ll.
inline LRO.o; case: ((r \in LRO.m){1}).
+ conseq (: _ ==> ={b} /\ Game1.r{2} \in Log.qs{2})=> //=.
  + by move=> /> &1 &2 _ _ rR _ _ _ _ _ h /h [] -> //.
  by auto=> /> &2 <- ->.
rcondt{1} 3; 1:by auto.
auto=> /> &2 log_is_dom r_notin_m y _; rewrite !get_set_sameE oget_some /=.
split.
+ by move=> _; rewrite eq_exceptP /pred1=> x; rewrite get_setE eq_sym=> ->.
by move=> _ rR aL mL aR qsR mR h /h [] ->.
>>>>>>> origin/1.0-preview
qed.

(* Step 2: replace h ^ m with h in the challenge encryption            *)
local module Game2 = {
  var r: rand

  proc main() = {
    var pk, sk, m0, m1, b, h, c, b';
<<<<<<< HEAD
                Hash.init();
    (pk,sk)  <$ dkeys;
    (m0,m1)  <@ A(Hash).choose(pk);
    r        <$ drand;
    h        <$ dptxt;
    c        <- ((f pk r),h);
    b'       <@ A(Hash).guess(c);
    b        <$ {0,1};
=======
                Log(LRO).init();
    (pk,sk)  <$ dkeys;
    (m0,m1)  <@ A(Log(LRO)).a1(pk);
    b        <$ {0,1};

    r        <$ drand;
    h        <$ dptxt;
    c        <- ((f pk r),h);

    b'       <@ A(Log(LRO)).a2(c);
>>>>>>> origin/1.0-preview
    return b' = b;
  }
}.

local equiv eq_Game1_Game2: Game1.main ~ Game2.main:
  ={glob A} ==> ={glob Hash, res} /\ Game1.r{1} = Game2.r{2}.
proof.
<<<<<<< HEAD
proc. swap{2} -4.
call (: ={glob Hash}); 1: by sim.
wp; rnd (fun x=> x +^ (b?m1:m0){2}).
auto; call (: ={glob Hash}); 1: by sim.
=======
proc.
call (: ={glob Log, glob LRO}); 1: by sim.
wp; rnd (fun x=> x +^ (b?m0:m1){2}).
auto; call (: ={glob Log, glob LRO}); 1: by sim.
>>>>>>> origin/1.0-preview
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
<<<<<<< HEAD
by rnd (pred1 b'); conseq (: true) => // /> *; rewrite dbool1E.
=======
swap 4 4.
wp; rnd (pred1 b')=> //=.
inline *; call (_: true).
+ exact A_a2_ll. (* adversary *)
+ by proc; call (LRO_o_ll _); auto=> /=; apply: dptxt_ll. (* oracle *)
auto; call (_: true).
+ exact A_a1_ll. (* adversary *)
+ by proc; call (LRO_o_ll _); auto=> /=; apply: dptxt_ll. (* oracle *)
auto=> />; rewrite dkeys_ll drand_ll dptxt_ll /predT /=.
by move=> _ _ _ _ _ _ r; rewrite dbool1E pred1E.
>>>>>>> origin/1.0-preview
qed.

(* Step 3: The reduction step -- if A queries the RO with the randomness *)
(*     used to encrypt the challenge, then I(A) inverts the OW challenge *)

local lemma pr_Game2_OW &m:
  Pr[Game2.main() @ &m: Game2.r \in Hash.qs]
  <= Pr[OW(I(A)).main() @ &m: res].
proof.
<<<<<<< HEAD
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
=======
rewrite (OW_OWr &m (I(A))). (* Note: we proved it forall (abstract) I    *)
byequiv => //=; proc; inline *; wp.
conseq
  (_ : _ ==>
       support dkeys (pk0{2}, sk{2}) /\
       Game2.r{1} = OWr.x{2} /\ Log.qs{1} = Log.qs{2} /\
       y{2} = f pk0{2} Game2.r{1}).
+ move=> /> qs x pk sk vk x_in_qs; pose P := fun p => f _ p = _.
  have h := nth_find witness P qs _.
  + by rewrite hasP; exists x.
  apply/(fI pk).
  + by exists sk.
  by rewrite h.
(* rest of proof *)
call (: ={glob Log, glob LRO}); 1: by sim.
swap{1} 6 -2.
auto; call (: ={glob Log, glob LRO}); 1: by sim.
by auto=> /> [pk sk] ->.
>>>>>>> origin/1.0-preview
qed.

lemma Reduction &m:
  Pr[CPA(BR93(Hash), A(Hash)).main() @ &m : res] - 1%r/2%r
  <= Pr[OW(I(A)).main() @ &m: res].
proof.
smt(pr_Game0_Game1 pr_Game1_Game2 pr_bad_Game1_Game2 pr_Game2 pr_Game2_OW).
qed.

<<<<<<< HEAD
end section.
=======
(* A family `f` of trapdoor permutations over `rand`,                   *)
(*        indexed by `pkey`, with inverse family `fi` indexed by `skey` *)
op f : pkey -> rand -> rand.
op fi: skey -> rand -> rand.
axiom fK pk sk x: (pk,sk) \in dkeys => fi sk (f pk x) = x.

(* Random Oracle                                                        *)
clone import ROM as H with
  type in_t    <- rand,
  type out_t   <- ptxt,
  type d_in_t  <- unit,
  type d_out_t <- bool,
  op   dout _  <- dptxt.
import Lazy.

(* A Definition for OWTP Security                                       *)
module type Inverter = {
  proc invert(pk:pkey, x:rand): rand
}.

module Exp_OW (I : Inverter) = {
  proc main(): bool = {
    var pk, sk, x, x';

    (pk,sk) <$ dkeys;
    x       <$ drand;
    x'      <@ I.invert(pk,f pk x);
    return (x = x');
  }
}.

(* A Definition for CPA Security                                        *)
module type Scheme (RO : Oracle) = {
  proc keygen(): (pkey * skey)
  proc enc(pk:pkey, m:ptxt): ctxt
}.

module type Adv (ARO : POracle)  = {
  proc a1(p:pkey): (ptxt * ptxt)
  proc a2(c:ctxt): bool
}.

module CPA (O : Oracle) (S:Scheme) (A:Adv) = {
  proc main(): bool = {
    var pk, sk, m0, m1, c, b, b';

               O.init();
    (pk,sk) <@ S(O).keygen();
    (m0,m1) <@ A(O).a1(pk);
    b       <$ {0,1};
    c       <@ S(O).enc(pk,b?m0:m1);
    b'      <@ A(O).a2(c);
    return b' = b;
  }
}.

(* And a definition for the concrete Bellare-Rogaway Scheme             *)
module (BR : Scheme) (H : Oracle) = {
  proc keygen():(pkey * skey) = {
    var pk, sk;

    (pk,sk) <$ dkeys;
    return (pk,sk);
  }

  proc enc(pk:pkey, m:ptxt): ctxt = {
    var h, r;

    r <$ drand;
    h <@ H.o(r);
    return ((f pk r) || m +^ h);
  }

  proc dec(sk:skey, c:ctxt): ptxt = {
    var r, p, h;
>>>>>>> origin/1.0-preview

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

<<<<<<< HEAD
lemma ex_Reduction (cA:adv_cost) (A<:Adv [choose : `{N cA.`cchoose, #ARO.o : cA.`ochoose},
                                          guess  : `{N cA.`cguess,  #ARO.o : cA.`oguess}] {-Hash}) &m:
  (0 <= cA.`cchoose /\ 0 <= cA.`ochoose /\ 0 <= cA.`cguess /\ 0 <= cA.`oguess) =>
  (forall (O <: ARO{-A}), islossless O.o => islossless A(O).guess) =>
  let qH = cA.`ochoose + cA.`oguess in
  let cB = 
    4 + (4 + cf + ceqrand) * (cA.`ochoose + cA.`oguess) + cdptxt + 
    (3 + cdptxt + cget qH + cset qH + cin qH) * (cA.`ochoose + cA.`oguess) +
    cA.`cguess + cA.`cchoose in
  exists (B <: Inverter [invert : `{N cB} ]),
    Pr[CPA(BR93(Hash), A(Hash)).main() @ &m : res] - 1%r/2%r <= Pr[OW(B).main() @ &m: res].  
proof.
  move=> cA_pos A_choose_ll qH.
  exists (Ifind(A)); split.  
  (* Proof of the complexity *)
  + proc.
    seq 5 : (size Hash.qs <= cA.`ochoose + cA.`oguess) time [N((4 + cf + ceqrand) * (cA.`ochoose + cA.`oguess) + 2)] => //.
    + wp.
      call (_: size Hash.qs- cA.`ochoose <= k /\ bounded RO.m (size Hash.qs);
           time
           [(Hash.o k : [N(3 + cdptxt + cget qH + cset qH + cin qH)])]).
      + move=> zo hzo; proc; inline *.
        wp := (bounded RO.m qH).
        rnd; auto => &hr />; rewrite dptxt_ll /=; smt (cset_pos bounded_set).
      rnd; call (_: size Hash.qs = k /\ bounded RO.m (size Hash.qs);
           time [(Hash.o k : [N(3 + cdptxt + cget qH + cset qH + cin qH)])]).
      + move=> zo hzo; proc; inline *.
        wp := (bounded RO.m qH).
        by rnd;auto => &hr />; rewrite dptxt_ll /=; smt(cset_pos bounded_set).
      inline *; auto => />; split => *.
      + smt (bounded_empty dptxt_ll size_ge0 size_eq0).
      rewrite !bigi_constz /= /#.
    while (true) (size Hash.qs) (cA.`ochoose + cA.`oguess) time [fun _ => N(2 + cf + ceqrand)].
    + move => z /=; auto => &hr H /=; smt (size_ge0).
    + move => &hr; smt (size_ge0 size_eq0). 
    + done.
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
=======
(* We will need to turn a concrete CPA adversary into an abstract one.  *)
(*      We do not need to do it for the inverter as the types coincide. *)
module A_CPA (A : Adv) (H : POracle) = {
  proc a1 = A(H).a1

  proc a2(c:rand * ptxt): bool = {
    var b;

    b <@ A(H).a2(c.`1 || c.`2);
    return b;
  }
}.

section.
declare module A : Adv { LRO, I }.

axiom A_a1_ll (O <: POracle {A}): islossless O.o => islossless A(O).a1.
axiom A_a2_ll (O <: POracle {A}): islossless O.o => islossless A(O).a2.

local clone import BR93 as Instance with
  type pkey  <- pkey,
  type skey  <- skey,
  op   dkeys <- dkeys,
  op   f     <- f,
  op   fi    <- fi,
  type ptxt  <- ptxt,
  op   (+^)  <- Plaintext.(+^),
  op   dptxt <- dptxt,
  type rand  <- rand,
  op   drand <- drand
proof addA, addC, addKp, dptxt_llfuuni, drand_lluni, dkeys_llfuni, fK.
realize addA          by move=> p1 p2 p3; algebra.
realize addC          by move=> p1 p2; algebra.
realize addKp         by move=> p1 p2; algebra.
realize dptxt_llfuuni by smt(@Plaintext.DWord).
realize drand_lluni   by smt(@Randomness.DWord).
realize dkeys_llfuni  by exact/dkeys_llfuni.
realize fK            by exact/fK.

lemma Reduction &m:
     Pr[CPA(LRO, BR, A).main() @ &m : res] - 1%r / 2%r
  <= Pr[Exp_OW(Self.I(A, LRO)).main() @ &m : res].
proof.
have <-:   Pr[BR93_CPA(A_CPA(A)).main() @ &m: res]
         = Pr[CPA(LRO,BR,A).main() @ &m: res].
+ byequiv=> //=; proc.
  inline A_CPA(A,Log(H.Lazy.LRO)).a2.
  wp; call (: H.Lazy.LRO.m{1} = LRO.m{2}).
  + by proc; inline *; auto.
  inline BR93(H.Lazy.LRO).enc BR(LRO).enc H.Lazy.LRO.o LRO.o; auto.
  call (: H.Lazy.LRO.m{1} = LRO.m{2}).
  + by proc; inline *; auto.
  inline *; auto=> /> [pk sk] _ [m0 m1] c b _ r _ h _ /=.
  by rewrite addC /= addC.
have <-:   Pr[OW_rand.OW(I(A_CPA(A))).main() @ &m: res]
         = Pr[Exp_OW(Self.I(A,LRO)).main() @ &m: res].
+ byequiv=> //=; proc.
  inline *; auto; call (: H.Lazy.LRO.m{1} = LRO.m{2} /\ ={qs}(Log,Self.I)).
  + by sim.
  auto; call (: H.Lazy.LRO.m{1} = LRO.m{2} /\ ={qs}(Log,Self.I)).
  + by sim.
  by auto.
apply/(Reduction (A_CPA(A)) _ _ &m).
+ by move=> O O_o_ll; exact/(A_a1_ll O O_o_ll).
by move=> O O_o_ll; proc; call (A_a2_ll O O_o_ll).
>>>>>>> origin/1.0-preview
qed.

end BR93.
