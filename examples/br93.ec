(* -------------------------------------------------------------------- *)
require import AllCore List FSet SmtMap.
require import Distr DBool.
require (*--*) BitWord OW ROM.

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

(* A set `rand` of nonces, equipped with                                *)
(*                              a lossless, uniform distribution drand; *)
type rand.
op drand: { rand distr |    is_lossless drand
                         /\ is_uniform drand } as drand_lluni.
lemma drand_ll: is_lossless drand by exact/(andWl _ drand_lluni).
lemma drand_uni: is_uniform drand by exact/(andWr _ drand_lluni).

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

(* A random oracle from `rand` to `ptxt`, modelling a hash function H;  *)
(* (we simply instantiate the generic theory of Random Oracles with     *)
(*    the types and output distribution declared above, discharging all *)
(*          assumptions on the instantiated parameters--there are none) *)
clone import ROM as H with
  type in_t    <- rand,
  type out_t   <- ptxt,
  type d_in_t  <- unit,
  type d_out_t <- bool,
  op   dout _  <- dptxt.
import H.Lazy.

(* We can define the Bellare-Rogaway 93 PKE Scheme.                     *)
(* BR93 is a module that, given access to an oracle H from type         *)
(*   `from` to type `rand` (see `print Oracle.`), implements procedures *)
(*   `keygen`, `enc` and `dec` as follows described below.              *)
module BR93 (H:Oracle) = {
  (* `keygen` simply samples a key pair in `dkeys` *)
  proc keygen() = {
    var kp;

    kp <$ dkeys;
    return kp;
  }

  (* `enc` samples a random string `r` in `drand` and uses it to       *)
  (*   produce a random mask `h` using the hash function, then returns *)
  (*      the image of `r` by permutation `f` and the plaintext masked *)
  (*                                                         with `h`. *)
  proc enc(pk, m) = {
    var r, h;

    r <$ drand;
    h <@ H.o(r);
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
    h     <- H.o(r);
    return h +^ m;
  }
}.

(* We can quickly prove it correct as a sanity check.                 *)
section Correctness.
local module Correctness = {
  proc main(m) = {
    var pk, sk, c, m';

    (pk,sk) <@ BR93(LRO).keygen();
    c       <@ BR93(LRO).enc(pk,m);
    m'      <@ BR93(LRO).dec(sk,c);
    return (m = m');
  }
}.

local lemma BR93_correct &m m: Pr[Correctness.main(m) @ &m: res] = 1%r.
proof.
byphoare=> //; conseq (: _ ==> true) (: _ ==> res)=> //.
+ proc; inline *.
  rcondf 17.
  + auto=> /> &hr [pk sk] kp_in_dkeys r _ y _ /=.
    rewrite fK //; split=> [_ _ _|-> //].
    by rewrite mem_set.
  auto=> /> &hr [pk sk] kp_in_dkeys r _ y _ /=.
  rewrite fK //; split=> [_ y' _|].
  + by rewrite get_set_sameE -addA addKp.
  rewrite domE; case: (LRO.m{hr}.[r])=> [|p] //= _ _.
  by rewrite -addA addKp.
by proc; inline *; auto=> />; rewrite dkeys_ll drand_ll dptxt_ll.
qed.
end section Correctness.

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
}.

(* We want to prove the following:                                      *)
(*   forall (valid) CPA adversary A which makes at most q queries to H, *)
(*     there exists a OW adversary I such that                          *)
(*          `|Pr[BR_CPA(A): res] - 1/2| <= Pr[OW_f(I): res]             *)
(* We construct I as follows, using A.a1 and A.a2 as black boxes        *)
module I(A:Adv): Inverter = {
  var x:rand

  proc invert(pk:pkey,y:rand): rand = {
    var m0, m1, h, b;

               Log(LRO).init();
    (m0,m1) <@ A(Log(LRO)).a1(pk);
    h       <$ dptxt;
    b       <@ A(Log(LRO)).a2(y,h);
    x       <- nth witness Log.qs (find (fun p => f pk p = y) Log.qs);

    return x;
  }
}.

(* We now prove the result using a sequence of games                    *)
section.
(* All lemmas in this section hold for all (valid) CPA adversary A      *)
declare module A : Adv { LRO, Log }.

axiom A_a1_ll (O <: POracle {A}): islossless O.o => islossless A(O).a1.
axiom A_a2_ll (O <: POracle {A}): islossless O.o => islossless A(O).a2.

(* Step 1: replace RO call with random sampling                         *)
local module Game1 = {
  var r: rand

  proc main() = {
    var pk, sk, m0, m1, b, h, c, b';
                Log(LRO).init();
    (pk,sk)  <$ dkeys;
    (m0,m1)  <@ A(Log(LRO)).a1(pk);
    b        <$ {0,1};

    r        <$ drand;
    h        <$ dptxt;
    c        <- ((f pk r),h +^ (b?m0:m1));

    b'       <@ A(Log(LRO)).a2(c);
    return b' = b;
  }
}.

local lemma pr_Game0_Game1 &m:
     Pr[BR93_CPA(A).main() @ &m: res]
  <=   Pr[Game1.main() @ &m: res]
     + Pr[Game1.main() @ &m: Game1.r \in Log.qs].
proof.
byequiv=> //; proc.
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
+ by move=> &2 _; proc; call (LRO_o_ll dptxt_ll); auto.
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
qed.

(* Step 2: replace h ^ m with h in the challenge encryption            *)
local module Game2 = {
  var r: rand

  proc main() = {
    var pk, sk, m0, m1, b, h, c, b';
                Log(LRO).init();
    (pk,sk)  <$ dkeys;
    (m0,m1)  <@ A(Log(LRO)).a1(pk);
    b        <$ {0,1};

    r        <$ drand;
    h        <$ dptxt;
    c        <- ((f pk r),h);

    b'       <@ A(Log(LRO)).a2(c);
    return b' = b;
  }
}.

local equiv eq_Game1_Game2: Game1.main ~ Game2.main:
  ={glob A} ==> ={glob Log, res} /\ Game1.r{1} = Game2.r{2}.
proof.
proc.
call (: ={glob Log, glob LRO}); 1: by sim.
wp; rnd (fun x=> x +^ (b?m0:m1){2}).
auto; call (: ={glob Log, glob LRO}); 1: by sim.
inline *; auto=> /> _ _ rR b _ rL _; split=> [|_].
+ by move=> hR _; rewrite addpK.
split=> [|_].
+ by move=> hR _; exact/dptxt_funi.
by move=> hL _; rewrite dptxt_fu /= addpK.
qed.

local lemma pr_Game1_Game2 &m:
  Pr[Game1.main() @ &m: res] = Pr[Game2.main() @ &m: res].
proof. by byequiv eq_Game1_Game2. qed.

local lemma pr_bad_Game1_Game2 &m:
    Pr[Game1.main() @ &m: Game1.r \in Log.qs]
  = Pr[Game2.main() @ &m: Game2.r \in Log.qs].
proof. by byequiv eq_Game1_Game2. qed.

local lemma pr_Game2 &m: Pr[Game2.main() @ &m: res] = 1%r / 2%r.
proof.
byphoare=> //=; proc.
swap 4 4.
wp; rnd (pred1 b')=> //=.
inline *; call (_: true).
+ exact A_a2_ll. (* adversary *)
+ by proc; call (LRO_o_ll dptxt_ll); auto. (* oracle *)
auto; call (_: true).
+ exact A_a1_ll. (* adversary *)
+ by proc; call (LRO_o_ll dptxt_ll); auto. (* oracle *)
auto=> />; rewrite dkeys_ll drand_ll dptxt_ll /predT /=.
by move=> _ _ _ _ _ _ r; rewrite dbool1E pred1E.
qed.

(* Step 3: The reduction step -- if A queries the RO with the randomness *)
(*     used to encrypt the challenge, then I(A) inverts the OW challenge *)
(* We need a version of the one-way game where the challenge is a global *)
local module OWr (I : Inverter) = {
  var x : rand

  proc main() : bool = {
    var x', pk, sk;

    (pk,sk) <$ dkeys;
    x       <$ drand;
    x'      <@ I.invert(pk,f pk x);
    return (x = x');
  }
}.

(* We can easily prove that it is strictly equivalent to OW              *)
local lemma OW_OWr &m (I <: Inverter {OWr}):
  Pr[OW(I).main() @ &m: res]
  = Pr[OWr(I).main() @ &m: res].
proof. by byequiv=> //=; sim. qed.

local lemma pr_Game2_OW &m:
  Pr[Game2.main() @ &m: Game2.r \in Log.qs]
  <= Pr[OW(I(A)).main() @ &m: res].
proof.
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
qed.

lemma Reduction &m:
  Pr[BR93_CPA(A).main() @ &m : res] - 1%r/2%r
  <= Pr[OW(I(A)).main() @ &m: res].
proof.
smt(pr_Game0_Game1 pr_Game1_Game2 pr_bad_Game1_Game2 pr_Game2 pr_Game2_OW).
qed.
end section.
end BR93.

(* We now consider a concrete instance:                                 *)
(*   - plaintexts are bitstrings of length k > 0                        *)
(*   - nonces are bitstrings of length l > 0                            *)
(*   - ciphertexts are bitstrings of length n = k + l                   *)

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
by rewrite take_cat drop_cat size_rand take0 drop0 cats0 /= mkrandK mkptxtK.
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

    (r,p) <- parse c;
    r     <- fi sk r;
    h     <@ H.o(r);
    return p +^ h;
  }
}.

(* And our inverter                                                     *)
module I (A:Adv) (H : Oracle) = {
  var qs : rand list

  module QRO = {
    proc o(x:rand) = {
      var r;

      qs <- x::qs;
      r  <@ H.o(x);
      return r;
    }
  }

  proc invert(pk:pkey,y:rand): rand = {
    var x, m0, m1, h, b;

    qs      <- [];
               H.init();
    (m0,m1) <@ A(QRO).a1(pk);
    h       <$ dptxt;
    b       <@ A(QRO).a2(y || h);
    x       <- nth witness qs (find (fun p => f pk p = y) qs);

    return x;
  }
}.

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
qed.
end section.
