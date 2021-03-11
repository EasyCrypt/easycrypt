require import AllCore List Distr DBool SmtMap.
(*   *) import StdOrder RField RealOrder StdBigop Bigreal.

(* This module represent what we have in mind for quantum oracle *)
(*
abstract theory Quantum_full.
  type c. (* classical input *)
  type q. (* quantum input   *)
  type u. (* quantum output  *)

  module type ClassicT = {
    proc init () : unit
    quantum proc get (_:c) : q -> u
  }.

  module Foo : ClassicT = {
    proc init () = { }
    quantum proc get (x:c) = {
       ...
       return (e: q -> u)   
    }     
  }

  quantum module type Adv(O:ClassicT) = {
     
  }

  module F = { 
     cu <@ Foo.get(c,cq);  (* Warning inline *)
  } 

  Declare module A : Adv.

type quantum_state.
qstate : quantum_state

qstate in glob A.

glob A -> glob A U qstate

={glob A, qstate} 

A B
declare quantum module B : ... {-A}

case : on test classic : fail if glob A avec A quantum

and 




q



  
    

  module type QuantumT = {
    proc qget (c:c, q:q) : u  
  }.

  module type QuantumT_i = {
    proc init () : unit 
    include QuantumT 
  }.

  module Quantum(O:ClassicT) = {
    include O [init]
    proc qget(c:c, q:q) = {
      var f;
      f <@ O.get(c);
      return (if f = None then witness else (oget f) q);   
      (* q_ *- U (if f = None then witness else (oget f) q) *)
    }
  }.

end Quantum_full.

(* Same a Quantum_full but with no classical input *)
abstract theory Quantum. 
  type q. (* quantum input   *)
  type u. (* quantum output  *)

  module type ClassicT = {
    proc init () : unit
    proc get () : (q -> u) option
  }.

  module type QuantumT = {
    proc qget (q:q) : u  
  }.

  module type QuantumT_i = {
    proc init () : unit 
    include QuantumT 
  }.

  module Quantum(O:ClassicT) = {
    include O [init]
    proc qget(q:q) = {
      var f;
      f <@ O.get();
      return (if f = None then witness else (oget f) q);
    }
  }.

  module type RoT = {
    proc init () : unit
    proc get () : (q -> u)
  }.

  (* We limit the number of queries *)
  abstract theory Restr.

  op max_queries : int.

  module RQuantum(O:RoT) : ClassicT = {
    var c : int
    proc init () = { c <- 0; O.init(); }
    proc get() = {
      var f, r;
      r <- None;
      if (c < max_queries) { f <@ O.get(); r <- Some f; c <- c + 1;}
      return r;
    }
  }.

  end Restr.

  abstract theory QRom.

  clone import MUniFinFun as MUF with
    type t <- q.  (* This assume that the type of q is finite *)

  op [lossless uniform full] du : u distr.

  op dfu : (q -> u) distr = dfun (fun _ => du).

  lemma dfu_ll: is_lossless dfu.
  proof. apply dfun_ll => ?;apply du_ll. qed.

  lemma dfu_uni: is_uniform dfu.
  proof. apply dfun_uni => ?; apply du_uni. qed.

  lemma dfu_fu: is_full dfu.
  proof. apply dfun_fu => ?; apply du_fu. qed.

  hint solve 0 random : dfu_ll dfu_uni dfu_fu.

  module RoI = {
    proc init () : 

    




end QRom.
*)




(* --------------------------------------------------------------------------- *)

type msg.
type sign.

type pkey.
type skey.

module type Sign = {
  proc kg() : pkey * skey
  proc sign(sk:skey, m:msg) : sign
  proc verify(pk:pkey, m:msg, s:sign) : bool
}.

module type OrclSign = {
  proc sign (m:msg) : sign
}.

module type OrclSign_f = {
  proc init() : pkey
  proc sign (m:msg)  : sign
}.

module type AdvEF (O:OrclSign) = {
  proc main(pk:pkey) : msg * sign
}.

op qs : { int | 0 <= qs } as ge0_qs.
op qh : { int | 0 <= qh } as ge0_qh.

module Log(O:OrclSign) : OrclSign = {
  var log : msg list

  proc sign(m:msg) = {
    var s;
    s <- witness;
    if (size log < qs) { 
      s   <@ O.sign(m);
      log <- m :: log;
    } 
    return s;
  }

}.

module EF(A:AdvEF) (O:Sign) = {
  var pk : pkey
  var sk : skey
  module Os = {
    proc sign(m:msg) = {
      var s;
      s   <@ O.sign(sk, m);
      return s;
    }
  }
  proc main() = {
    var m, s, b;
    (pk, sk) <@ O.kg();
    Log.log <- [];
    (m,s) <@ A(Log(Os)).main(pk);
    b <@ O.verify(pk, m, s);
    return b /\ !m \in Log.log;
  }
}.

type hash.

op f : pkey -> sign -> hash.
op finv: skey -> hash -> sign.
op kg : (pkey * skey) distr.

axiom finv_f ks s : ks \in kg => finv ks.`2 (f ks.`1 s) = s.
axiom f_finv ks h : ks \in kg => f ks.`1 (finv ks.`2 h) = h.

op [lossless uniform full] dhash : hash distr.
op [lossless uniform full] dsign : sign distr.

axiom dhash_dsign : mu1 dhash witness = mu1 dsign witness.
 
module type AdvOW = {
  proc main(pk:pkey, y:hash) : sign
}.

module OW(A:AdvOW) = {
  proc main() = {
    var pk, sk, y, x;
    (pk, sk) <$ kg;
    y <$ dhash;
    x <@ A.main(pk, y);
    return (finv sk y) = x;
  }
}.

(* --------------------------------------------------------------------------*)
(* We define the random distribution over functions *)
clone import MUniFinFun as MUFF with
  type t <- msg.   (* This assume that the type of msg is finite *)

op dfhash : (msg -> hash) distr = dfun (fun _ => dhash).

lemma dfhash_ll: is_lossless dfhash.
proof. apply dfun_ll => ?;apply dhash_ll. qed.

lemma dfhash_uni: is_uniform dfhash.
proof. apply dfun_uni => ?; apply dhash_uni. qed.

lemma dfhash_fu: is_full dfhash.
proof. apply dfun_fu => ?; apply dhash_fu. qed.

hint solve 0 random : dfhash_ll dfhash_uni dfhash_fu.

op dfsign : (msg -> sign) distr = dfun (fun _ => dsign).

lemma dfsign_ll: is_lossless dfsign.
proof. apply dfun_ll => ?;apply dsign_ll. qed.

lemma dfsign_uni: is_uniform dfsign.
proof. apply dfun_uni => ?; apply dsign_uni. qed.

lemma dfsign_fu: is_full dfsign.
proof. apply dfun_fu => ?; apply dsign_fu. qed.

hint solve 0 random : dfsign_ll dfsign_uni dfsign_fu.

lemma dfsign_dfhash (hs: msg -> sign) (hh:msg -> hash) : mu1 dfsign hs = mu1 dfhash hh.
proof.
  rewrite !dfun1E;apply BRM.eq_big => //= x _.
  rewrite (is_full_funiform _ dsign_fu dsign_uni _ witness).
  by rewrite (is_full_funiform _ dhash_fu dhash_uni _ witness) dhash_dsign.
qed.

(* --------------------------------------------------------------------------- *)
module type Hash = {
  proc h (m:msg) : hash 
}.

module type Hash_i = {
  proc init() : unit
  proc h (m:msg) : hash 
}.

module Hash : Hash_i = {
  var  h : msg -> hash

  proc init() = { h <$ dfhash; }

  proc h (m:msg) = {
    return h m;
  }
}.

module FDH (H:Hash_i) = {
  proc kg () = {
    var k;
    H.init();
    k <$ kg;
    return k;
  }

  proc sign(sk:skey, m:msg) = {
    var h;
    h <@ H.h(m);
    return finv sk h;
  }

  proc verify(pk:pkey, m:msg, s:sign) = {
    var h;
    h <@ H.h(m);
    return h = f pk s;
  }
}.

module type AdvEFH (H:Hash) (O:OrclSign) = {
  proc main(pk:pkey) : msg * sign
}.

module RH (H:Hash) = {
  var c : int
  proc h (m:msg) = {
    var r;
    r <- witness;
    if (c < qh) { r <@ H.h(m); c <- c + 1; }
    return r;
  }
}.

module RA (A:AdvEFH) (H:Hash) (O:OrclSign) = {
  proc main(pk:pkey) = {
    var r;
    RH.c <- 0;
    r <@ A(RH(H),O).main(pk);
    return r;
  }
}.
  
clone import MUniFinFunBiased as DBB with 
  type t <- msg,
  op MUniFinFun.FinT.enum <-  MUFF.FinT.enum
  proof *.
realize MUniFinFun.FinT.enum_spec by apply MUFF.FinT.enum_spec.

op p : real.
axiom p_bound : 0%r <= p <= 1%r.

op dfbool = dbfun p.

lemma pr_dfbool_l m (l:msg list) q : 
  !m \in l => size l <= q =>  
  p*(1%r-p)^q <= mu dfbool (fun t => t m /\ forall m', m' \in l => !t m').
proof.
  move=> hm hl.
  apply (ler_trans (p ^ 1 * (1%r - p) ^ size l)).
  rewrite RField.expr1; apply ler_wpmul2l; 1: by case: p_bound.
  apply ler_wiexpn2l; [1:smt (p_bound)| 2: smt(size_ge0)].
  apply (ler_trans _ _ _ (dbfunE_mem_le p [m] l p_bound _)); 1: smt().
  by apply mu_le => /#.
qed.

theory RNDIF.

op q : int.

type result.

module type AdvRNDIF (H:Hash) = {
  proc main() : result
}.
    
module RndIf (A:AdvRNDIF) = {
  var hf : msg -> hash
  var bf : msg -> bool
  var c  : int

  module H = {
    proc h (m:msg) = {
      var r;
      r <- witness;
      if (c < q) {
        r <- hf m;
        c <- c + 1;
      }
      return r;
    }
  }

  proc main1(dfh : (msg -> hash) distr) = {
    var b, y;
    c  <- 0;
    bf <$ dfbool;
    hf <$ dfh;
    y  <$ dhash; 
    b  <@ A(H).main();
    return (b,bf);
  }

  proc main2(dfh : (msg -> hash) distr) = {
    var b, y;
    c  <- 0;
    bf <$ dfbool;
    hf <$ dfh;
    y  <$ dhash; 
    hf <- fun m => if bf m then y else hf m;
    b  <@ A(H).main();
    return (b, bf);
  }
}.

(* Remark the event depend of result return by the adversary but also
   of the function bf indicating if the hf return y or a random value.
   It would be interesting to known if we can add y in the event
 *)

type event = result * (msg -> bool) -> bool.  

op factor = 8%r/3%r * q%r^4 * p^2.

axiom advantage (A<:AdvRNDIF{RndIf}) &m dfh0 (P:event):
  is_lossless dfh0 =>
  is_uniform dfh0  => 
  is_full    dfh0  =>
  `| Pr[RndIf(A).main1(dfh0) @ &m : P res] - Pr[RndIf(A).main2(dfh0) @ &m: P res] | 
   <= 8%r/3%r * q%r^4 * p^2.

end RNDIF.

module B(A:AdvEFH) = {
  import var EF
  var hs : msg -> sign
  
  module Os = {
    proc sign(m:msg) = { return hs m; }
  }

  proc main(pk:pkey, y:hash) : sign = {
    var m,s, t;
    t <$ dfbool;
    hs <$ dfsign;
    Hash.h <- fun m => if t m then y else f pk (hs m);
    Log.log <- [];
    (m,s) <@ RA(A, Hash, Log(Os)).main(pk);
    return s;
  }
}.

section.

declare module A : AdvEFH { RH, EF, Log, Hash, B}.
axiom A_ll (H <: Hash{A}) (O <: OrclSign{A}) : 
 islossless O.sign => islossless H.h => islossless A(H, O).main.

local module G1 = {
  import var EF
  var t : msg -> bool
  var m : msg
  var s : sign

  module Os = {
    proc sign(m:msg) = {
      var hm;
      hm   <@ Hash.h(m);
      return finv sk hm;
    }
  }

  proc main() = {
    var b, hm;
    Hash.init();
    (pk, sk) <$ kg;
    Log.log <- [];
    (m,s) <@ RA(A, Hash, Log(Os)).main(pk);
    hm <@ Hash.h(m);
    b <- hm = f pk s;
    return b /\ !m \in Log.log;
  }

  proc main'() = {
    var b;
    t <$ dfbool;  (* x -> true p  false 1 -p *)  
    b <@ main();
    return b /\ (t m /\ forall m', m' \in Log.log => !t m');
  }
}.

local lemma l1 &m : 
   Pr[ EF(RA(A,Hash), FDH(Hash)).main() @ &m : res] =
   Pr[ G1.main() @ &m : res].
proof. 
  byequiv (: ={glob A} ==> ={res})=> //.
  proc. inline *; sim.
  call (: ={Hash.h, Log.log, EF.pk, EF.sk, RH.c}).
  + by proc;inline *; sim.
  + by sim.
  by auto.
qed.

local lemma l2 &m :
  Pr[ G1.main'() @ &m : res] >= p*(1%r-p)^qs * Pr [G1.main() @ &m : res].
byphoare (:(glob A){m} = glob A ==> _) => //.
proc.
swap 1 1.
seq 1 : b Pr[G1.main() @ &m : res] (p * (1%r - p) ^ qs) _ 0%r (b => !G1.m \in Log.log /\ size Log.log <= qs).
+ inline G1.main; wp.
  conseq (:size Log.log <= qs) => />.
  call (:true); 1:done.
  inline RA(A, Hash, Log(G1.Os)).main; wp.
  call (: size Log.log <= qs).
  + proc; sp; if => //.
    wp; call(:true); 1: done; skip => /> /#.
  + by conseq />.
  inline *; auto => /> *; apply ge0_qs.
+ call (: (glob A){m} = glob A ==> res); 2: by auto.
  bypr => &m0 ?.
  byequiv (: ={glob A} ==> ={res}) => //; 1: sim.
+ rnd (fun t => t G1.m /\ forall (m' : msg), m' \in Log.log => ! t m').
  skip => />; smt (pr_dfbool_l).
+ by auto.
smt().
qed.

local module ARI (H:Hash) = {
  import var EF
  import var G1

  module Os = {
    proc sign(m:msg) = {
      var hm;
      hm   <@ H.h(m);
      return finv sk hm;
    }
  }

  proc main() = {
    var b, hm;
    (pk, sk) <$ kg;
    Log.log <- [];
    (m,s) <@ RA(A, H, Log(Os)).main(pk);
    hm <@ H.h(m);
    b <- hm = f pk s;
    return (b, Log.log, m);
  }
}.

(* !m \in Log.log /\ (t m /\ forall m', m' \in Log.log => !t m'); *)
local clone import RNDIF as RNDIF0 with
  op q = qs + qh + 1,
  type result <- bool * msg list * msg. 

local equiv hE z : Hash.h ~ RndIf(ARI).H.h : 
   ={arg} /\ Hash.h{1} = RndIf.hf{2} /\ RndIf.c{2} = z /\ z < q ==>
   ={res} /\ RndIf.c{2} = z + 1.
proof. by proc; auto => /> /#. qed.

op P (r:(bool * msg list * msg) * (msg -> bool)) = 
  let (b, log, m, t) = (r.`1.`1, r.`1.`2, r.`1.`3, r.`2) in
  b /\ !m \in log /\ (t m /\ forall m', m' \in log => !t m').

local lemma l3 &m : 
  Pr[ G1.main'() @ &m : res] = Pr[RndIf(ARI).main1(dfhash) @ &m : P res].
proof.
  byequiv => //.
  proc.
  inline G1.main ARI(RndIf(ARI).H).main; wp.
  ecall (hE (size Log.log + RH.c){1}).
  inline *; wp.
  call (: Hash.h{1} = RndIf.hf{2} /\ ={Log.log, RH.c, EF.pk, EF.sk} /\
          RndIf.c{2} = (size Log.log + RH.c){1} /\
          size Log.log{1} <= qs /\ RH.c{1} <= qh).
  + proc; sp; if => //.
    inline G1.Os.sign ARI(RndIf(ARI).H).Os.sign.
    by wp; ecall (hE (RndIf.c{2})); auto => /> /#.
  + proc; sp; if => //.
    by wp; ecall (hE (RndIf.c{2})); auto => /> /#.
  by swap{2} 2 -1; auto; rnd{2}; auto => />; smt (ge0_qh ge0_qs).
qed. 

local lemma l4 &m : 
  `| Pr[RndIf(ARI).main1(dfhash) @ &m : P res] - Pr[RndIf(ARI).main2(dfhash) @ &m : P res] | <= 
   factor.
proof.
  apply (advantage ARI &m dfhash).
  + by apply dfhash_ll. + by apply dfhash_uni. + by apply dfhash_fu.
qed.

local module G2 = {
  import var EF G1
  
  var h : hash
  var hs : msg -> sign

  module Os = {
    proc sign(m:msg) = { return hs m; }
  }

  proc main () = {
    (pk, sk) <$ kg;
    h <$ dhash;
    t <$ dfbool;
    hs <$ dfsign;
    Hash.h <- fun m => if t m then h else f pk (hs m);
    Log.log <- [];
    (m,s) <@ RA(A, Hash, Log(Os)).main(pk);
    return finv sk h = s /\ !m \in Log.log /\ (t m /\ forall m', m' \in Log.log => !t m');
  }
}.

local lemma l5 &m : 
  Pr[RndIf(ARI).main2(dfhash) @ &m : P res] = 
  Pr[G2.main() @ &m : res].
proof.
  byequiv (: ={glob A} /\ dfh{1} = dfhash ==> P res{1} = res{2}) => //.
  proc; inline *; wp.
  (* Proof using upto bad *)
  call (: (exists m', m' \in Log.log /\ G1.t m'), 
          (={EF.pk, EF.sk, Log.log, RH.c} /\
          RndIf.bf{1} = G1.t{2} /\
          RndIf.c{1} = (size Log.log + RH.c){2} /\
          size Log.log{1} <= qs /\ RH.c{1} <= qh /\
          Hash.h{2} = RndIf.hf{1} /\ 
          (forall m', !G1.t m' => Hash.h m' = f EF.pk (G2.hs m')){2} /\
          (EF.pk,EF.sk){2} \in kg),
          (exists m', m' \in Log.log /\ RndIf.bf m'){1} =
          (exists m', m' \in Log.log /\ G1.t m'){2}
          ).
  + exact A_ll. 
  + by proc; sp; if => //; inline *;auto => />;smt(finv_f). 
  + by move=> *; proc; inline *; auto => /> /#.
  + by move=> *; proc; inline *; auto => /> /#.
  + by proc; sp; if => //; inline *; auto => /> /#.
  + by move=> *; proc; inline *; auto => /> /#.
  + by move=> *; proc; inline *; auto => /> /#.
  swap{1} 6 - 5; swap{1} 2 3; swap{1} 4 -2; wp.
  rnd (fun (h:msg -> hash) => fun m => finv EF.sk{1} (h m))
      (fun (h:msg -> sign) => fun m => f EF.pk{1} (h m)).
  rewrite /P; auto => |> k hk h _ bf _; split.
  + move=> *; apply fun_ext => ?; smt(finv_f).
  smt(dfsign_dfhash f_finv finv_f ge0_qs ge0_qh).
qed.

local lemma l6 &m : 
  Pr[G2.main() @ &m : res] <= Pr[OW(B(A)).main() @ &m : res].
proof.
  byequiv => //.
  proc; inline *; wp.
  conseq (: ={r} /\ G2.h{1} = y{2} /\ EF.sk{1} = sk{2}) => />.
  by sim (: ={Log.log, RH.c, Hash.h} /\ G2.hs{1} = B.hs{2}).
qed.

lemma conclusion &m : 
   p * (1%r - p) ^ qs * Pr[EF(RA(A, Hash), FDH(Hash)).main() @ &m : res] <=
   Pr[OW(B(A)).main() @ &m : res] + 8%r / 3%r * q%r ^ 4 * p ^ 2. 
proof.
  move: (l1 &m) (l2 &m) (l3 &m) (l4 &m) (l5 &m) (l6 &m) => /#.
qed.

end section.

(* Proof for claw free permutation *)

op f2   : pkey -> sign -> hash.
op f2inv: skey -> hash -> sign.
axiom f2inv_f2 ks s : ks \in kg => f2inv ks.`2 (f2 ks.`1 s) = s.
axiom f2_f2inv ks h : ks \in kg => f2 ks.`1 (f2inv ks.`2 h) = h.

module type AdvClawFree = {
  proc main (pk:pkey) : sign * sign
}.

module ClawFree(A:AdvClawFree) = {
  proc main () = {
    var pk, sk, s1, s2;
    (pk, sk) <$ kg;
    (s1, s2) <@ A.main(pk);
    return f pk s1 = f2 pk s2;
  }
}.

module BCF (A:AdvEFH) = { 

  var hs : msg -> sign

  module Os = {
    proc sign(m:msg) = { return hs m; }
  }

  proc main(pk:pkey) = {
    var t, m, s;
    t <$ dfbool;
    hs <$ dfsign;
    Hash.h <- (fun m => if t m then f2 pk (hs m) else f pk (hs m)); 
    Log.log <- [];
    (m,s) <@ RA(A, Hash, Log(Os)).main(pk);
    return (s, hs m); 
  }

}.

section.

declare module A : AdvEFH { RH, EF, Log, Hash, BCF}.
axiom A_ll (H <: Hash{A}) (O <: OrclSign{A}) : 
 islossless O.sign => islossless H.h => islossless A(H, O).main.

local module G1 = {
  import var EF
  var t : msg -> bool
  var m : msg
  var s : sign

  module Os = {
    proc sign(m:msg) = {
      var hm;
      hm   <@ Hash.h(m);
      return finv sk hm;
    }
  }

 proc main() = {
    var b, hm;
    Hash.init();
    (pk, sk) <$ kg;
    Log.log <- [];
    (m,s) <@ RA(A, Hash, Log(Os)).main(pk);
    hm <@ Hash.h(m);
    b <- hm = f pk s;
    return b /\ !m \in Log.log;
  }

  proc main'() = {
    var b;
    t <$ dfbool;
    b <@ main();
    return b /\ (t m /\ forall m', m' \in Log.log => !t m');
  }
}.

local lemma l1 &m : 
   Pr[ EF(RA(A,Hash), FDH(Hash)).main() @ &m : res] =
   Pr[ G1.main() @ &m : res].
proof. 
  byequiv => //.
  proc; inline *; sim.
  call (: ={Hash.h, Log.log, EF.pk, EF.sk, RH.c}).
  + by proc;inline *; sim.
  + by sim.
  by auto.
qed.

local lemma l2 &m :
  Pr[ G1.main'() @ &m : res] >= p*(1%r-p)^qs * Pr [G1.main() @ &m : res].
byphoare (:(glob A){m} = glob A ==> _) => //.
proc.
swap 1 1.
seq 1 : b Pr[G1.main() @ &m : res] (p * (1%r - p) ^ qs) _ 0%r (b => !G1.m \in Log.log /\ size Log.log <= qs).
+ inline G1.main; wp.
  conseq (:size Log.log <= qs) => />.
  call (:true); 1:done.
  inline RA(A, Hash, Log(G1.Os)).main; wp.
  call (: size Log.log <= qs).
  + proc; sp; if => //.
    wp; call(:true); 1: done; skip => /> /#.
  + by conseq />.
  inline *; auto => /> *; apply ge0_qs.
+ call (: (glob A){m} = glob A ==> res); 2: by auto.
  bypr => &m0 ?.
  byequiv (: ={glob A} ==> ={res}) => //; 1: sim.
+ rnd (fun t => t G1.m /\ forall (m' : msg), m' \in Log.log => ! t m').
  skip => />; smt (pr_dfbool_l).
+ by auto.
smt().
qed.

local module G2 = {
  import var EF
  import var G1

  var hs : msg -> sign

  module Os = {
    proc sign(m:msg) = { return hs m; }
  }

  proc main() = {
    var b, hm;
    (pk, sk) <$ kg;
    t <$ dfbool;
    hs <$ dfsign;
    Hash.h <- (fun m => if t m then f2 pk (hs m) else f pk (hs m)); 
    Log.log <- [];
    (m,s) <@ RA(A, Hash, Log(Os)).main(pk);
    hm <@ Hash.h(m);
    b <- hm = f pk s;
    return b /\ !m \in Log.log /\ (t m /\ forall m', m' \in Log.log => !t m');
  }

}.

local lemma l3 &m : 
  Pr [G1.main'() @ &m : res] = Pr [G2.main() @ &m : res].
proof.
  byequiv => //;proc.
  inline *; wp.
  call (: (exists m', m' \in Log.log /\ G1.t m'), 
          (={G1.t, EF.pk, EF.sk, Log.log, RH.c, Hash.h} /\
          Hash.h{2} = (fun m => if G1.t m then f2 EF.pk (G2.hs m) else f EF.pk (G2.hs m)){2} /\ 
          (EF.pk,EF.sk){2} \in kg),
          (exists m', m' \in Log.log /\ G1.t m'){1} = (exists m', m' \in Log.log /\ G1.t m'){2}).
  + by apply A_ll.
  + proc; inline *; auto => />; smt (finv_f).
  + by move=> *; proc; inline *; auto => /> /#.
  + by move=> *; proc; inline *;auto => /> /#.
  + by proc; inline *; auto.
  + by move=> *; proc; inline *; auto => /> /#.
  + by move=> *; proc; inline *; auto.
  swap{1} 3 -2; wp.
  rnd (fun h  => fun m => if G1.t m then f2inv EF.sk (h m) else finv EF.sk (h m)){2}
      (fun hs => fun m => if G1.t m then f2 EF.pk (hs m) else f EF.pk (hs m)){2}.
  auto => /> {&m}.
  move => k hk t _; split.
  + move=> hs _; apply fun_ext; smt (f2inv_f2 finv_f).
  smt (dfsign_dfhash f2_f2inv f_finv).
qed.

local lemma l4 &m : 
  Pr [G2.main() @ &m : res] <= Pr [ClawFree(BCF(A)).main() @ &m : res].
proof.
  byequiv => //.
  proc; inline *;wp.
  call (: ={Log.log, RH.c, Hash.h} /\ G2.hs{1} = BCF.hs{2} /\
          Hash.h{2} = (fun m => if G1.t m then f2 EF.pk (G2.hs m) else f EF.pk (G2.hs m)){1}).
  + by sim />.
  + by sim />.
  auto => /> * /#.
qed.




(*
proc Q (x) = { 
  r <- witness;
  if (c < q) {
    c <- c + 1;
    r <- f' x;

  }
  return r;
}.


proc Qb () = { 
  var b;
  b <- (c < q);
  if b then c <- c + 1;
  return b;
}

proc Q (Qb, f') (|x,y>) = {
  var b;
  b <- Qb ();
  |x,y> -> |x, y + (if b then f' x else witness)>;
  return r;
}

qproc Q () = {

  var b;
  b <- (c < q);
  if b then c <- c + 1;
  return b;
}, e (* :T->U *)

module type OT = {
  qproc Q (_: T) : U 
}

module O : OT = {
   var f : T -> U;
   proc init () = {
     f <$ sample (T -> U);
   }

   qproc Q, f () = {
     var b;
     b <- (c < q);
     if b then c <- c + 1;
     return b;
   }

 
   
 


A_C,(Qb : unit -> bool, f' : T -> U)

*)




end section.




