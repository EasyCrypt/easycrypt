require import AllCore List Distr DBool SmtMap.

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

op dfhash : (msg -> hash) distr.
op dfsign : (msg -> sign) distr.

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
    
op [lossless] dfbool : (msg -> bool) distr.

op p : real.

axiom pr_dfbool m : mu dfbool (fun t => t m) = p.
axiom pr_dfbool_l m (l:msg list) q: 
  !m \in l => size l <= q =>  
  p*(1%r-p)^q <= mu dfbool (fun t => t m /\ forall m', m' \in l => !t m').

theory RNDIF.

op q : int.

type result.

module type AdvRNDIF (H:Hash) = {
  proc init() : hash {}
  proc main() : result
}.

(*
op d1 : (A -> B) distr.
op d2 : (A -> B) distr.
op eps : real.

axiom forall a (E : B -> bool) : 
  `| mu d1 (fun f => E (f a)) - mu d2 (fun f => E (f a)) | <= eps.

Pr[main1 () : E f res ] - Pr[main2 () : E res ] <= q^3 * eps.
*)
    
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
    var b, h;
    c  <- 0;
    bf <$ dfbool;
    hf <$ dfh;
    h  <@ A(H).init();
    b  <@ A(H).main();
    return (b,bf);
  }

  proc main2(dfh : (msg -> hash) distr) = {
    var b, h;
    c  <- 0;
    bf <$ dfbool;
    hf <$ dfh;
    h  <@ A(H).init(); 
    hf <- fun m => if bf m then h else hf m;
    b  <@ A(H).main();
    return (b, bf);
  }
}.

op factor : real.

axiom advantage (A<:AdvRNDIF{RndIf}) &m dfh0 P:
  is_uniform dfh0 => 
  is_full    dfh0 =>
  `| Pr[RndIf(A).main1(dfh0) @ &m : P res] - Pr[RndIf(A).main2(dfh0) @ &m: P res] | <= factor.

end RNDIF.

clone import RNDIF as RNDIF0 with
  op q = qs + qh + 1,
  type result <- bool * msg list * msg. 

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

declare module A : AdvEFH { RH, EF, Log, Hash, RndIf, B}.
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

  proc init () = {
    var h;
    h <$ dhash;
    return h;
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
  inline G1.main ARI(RndIf(ARI).H).init ARI(RndIf(ARI).H).main; wp.
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
  + admit. (* is_uniform dfhash *)
  admit.   (* is_full dfhash *)
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
  swap{1} 7 - 6; swap{1} 2 3; swap{1} 4 -2; wp.
  rnd (fun (h:msg -> hash) => fun m => finv EF.sk{1} (h m))
      (fun (h:msg -> sign) => fun m => f EF.pk{1} (h m)).
  rewrite /P; auto => |> k hk h _ bf _; split.
  + move=> *; apply fun_ext => ?; smt(finv_f).
  move=> _; split.
  + admit. (* the distribution are uniform *)
  move=> _ hf ?; split.
  + admit. (* the distribution is full *)
  smt(f_finv finv_f ge0_qs ge0_qh).
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
   Pr[OW(B(A)).main() @ &m : res] + factor. 
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
  move=> _; split.
  + admit. (* uniform on the same space *)
  move=> _ h _; split.
  + admit. (* the distribution is full *)
  smt (f2_f2inv f_finv).
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

qproc Q, e:T->U () = {

  var b;
  b <- (c < q);
  if b then c <- c + 1;
  return b;

}

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




