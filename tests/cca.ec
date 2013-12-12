module type I = { 
  proc f() : unit
  proc init () : unit 
}.

module type IF (X:I) = { 
  proc init() : unit { X.init }
}.

module F(X:I) : IF(X), I = { 
   proc f() : unit = { X.f(); }
   proc init() : unit = { X.init();}
}.

module type Adv = {
  proc a (x:int) : int {} 
}.

module Test (A:Adv) = { 
  proc main(x:int) : int = { 
    var r : int;
    r  = A.a(x);
    return r;
  }
}.

module A : Adv = {
  proc a (x:int) : int = { return x; }
}.

module M = Test(A).

lemma foo : 
  forall (A<:Adv {Test}), 
    equiv [ Test(A).main ~ Test(A).main : 
         x{1} = x{2} /\ (glob A){1} = (glob A){2} ==> 
         res{1} = res{2} /\  (glob A){1} = (glob A){2} ].
proof -strict.
 intros A.
 proc.
 call (x{1} = x{2} /\ (glob A){1} = (glob A){2}) 
      (res{1} = res{2} /\  (glob A){1} = (glob A){2}).
 proc true;try (simplify;split).
 skip;simplify. (* Il y a un bug : les variables sont des fois avec les
                   arguments des foncteurs d'autres fois non *)
 smt.
qed.

module type IO = { 
  proc h (x:int) : int {}
}.

module type Adv' (O:IO) = { 
  proc a (x:int) : int { O.h } (* check that the oracle are disjoint *)
}.

module G (B:Adv') = {

  module O : IO = { 
    proc h (x:int) : int = {
      return x;
    }
  }

  module A1 = B(O) 

  proc main (x:int) : int = { 
    var r : int;
    r  = A1.a(x); 
    return r; 
  } 
}.

(* module F1 (B:Adv') = { 
  module A1 = B(G.O)
}.
*)

lemma foo' : 
  forall (A<:Adv' {G}), 
    equiv [ G(A).main ~ G(A).main : 
         x{1} = x{2} /\ (glob A){1} = (glob A){2} ==> 
         res{1} = res{2} /\  (glob A){1} = (glob A){2} ].
proof -strict.
intros A. 
 proc.
 call (x{1} = x{2} /\ (glob A){1} = (glob A){2} /\ true) 
      (res{1} = res{2} /\ (glob A){1} = (glob A){2} /\ true).
 proc true;try smt.
 proc.
 skip;smt.
 skip;smt.
qed.

module A' (O:IO) : Adv'(O) = { 
  proc a (x:int) : int = {
    var r : int;
    r  = O.h(x);
    return r;
  }
}.

lemma foo1 :
   equiv [ G(A').main ~ G(A').main : 
           x{1} = x{2} /\ (glob A'){1} = (glob A'){2} ==> 
           res{1} = res{2} /\  (glob A'){1} = (glob A'){2} ].
proof -strict.
 apply (foo' (A')).
qed.


lemma foo2 : forall (x:int) &m1 &m2, 
     Pr[G(A').main(x) @ &m1 : res = 0] = Pr[G(A').main(x) @ &m1 : res = 0].
proof -strict.
 intros xv &m1 &m2.
 equiv_deno (_ : x{1} = x{2} /\ (glob A'){1} = (glob A'){2} ==> 
                 res{1} = res{2} /\  (glob A'){1} = (glob A'){2}).
 apply foo1.
 simplify;smt.
 smt.
qed.

(*






type from.
type to.

module type Ihash = {
  proc init () : unit
  proc hash (x:from) : to 
}.

type skey.
type pkey.
type message.
type cipher.

require import Option.
require import List.
module type Ischeme (H:Ihash) = {
  proc gen()                   : pkey * skey     {H.hash}
  proc enc(pk:pkey, m:message) : cipher          {H.hash}
  proc dec(sk:skey, c:cipher)  : message option  {H.hash} 
}.

module type Icca_oracles = {
  proc hash (x:from)   : to
  proc dec1  (c:cipher) : message option
  proc dec2  (c:cipher) : message option
}.

module type Iadv (O:Icca_oracles) = {
  proc a1 (pk:pkey)  : message * message { O.hash O.dec1 }
  proc a2 (c:cipher) : bool              { O.hash O.dec2 }
}.

module CCA (H:Ihash, S:Ischeme, A:Iadv) = {
  var hlog    : from list
  var dec_log : cipher list
  var pk:pkey
  var sk:skey

  module S = S(H)

  module O = {

    proc hash (x:from) : to = { 
      var r : to;
      r  = H.hash(x);
      hlog = x::hlog;
      return r;
    }

    proc dec1 (c:cipher) : message option = {
      var r : message option;
      r  = S.dec(sk, c);
      return r;
    }

    proc dec2 (c:cipher) : message option = {
      var r : message option;
      dec_log = c::dec_log;
      r  = S.dec(sk,c);
      return r;
    }      
  }

  module A = A(O)

  var cs : cipher

  proc main () : bool = {
    var m0 : message;
    var m1 : message;
    var b  : bool;
    var b' : bool;
    H.init();
    hlog    = []
    dec_log = [];
    (pk,sk)  = S.gen();
    (m1,m0)  = A.a1(pk);
    cs       = S.enc(pk, b ? m1 : m0);
    b'       = A.a2(cs);
    return b = b';
  }
    
}.
*)