require import Distr.
require import Set.
require import Map.
module type O = { 
  fun hashA (x:int) : int 
}.

module type Adv(O:O) = { 
  fun a (h:int) : int 
}.

module RO = {
  var mH : (int,int) map
  
  fun hash (x:int) : int = { 
    var r : int;
    r = $[0..10];
    if (!in_dom x mH) mH.[x] = r;
    return (proj mH.[x]);
  }

  var logA : int set
  
  fun hashA (x:int) : int = { 
    var r : int;
    logA  = add x logA;
    r     = hash(x);
    return r;
  }
}.

module F1(A:Adv) = { 

  module A1 = A(RO)

  var xs : int

  fun main() : int = { 
    var h: int;
    var r : int;
    RO.mH    = Map.empty;
    RO.logA  = Set.empty;
    h        = RO.hash(xs);
    r        = A1.a(h);
    return r;
  }
}.

module F2(A:Adv) = { 
  module A1 = A(RO)

  var xs : int

  fun main() : int = { 
    var h: int;
    var r : int;
    RO.mH    = Map.empty;
    RO.logA  = Set.empty;
    h        = $[0..10];
    r        = A1.a(h);
    return r;
  }
}.

lemma foo : forall (A<:Adv{RO,F1,F2}), 
  (forall (O<:O),  
      bd_hoare [O.hashA : true ==> true] = 1%r => 
      bd_hoare [A(O).a : true ==> true] = 1%r) =>  
  equiv [F1(A).main ~ F2(A).main : 
     (glob A){1} = (glob A){2} /\ F1.xs{1} = F2.xs{2} ==> 
     (!mem F2.xs RO.logA){2} => res{1} = res{2}].
proof.
  intros A Hlossless;fun.
  call ((!mem F2.xs RO.logA){2} /\ h{1} = h{2} /\ (glob A){1} = (glob A){2} /\
         F1.xs{1} = F2.xs{2} /\
         RO.logA{1} = RO.logA{2} /\ eq_except RO.mH{1} RO.mH{2} F2.xs{2})
       ( (!mem F2.xs RO.logA){2} => res{1} = res{2} ).
    fun (mem F2.xs RO.logA)
      (RO.logA{1} = RO.logA{2} /\ F1.xs{1} = F2.xs{2} /\
       eq_except RO.mH{1} RO.mH{2} F2.xs{2}) 
      (F1.xs{1} = F2.xs{2}); try (trivial).
      apply Hlossless.
      fun; inline RO.hash;wp;rnd;wp;skip;simplify;trivial.

    (* Hoare goal *)
    admit.
    admit.
  inline RO.hash;wp;rnd;wp;skip;simplify;trivial.
save.

