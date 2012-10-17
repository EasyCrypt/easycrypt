(*
** MARION
**
** Proof that the advantage of an adversary attacking (in parallel) n
** instances of a signature scheme with independently generated keys
** is bounded by n times that of an adversary attacking one instance
** of the scheme. My understanding is that I cannot formalize this
** "n" parameter, so I chose to start with 2.
*)

(* 
** SANTIAGO
**
** Can you give as some pointers to a proof of this result in the
** literature?
** I believe we can prove the fully general result parametric in n.
** This depends on the reduction that you have in mind, which is stll
** unclear for me (I have one in mind that I think will work).
*)

type message.
type signature.
type skey.
type pkey.

(* 
** MARION
**
** To write the hypothesis that the verification of legitimate
** signatures succeeds, as I couldn't manage to write an "axiom" on
** probabilistic operators, I explicitely formalized the randomness of
** the signature algorithms (keygen, signing, and verification
** algos)
*)

(* 
** SANTIAGO
**
** The verification algorithm is deterministic, so you can encode
** it as a normal operator.
**
** I wrote appropriate specs for KG and Sign. Note that this are
** irrelevant for the proof and may be safely omitted.
*)

pop KG      : () -> pkey * skey.
pop Sign    : (skey, message) -> signature.
op  Verify  : (pkey, message, signature) -> bool.

op key_pair : (pkey * skey) -> bool.
op sig      : (skey, message, signature) -> bool.

spec KG_spec() :
   kp1 = KG() ~ kp2 = KG() : true ==> kp1 = kp1 && key_pair(kp1).

spec Sign_spec(sk:skey, m:message) :
   s1 = Sign(sk, m) ~ s2 = Sign(sk, m) : true ==> s1 = s2 && sig(sk, m, s1).

axiom Verify_spec : 
  forall (pk:pkey, sk:skey, m:message, s:signature), 
    key_pair((pk, sk)) => sig(sk, m, s) => Verify(pk, m, s).

(** Existential Forgery Under Chosen-Message Attack *)

adversary A(pk:pkey) : message * signature 
  { message -> signature }.

(*
** SANTIAGO
**
** In the games that you wrote you did not require the signature output by
** the adversary be fresh...
*)

game EF_CMA = {

(* 
** MARION
**
** These variables are declared here because I tried using them in
** equiv statements and I reckon this requires them to be "visibly"
** declared in the game. This assumption has been made all alonf the
** code. 
*)

(*
** SANTIAGO
**
** Only global variables, formal procedure arguments and the special
** 'res' keyword can appear as variables in relational assertions.
** Only 'res' and global variables can appear in events in probability
** claims.
**
** One can usually work around this limitation, but it would be
** convenient to sometimes allow the use of local variables.
** (This was already in our TODO list.)
**
*)

  var pk : pkey 
  var sk : skey
  var L  : (message * signature) list

  fun S(m:message) : signature = {
    var s : signature = Sign(sk, m);
    L = (m, s) :: L;
    return s;
  }
  
  abs A = A {S}

  fun Main() : bool = {
    var m : message;
    var s : signature;
    (pk, sk) = KG();
    L = [];
    (m, s) = A(pk);
    return (Verify(pk, m, s) && !mem((m,s), L));
  }
}.


(** Existential Forgery Under Chosen-Message Attack and 2 indenpendent keys *)

adversary A2(pk1, pk2:pkey) : bool * message * signature
  { message -> signature; message -> signature }.

game EF_2CMA = {
  var pk1, pk2 : pkey 
  var sk1, sk2 : skey
  var L1, L2   : (message * signature) list
  var b : bool
 
  fun S1(m:message) : signature = {
    var s : signature = Sign(sk1, m);
    L1 = (m, s) :: L1;
    return s;
  }
 
  fun S2(m:message) : signature = {
    var s : signature = Sign(sk2, m);
    L2 = (m, s) :: L2;
    return s;
  }
   
  abs A2 = A2 {S1, S2}

  fun Main() : bool = {
    var m : message;
    var s : signature;
    (pk1, sk1) = KG();
    (pk2, sk2) = KG();
    L1 = [];
    L2 = [];
    (b, m, s) = A2(pk1, pk2);
    return (if b then Verify(pk1,m,s) && !mem((m,s), L1) 
                 else Verify(pk2,m,s) && !mem((m,s), L2));
  }
}.


(*
**
** MARION
**
** Here I declare the intermediate game with the adversary against
** UNF1 simulating the adversary against UNF2.
*)

(** This is an instance of EF_CMA with a concrete adversary B using A2 *)
game Red1 = {
  var pk : pkey 
  var sk : skey
  var L  : (message * signature) list

  fun S(m:message) : signature = {
    var s : signature = Sign(sk, m);
    L = (m, s) :: L;
    return s;
  }
  
  (** BEGIN Adversary *)
  var pk' : pkey
  var sk' : skey
 
  fun S1(m:message) : signature = {
    var s : signature;
    s = S(m);
    return s;
  }

  fun S2(m:message) : signature = {
    var s : signature = Sign(sk', m);
    return s;
  }

  abs A2 = A2 {S1, S2}

  fun B(_pk:pkey) : message * signature = {
    var m : message;
    var s : signature;
    var b : bool;
    (pk', sk') = KG();
    (b, m, s) = A2(_pk, pk');
    return (m, s);
  }
  (** END Adversary *)
 
  fun Main() : bool = {
    var m : message;
    var s : signature;
    (pk, sk) = KG();
    L = [];
    (m, s) = B(pk);
    return (Verify(pk, m, s) && !mem((m,s), L));
  }
}.

prover "alt-ergo".

equiv S1_S1 : EF_2CMA.S1 ~ Red1.S1 :
  ={m} &&
  pk1{1} = pk{2} && sk1{1} = sk{2} && pk2{1} = pk'{2} && sk2{1} = sk'{2} && 
  forall (ms:message * signature), !mem(ms,L1{1}) => !mem(ms,L{2})
  ==>
  ={res} &&
  pk1{1} = pk{2} && sk1{1} = sk{2} && pk2{1} = pk'{2} && sk2{1} = sk'{2} &&
  forall (ms:message * signature), !mem(ms,L1{1}) => !mem(ms,L{2}).
proof.
 inline{2} S; trivial.
save.

equiv EF_2CMA_Red1 : EF_2CMA.Main ~ Red1.Main : true ==> res{1} && b{1} => res{2}.
proof.
 inline B.
 auto
  (pk1{1} = pk{2} && sk1{1} = sk{2} && pk2{1} = pk'{2} && sk2{1} = sk'{2} &&
   forall (ms:message * signature), !mem(ms,L1{1}) => !mem(ms,L{2})).
 derandomize; wp; trivial.
save.


(** This is an instance of EF_CMA with a concrete adversary B using A2 *)
game Red2 = {
  var pk : pkey 
  var sk : skey
  var L  : (message * signature) list

  fun S(m:message) : signature = {
    var s : signature = Sign(sk, m);
    L = (m, s) :: L;
    return s;
  }
  
  (** BEGIN Adversary *)
  var pk' : pkey
  var sk' : skey
 
  fun S1(m:message) : signature = {
    var s : signature = Sign(sk', m);
    return s;
  }

  fun S2(m:message) : signature = {
    var s : signature;
    s = S(m);
    return s;
  }

  abs A2 = A2 {S1, S2}

  fun B(_pk:pkey) : message * signature = {
    var m : message;
    var s : signature;
    var b : bool;
    (pk', sk') = KG();
    (b, m, s) = A2(pk', _pk);
    return (m, s);
  }
  (** END Adversary *)
 
  fun Main() : bool = {
    var m : message;
    var s : signature;
    (pk, sk) = KG();
    L = [];
    (m, s) = B(pk);
    return (Verify(pk, m, s) && !mem((m,s), L));
  }
}.

equiv S2_S2 : EF_2CMA.S2 ~ Red2.S2 :
  pk1{1} = pk'{2} && sk1{1} = sk'{2} && pk2{1} = pk{2} && sk2{1} = sk{2} && 
  ={m} &&
  forall (ms:message * signature), !mem(ms,L2{1}) => !mem(ms,L{2})
  ==>
  pk1{1} = pk'{2} && sk1{1} = sk'{2} && pk2{1} = pk{2} && sk2{1} = sk{2} && 
  ={res} &&
  forall (ms:message * signature), !mem(ms,L2{1}) => !mem(ms,L{2}).
proof.
 inline{2} S; trivial.
save.

equiv EF_2CMA_Red2 : EF_2CMA.Main ~ Red2.Main : true ==> res{1} && !b{1} => res{2}.
proof.
 inline B; swap{1} 1.
 auto
  (pk1{1} = pk'{2} && sk1{1} = sk'{2} && pk2{1} = pk{2} && sk2{1} = sk{2} &&
   forall (ms:message * signature), !mem(ms,L2{1}) => !mem(ms,L{2})).
 derandomize; wp; trivial.
save.

(* 
** MARION
**
** The proof strategy is to show that winning in Red implies winning
** in EF_CMA, and that winning EF_2CMA is winning Red or the
** equivalent game Red2 (attaking pk2,sk2 instead of pk1,sk1). The
** first statement is formalized as:
**
**  equiv Fact1 : Red.Main ~ EF_CMA.Main : true ==> res{1} => res{2}. 
**
** I can't manage to do anything to compare the adversaries, seemingly
** because I can't get around the fact that A2 and A do not have the
** same interface. How can I get to say something like "Ared is an
** instance of A in UNF1"
*)

(* 
** SANTIAGO
**
**
** A different proof strategy could be to build an adversary B
** against EF_CMA of (KG,Sign,Verify) that uses an adversary A2
** against EF_2CMA and chooses uniformly at random which instance to
** simulate using its own oracle and which to simulate using a freshly
** generated key pair.
**
** As we discussed in Sophia, we do not have yet implemented an
** instantiation mechanism that would you allow to prove that a
** concrete adversary is an instance of an abstract one.
*)

(* 
** MARION
**
** I now prove that winning Red is equivalent to winning
** EF_2CMA if the adversary chooses to attack key-pair 1, formalized as : 
**
**  equiv Fact2 : Red.Main ~ EF_2CMA.Main : true ==> res{1} <=> n{2}=1 && b{2}.
**
** Here I'm stuck because I don't know how to tell "get rid of this
** b'=pVerif(...) because it does not appear in what I prove. How do I
** do that ?
*)

(*
** SANTIAGO
**
** You will not have the problem you mention when you formalize Verify
** as a deterministic operator
*)

(*
** MARION
**
**  claim Eq_1 : Red.Main[res] + Red2.Main[res] = EF_2CMA.Main[res] 
**    using Fact1 and Fact2 
** 
** How do I write using 2 facts ?
*)

(*
** SANTIAGO
**
** You would need to prove first using 'compute'
**
**  EF_2CMA.Main[res] = EF_2CMA.Main[res && n=1] + EF_2CMA.Main[res && n=2]
**
** Then bound each term on the right separately, and finally combine both 
*)

claim Split : EF_2CMA.Main[res] = EF_2CMA.Main[res && b] + EF_2CMA.Main[res && !b]
compute.

claim EF_2CMA_Red1 : EF_2CMA.Main[res && b ] <= Red1.Main[res] auto.

claim EF_2CMA_Red2 : EF_2CMA.Main[res && !b] <= Red2.Main[res] auto.

claim Red1_EF_CMA : Red1.Main[res] <= EF_CMA.Main[res]
admit. (* by abstraction. *)

claim Red2_EF_CMA : Red2.Main[res] <= EF_CMA.Main[res]
admit. (* by abstraction. *)

(*
** SANTIAGO
**
** I removed the unnecessary absolute value bars from the claim below
*)

lemma aux : 1%r + 1%r = 2%r.

claim Conclusion : EF_2CMA.Main[res] <= 2%r * EF_CMA.Main[res].
