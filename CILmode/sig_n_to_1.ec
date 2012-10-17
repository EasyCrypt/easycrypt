(* Proof that the advantage of an adversary attacking (in parallel) n instances
of a signature scheme with independently generated keys is bounded
by n times that of an adversary attacking one instance of the scheme.
My understanding is that I cannot formalize this "n" parameter,
so I chose to start with 2.*)


type plaintext.
type certificate.
type skey.
type pkey.
type rand.

(* to write the hypothesis that the verification of legitimate signatures
succeeds, as I couldn't manage to write an "axiom" on probabilistic operators,
I explicitely formalized the randomness of the signature algorithms
(keygen, signing, and verification algos)*)

pop coin_toss : () -> rand.
op KG : rand -> pkey * skey.
op Sig : (rand,skey, plaintext) -> certificate.
op Verif : (rand,pkey, plaintext, certificate) -> bool.

op check_validity_keys : (pkey,skey) -> bool.

axiom valid_keys :
forall (r : rand), check_validity_keys(fst(KG(r)),snd(KG(r))).

axiom good_sig : 
  forall (pk : pkey, sk : skey, m : plaintext, r,r' : rand), 
  check_validity_keys(pk,sk)=true => Verif(r',pk,m,Sig(r,sk,m))= true.

adversary A(pk : pkey) : plaintext * certificate
 { plaintext -> certificate}.


(* unforgery game for signature algo Sig*)
game UNF_1={
(* these variables are declared here because I tried using 
them in equiv statements and I reckon this requires
them to be "visibly" declared in the game. This assumption
has been made all alonf the code. *)
  var sk : skey
  var fm : plaintext
  var fc : certificate
  var b : bool

  fun SigOracle(m: plaintext) : certificate = {
    var c : certificate;
    var r : rand;
    r = coin_toss();
    c = Sig(r,sk,m);
    return c;
    }

fun pVerif(pk : pkey, m: plaintext, c : certificate) : bool = {
    var r : rand;
    var b' : bool;
    r = coin_toss();
    b' = Verif(r,pk,m,c);
    return b';
    }
  
  abs A = A {SigOracle}

  fun Main () : bool = {
    var coin : rand;
    var pk : pkey;

    coin = coin_toss();
    (pk,sk) = KG (coin);
    (fm,fc) = A(pk);
     b= pVerif(pk,fm,fc);
     return b;
  }

}.

adversary A2(pk1, pk2 : pkey) : int * plaintext * certificate
 { plaintext -> certificate; plaintext -> certificate}.

game UNF2={

  var sk1 : skey

  fun SigOracle_1(m: plaintext) : certificate = {
    var c : certificate;
    var r : rand;
    r = coin_toss();
    c = Sig(r,sk1,m);
    return c;
    }

  var sk2 : skey

  fun SigOracle_2(m: plaintext) : certificate = {
    var c : certificate;
    var r : rand;
    r = coin_toss();
    c = Sig(r,sk2,m);
    return c;
    }

  fun pVerif(pk : pkey, m: plaintext, c : certificate) : bool = {
    var r : rand;
    var b : bool;
    r = coin_toss();
    b = Verif(r,pk,m,c);
    return b;
    }

  abs A2 = A2 {SigOracle_1, SigOracle_2}

  var n : int
  var b : bool 
  fun Main () : bool = {
    var coin1 : rand;
    var coin2 : rand; 
    var pk1 : pkey;
    var pk2 : pkey;
    var m : plaintext;
    var c : certificate;
    var b' : bool;

    coin1 = coin_toss();
    (pk1,sk1) = KG (coin1);
    coin2 = coin_toss();
    (pk2,sk2) = KG(coin2);
    (n,m,c) = A2(pk1,pk2);
    b=pVerif(pk1,m,c);
    b'=pVerif(pk2,m,c);
     return (b||b');
  }

}.
 

(* Here I declare the intermediate game with the adversary
against UNF1 simulating the adversary against UNF2.*)

game red={

  var sk1 : skey


  fun SigOracle_1(m: plaintext) : certificate = {
    var c : certificate;
    var r : rand;
    r = coin_toss();
    c = Sig(r,sk1,m);
    return c;
    }
  
  var sk2 : skey

  fun SigOracle_2(m: plaintext) : certificate = {
    var c : certificate;
    var r : rand;
    r = coin_toss();
    c = Sig(r,sk2,m);
    return c;
    }

  fun pVerif(pk : pkey, m: plaintext, c : certificate) : bool = {
    var r : rand;
    var b : bool;
    r = coin_toss();
    b = Verif(r,pk,m,c);
    return b;
    }

  (* adversary for reduction  : begin*)
  abs A2 = A2 {SigOracle_1,SigOracle_2}

  var fm : plaintext
  var fc : certificate
  var n : int
  var b : bool
  fun Ared(pk1: pkey) : plaintext * certificate = {
     var coin_2 : rand; 
     var pk_2 : pkey; 
     var sk_2 : skey; 
    var b' : bool;
    var m : plaintext;
    var c : certificate;

    coin_2 = coin_toss();
    (pk_2,sk_2) = KG(coin_2);
    (n,m,c)=A2(pk1,pk_2);
    return (m,c);
    }
 (* end aversary for reduction  *)

  fun Main () : bool = {
    var coin1 : rand;
    var pk1 : pkey;
    coin1 = coin_toss();
    (pk1,sk1) = KG(coin1);
    (fm,fc) = Ared(pk1);
    b=pVerif(pk1,fm,fc);
     return (b && n=1);
  }
}.

(* The proof strategy is to show that winning in red implies
winning in UNF1, and that winning UNF2 is winning red or
the equivalent game red2 (attaking pk2,sk2 instead of pk1,sk1).
The first statement is formalized as:  *)

(* equiv Fact1 : red.Main~ UNF_1.Main : true ==> ( res{1} => res{2}). *)
(* I can't manage to do anything to compare the adversaries,
seemingly because I can't get around the fact that A2 and A do not
have the same interface. How can I get to say something like 
"Ared is an instance of A in UNF1" *)
(* save. *)


(* Once I get the Fact1, I can go on with  *)
(* claim Ineq_1 : red.Main[res] <= UNF_1.Main[res] *)
(* using Fact1. *)

(* I now prove that winning red is equivalent to winning
UNF2 if the adversary chooses to attack key-pair 1, formalized as : *)
(*equiv Fact2 : red.Main ~ UNF2.Main : true ==> (res{1} <=> (n{2}=1 && b{2})).*)
(* Here I'm stuck because I don't know how to tell "get rid of this
b'=pVerif(...) because it does not appear in what I prove. How do I do that ? *)


(* TODO : definir red2 pareil que red mais avec cle 2, and
prove 
1/ Ineq_2 (analogous to Ineq_1) comparing red2 and UNF_1,
probably using a Fact3 mimicing Fact1
2/ a Fact4 (analogous to Fact2) comparing red2 and UNF2 when n=2
*)


(*claim Eq_1 : red.Main[res]+ red2.Main[res]=UNF2.Main[res] 
using Fact1 and  Fact2 => how do I write using 2 facts ? *)

(* then, it seems that this can follow easily*)
claim Conclusion : |UNF2.Main[res]| <= 2%r  *   |UNF_1.Main[res]|