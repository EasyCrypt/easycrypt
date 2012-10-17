cnst k : int.  (*security parameter*)
cnst u : int.
cnst v : int.

(* k is positive, and all other constants are at least as
big as k*)
axiom k_pos : 0 <= k.
axiom u_pos : k <= u.
axiom v_pos : k <= v.

type skey = bitstring{u}.   (* Type of secret  key*)
type pkey = bitstring{v}. (*Type of public key*)
type keypair  = skey * pkey. (*Type of keypair is a secret and a public key *)
type message = bool list. (* Message is a bitstring of arbitrary length*)
type cipher = bool list.
pop gen_keypair : int -> keypair. (*Probabilistic operator used to generate private-public key pair*)

(** The adversary **)
adversary A1(pk:pkey) : message * message { }.
   adversary A2(y:cipher) : bool { }.

op Enc : (pkey, bitstring{k}, message) -> cipher.
cnst t:int.
(*The INDCPA game*)
game INDCPA = {

   abs A1 = A1 {}
   abs A2 = A2 {}

(* Here's the function that generates a pair of keys *)
fun KG(k:int) : keypair = {
	var z : keypair = gen_keypair(k);
	return z;
}
(* How do I say that z is actually two keys? Do I need to? *)



fun Main() : bool = {
    var pk : pkey;
    var sk : skey;
    var b, b' : bool;
    var m0, m1 : message;
    var c : cipher;
    var r : bitstring{k};

    (sk, pk) = KG(k);
    (m0, m1) = A1(pk);
    b = {0,1};
    r = {0,1}^k;
    c = Enc(pk, r, b? m1 : m0);


    b' = A2(c);
    return b = b';
  }
}.
game DUMMY = INDCPA where
    Main = {
    var pk : pkey;
    var sk : skey;
    var b, b' : bool;
    var m0, m1 : message;
    var c : cipher;
    var r : bitstring{k};

    (sk, pk) = KG(k);
    (m0, m1) = A1(pk);
    b = {0,1};
    r = {0,1}^k;
    c = Enc(pk, r, b? m1 : m0);
    b' = A2(c);
    return b = b';
  }
.
(* prover "alt-ergo". *)
equiv Fact1 : INDCPA.Main ~ DUMMY.Main : true ==> res{1} => res{2}.
auto.
*rnd.
auto.
save.

claim conclusion: INDCPA.Main[res] <= DUMMY.Main[res] using Fact1.

