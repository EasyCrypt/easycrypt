type group. 
type skey       = int.
type pkey       = group.
type plaintext  = group.
type ciphertext = group * group.

cnst q : int.
cnst g : group.

(* If we use the native modulo "alt-ergo" is not able
   to perform the proof.
   So we declare an operator (%%) which stand for the modulo ...
*)

op [%%] : (int,int) -> int as mod_int.
op [*] : (group, group) -> group as group_mult.
op [^] : (group, int) -> group   as group_pow.
op log : group -> int.

axiom q_pos : 0 < q.

axiom group_pow_add : 
 forall (x, y:int), g ^ (x + y) = g ^ x * g ^ y.

axiom group_pow_mult :
 forall (x, y:int),  (g ^ x) ^ y = g ^ (x * y).

axiom log_pow : 
 forall (g':group), g ^ log(g') = g'.

axiom pow_mod : 
 forall (z:int), g ^ (z%%q) = g ^ z.

axiom mod_add : 
 forall (x,y:int), (x%%q + y)%%q = (x + y)%%q.

axiom mod_small : 
 forall (x:int), 0 <= x => x < q => x%%q = x.

axiom mod_sub : 
 forall (x, y:int), (x%%q - y)%%q = (x - y)%%q. 

axiom mod_bound : 
 forall (x:int), 0 <= x%%q && x%%q < q. 

adversary A1(pk:pkey)               : plaintext * plaintext {}.
adversary A2(pk:pkey, c:ciphertext) : bool {}.


game INDCPA = {
  fun KG() : skey * pkey = {
    var x : int = [0..q-1];
    return (x, g^x);
  }

  fun Enc(pk:pkey, m:plaintext): ciphertext = {
    var y : int = [0..q-1];
    return (g^y, (pk^y) * m);
  }

  abs A1 = A1 {}
  abs A2 = A2 {}
  
  fun Main() : bool = {
    var sk : skey;
    var pk : pkey;
    var m0, m1, mb : plaintext;
    var c: ciphertext;
    var b, b' : bool;

    (sk,pk) = KG();
    (m0,m1) = A1(pk);
    b = {0,1};
    mb = if b then m0 else m1;
    c = Enc(pk, mb);
    b' = A2(pk, c);
    return (b = b');
  } 
}.


game DDH0 = {
  abs A1 = A1 {}
  abs A2 = A2 {}
  
  fun B(gx:group, gy:group, gz:group) : bool = {
    var m0, m1, mb : plaintext;
    var c : ciphertext;
    var b, b' : bool;
 
    (m0, m1) = A1(gx);
    b = {0,1};
    mb = b ? m0 : m1;
    c = (gy, gz * mb);
    b' = A2(gx,c);
    return (b = b');
  }

  fun Main() : bool = {
    var x, y : int;
    var d : bool;

    x = [0..q-1];
    y = [0..q-1];
    d = B(g^x, g^y, g^(x*y));
    return d;
  }     
}.

game DDH1 = DDH0 where 
  Main = {
    var x, y, z : int;
    var d : bool;

    x = [0..q-1];
    y = [0..q-1];
    z = [0..q-1];
    d = B(g^x, g^y, g^z);
    return d;
  }.


game G1 = INDCPA where 
  Main = {
    var x, y, z : int;
    var gx, gy, gz : group;
    var d, b, b' : bool;
    var m0, m1, mb : plaintext;
    var c : ciphertext;
 
    x = [0..(q - 1)];
    y = [0..(q - 1)];
    gx = g^x;
    gy = g^y;
    (m0, m1) = A1 (gx);
    b = {0,1};
    mb = b ? m0 : m1; 
    z = [0..(q - 1)];
    gz = g^z;
    c = (gy, gz * mb);
    b' = A2 (gx, c);
    d = (b = b');
    return d;
  }.


game G2 = G1 where 
  Main = {
    var x, y, z : int;
    var gx, gy, gz : group;
    var d, b, b' : bool;
    var m0, m1, mb : plaintext;
    var c : ciphertext;
 
    x = [0..(q - 1)];
    y = [0..(q - 1)];
    gx = g^x;
    gy = g^y;
    (m0, m1) = A1(gx);
    z = [0..(q - 1)];
    gz = g^z;
    c = (gy, gz); 
    b' = A2 (gx, c);
    b = {0,1};
    d = b = b';
    return d;
  }.
 
prover "alt-ergo".
timeout 1.

claim Pr1 : INDCPA.Main[res] = DDH0.Main[res] 
auto.
       
claim Pr2 : G1.Main[res] = DDH1.Main[res] 
auto.

timeout 3.

equiv Fact3 : G1.Main ~ G2.Main : (true).
 swap{2} [10-10] -4;auto.
 rnd ((z + log(if b then m0 else m1){2}) %% q), 
     ((z - log(if b then m0 else m1){2}) %% q).
 trivial; auto; trivial.
save.

claim Pr3 : G1.Main[res] = G2.Main[res]
using Fact3.

claim Pr4 : G2.Main[res] = 1%r / 2%r
compute.

claim Conclusion : 
 | INDCPA.Main[res] - 1%r / 2%r | = | DDH0.Main[res] - DDH1.Main[res] |.
