type state.
type group.
type skey       = int.
type pkey       = group.
type plaintext  = group.
type ciphertext = group * group.

cnst q : int.
cnst g : group.

(* If we use the native modulo operator, Alt-Ergo gets lost. *)
op [%%] : (int,int) -> int        as mod_int.
op [*]  : (group, group) -> group as group_mult.
op [^]  : (group, int) -> group   as group_pow.
op log  : group -> int.

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

adversary A1(pk:pkey)               : plaintext * plaintext * state {}.
adversary A2(c:ciphertext, s:state) : bool {}.

game INDCPA = {
  fun KG() : pkey * skey = {
    var x : int = [0..q-1];
    return (g^x, x);
  }

  fun Enc(pk:pkey, m:plaintext): ciphertext = {
    var y : int = [0..q-1];
    return (g^y, pk^y * m);
  }

  abs A1 = A1 {}
  abs A2 = A2 {}
  
  fun Main() : bool = {
    var sk : skey;
    var pk : pkey;
    var m0, m1 : plaintext;
    var c : ciphertext;
    var b, b' : bool;
    var sigma : state;
    (pk,sk) = KG();
    (m0,m1,sigma) = A1(pk);
    b = {0,1};
    c = Enc(pk, b ? m0 : m1);
    b' = A2(c, sigma);
    return (b = b');
  } 
}.

game DDH0 = {
  abs A1 = A1 {}
  abs A2 = A2 {}
  
  fun B(alpha,beta,gamma:group) : bool = {
    var m0, m1 : plaintext;
    var c : ciphertext;
    var b, b' : bool;
    var sigma : state;
    (m0, m1, sigma) = A1(alpha);
    b = {0,1};
    c = (beta, gamma * (b ? m0 : m1));
    b' = A2(c, sigma);
    return (b = b');
  }

  fun Main() : bool = {
    var x, y : int;
    var d : bool;
    x = [0..q-1]; y = [0..q-1];
    d = B(g^x, g^y, g^(x*y));
    return d;
  }     
}.

game DDH1 = DDH0 where 
  Main = {
    var x, y, z : int;
    var d : bool;
    x = [0..q-1]; y = [0..q-1]; z = [0..q-1];
    d = B(g^x, g^y, g^z);
    return d;
  }.

game G = INDCPA where 
  Main = {
    var x, y, z : int;
    var d, b, b' : bool;
    var m0, m1 : plaintext;
    var c : ciphertext;
    var sigma : state;

    x = [0..(q - 1)];
    y = [0..(q - 1)];
    (m0, m1, sigma) = A1(g^x);
    z = [0..(q - 1)];
    b' = A2((g^y, g^z), sigma);
    b = {0,1};
    return b = b';
  }.
 
prover "alt-ergo".
timeout 1.

claim INDCPA_DDH0 : INDCPA.Main[res] = DDH0.Main[res] 
auto.

equiv DDH1_G : DDH1.Main ~ G.Main : true ==> res{1} = res{2}.
 inline B; swap{1} 3 2; swap{1} [5-6] 2; swap{2} 6 -2.
 auto.
 rnd ((z + log(b ? m0 : m1){2}) %% q), ((z - log(b ? m0 : m1){2}) %% q).
 rnd; auto; trivial.
save.
       
claim DDH1_G : DDH1.Main[res] = G.Main[res] 
auto.

claim Independent : G.Main[res] = 1%r / 2%r
compute.

claim Conclusion : 
 | INDCPA.Main[res] - 1%r / 2%r | = | DDH0.Main[res] - DDH1.Main[res] |.
