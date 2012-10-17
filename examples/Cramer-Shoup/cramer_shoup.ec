prover "alt-ergo", vampire, z3, cvc3.

(* ************* Group ***************)
type group.

cnst q : int.   (* prime order of the group *)
cnst g : group. (* a generator of the group *)

op [^] : (group, int) -> group   as group_pow.
op [*] : (group, group) -> group as group_mul.

axiom q_pos : 1 < q.
 
axiom group_pow_mod : 
 forall (g1:group, x:int), g1^x = g1^(x%q).

axiom group_pow_mult :
 forall (g1:group, x, y:int)[ (g1^x^y)], (g1^x)^y = g1^(x*y)  .

axiom group_pow_comm :
 forall (g1:group, x, y:int), (g1^x)^y = (g1^y)^x.  

axiom group_pow_mult_distr :
 forall (g1:group, x, y:int),  g1^x * g1^y = g1^(x+y).

axiom group_mult_assoc : 
 forall (g1, g2, g3:group),  g1 * (g2 * g3) = (g1 * g2) * g3.

axiom group_mul_pow_distr : 
 forall (g1, g2:group, x:int), (g1 * g2) ^ x = (g1^x) * (g2^x).

axiom group_mult_comm :
 forall (g1, g2:group),  g1 * g2 = g2 * g1. 

axiom plus_mod_idemp_l : 
 forall (a, b, n:int), (a + b)%n = ((a%n) + b)%n.

lemma plus_mod_idemp_r :
 forall (a, b, n:int), (a + b)%n = (a + (b%n))%n.

lemma plus_mod : 
 forall (a, b, n:int), (a + b)%n = (a%n + (b%n))%n.

lemma minus_mod_idemp_l : 
 forall (a, b, n:int), (a - b)%n = ((a%n) - b)%n.

axiom minus_mod_idemp_r : 
 forall (a, b, n:int), (a - b)%n = (a - (b%n))%n.

lemma minus_mod : 
 forall (a, b, n:int), (a - b)%n = (a%n - (b%n))%n.

axiom mult_mod_idemp_l : 
 forall (a, b, n:int), (a * b)%n = ((a%n) * b)%n.

lemma mult_mod_idemp_r : 
 forall (a, b, n:int), (a * b)%n = (a * (b%n))%n.

lemma mult_mod : 
 forall (a, b, n:int), (a * b)%n = (a%n * (b%n))%n.

axiom mod_small : 
 forall (a, n:int),  0 <= a => a < n => a%n = a.

lemma mod_mod : 
 forall (a, n:int), (a%n)%n = a%n.

lemma mod_zero_opp: 
 forall (a, b : int), 0 < b => a%b = 0 => (-a)%b = 0.

(* This holds because q is prime, and so Z/qZ is an integral field *)
axiom mult_mod_q_integral :
  forall (a, b:int), (a*b)%q = 0 => (a%q = 0 || b%q = 0).

lemma minus_mod_diff : 
  forall (u, u':int),
   0 <= u => u <= q-1 => 
   0 <= u' => u' <= q-1 => 
   u <> u' =>   
   (u'-u)%q <> 0.

lemma minus_mult_mod_0 : 
  forall (u, u', pg:int),
   0 <= u => u <= q-1 => 
   0 <= u' => u' <= q-1 => 
   1 <= pg => pg <= q-1 => 
   u <> u' =>   
   ((u'-u) * pg)%q <> 0. 

lemma aux1 : 
  forall (x, z:int),
    0 <= z => z <= q - 1 =>
    ((z - x)%q + x)%q = z.

lemma aux2 : 
  forall (x, z:int),
   0 <= z => z <= q - 1 =>
   ((z + x)%q - x)%q = z.

(* inv() Computes the inverse of an integer modulo q *)
op inv_q : int -> int.
(** 
   This operator can be defined provided q is prime :
   inv(x) = 
    if (x%q = 0) { Return default value }
    else { 
      Since x%q <> 0 and q is prime, gcd(q,x) = 1. Hence,  
      Using the extended Euclidean algorithm, compute u,v
      satisfying Bezout's identity q*u + x*v = gcd(q,x) = 1.
      Return v%q
*)
axiom inv_correct : 
  forall (x:int), 0 <> x%q => (inv_q(x) * x)%q = 1.

(* Discrete logarithm in base g *)
op dlg : group -> int.

axiom dlg_pow : 
  forall (g1:group), g^dlg(g1) = g1.

axiom pow_dlg : 
  forall (x:int), dlg(g^x) = x%q.

axiom dlg_bound : 
  forall (g1:group), 0 <= dlg(g1) && dlg(g1) <= q-1.

axiom done_in_coq : 
  forall (U, U', z, pg, Rc, aux:int),
    0 <= U => U <= q-1 =>
    0 <= U' => U' <= q-1 =>
    1 <= pg => pg <= q-1 =>
    U <> U' =>
    0 <= Rc => Rc <= q-1 =>
    ( ((((U*(z-pg*Rc) + (pg * U')*Rc + aux)%q - U*z) - aux) * 
      inv_q((U'-U)*pg))%q = Rc &&
      ((((U*(z-(pg*((((Rc-U*z) - aux)* inv_q((U'-U)*pg))%q)))) + 
       ((pg*U')*((((Rc-(U*z))-aux)* inv_q((U'-U)*pg))%q))) + aux)%q) =
      Rc).


axiom done_in_coq2_1 : 
  forall (Rap, pg:int), 
    0 <= Rap => Rap <= q - 1 =>
    1 <= pg  => pg <= q - 1 =>
    ((((pg * Rap) % q) * inv_q(pg)) % q) = Rap.

axiom done_in_coq2_2 : 
  forall (Rap, pg:int), 
    0 <= Rap => Rap <= q - 1 =>
    1 <= pg => pg <= q - 1 =>
    ((pg * ((Rap * inv_q (pg)) % q)) % q) = Rap.

axiom done_in_coq3 :
  forall (U, U', x, y, y1 ,y2, v, pg, Rd:int),
    0 <= U  => U <= q - 1 =>
    0 <= U' => U' <= q - 1 =>
    0 <= Rd => Rd <= q - 1 =>
    1 <= pg => pg <= q - 1 => 
    U <> U' =>
    ( (((((((U * (((x - (pg * Rd)) % q) + (v * ((y - (pg * y2)) % q)))) +
      ((pg * U') * (Rd + (v * y2)))) % q) - (U * (x + (v * y)))) *
      inv_q (((U' - U) * pg))) - (v * y2)) % q) = Rd
      && 
      (((U *
        (((x - (pg * ((((Rd - (U * (x + (v * y)))) * inv_q (((U' - U) * pg)))
       - (v * y2)) % q))) % q) + (v * ((y - (pg * y2)) % q)))) + ((pg *
       U') * ((( ( (Rd - (U * (x + (v * y)))) * inv_q ( ( (U' - U) *
       pg))) - (v * y2)) % q) + (v * y2)))) % q) = Rd ).

axiom done_in_coq4 :
  forall (x, x1, x2, y, y1, y2,  
          pg, Rd, U, U', V, vd, u, u', r:int,
          a, ap, d:group, Ly2:int list),
    x2 = ((Rd - U*(x+V*y))*inv_q((U'-U)*pg) - V*y2)%q =>
    x1 = (x - pg*x2)%q =>
    y1 = (y - pg*y2)%q => 
    0 <= y2 => y2 <= q-1 =>
    1 <= pg => pg <= q-1 =>
    ap <> a^pg =>
    vd <> V =>
    0 <= vd => vd <= q-1 =>
    0 <= V => V <= q-1 =>
    u = dlg(a) =>
    u' = (dlg(ap) * inv_q(pg))%q =>
    d = a^(x1+vd*y1) * ap^(x2+vd*y2) => 
    r = dlg(d) =>
    mem(y2, ((((r -u*(x+vd*y))*inv_q((u'-u)*pg) - 
           (Rd-U*(x+V *y))*inv_q((U'-U)*pg))*inv_q(vd-V))%q)::Ly2).

unset plus_mod, minus_mod, mult_mod, minus_mod_diff, minus_mult_mod_0, 
      done_in_coq, done_in_coq2_1, done_in_coq2_2, 
      done_in_coq3, done_in_coq4, 
      mod_mod, mod_zero_opp, mult_mod_q_integral, 
      mult_mod_idemp_r, mult_mod_idemp_l, aux1, aux2.


(* ************* Messages ***************)
type message = group.

cnst bot_message : message.


(* ***********  Ciphertexts *************)
(* TODO : replace by (group * group) * (group * group) *)
type cipher = group * group * group * group.

cnst bot_cipher : cipher.


(* *********** Public keys *************)
type public_key = int * group * group * group * group.


(* ********** Hash function ************)
(* Assume the key space for the hash function is [0..k] *)
cnst k : int.

axiom k_pos : 0 <= k.

op H : (int, group, group, group) -> int as Hash.

axiom H_bound : 
 forall (hk:int,g1, g2, g3:group),
  0 <= H(hk,g1,g2,g3) && H(hk,g1,g2,g3) <= q-1.


(* ********* IND-CCA Adversary *********)

adversary A1(pk:public_key) : message * message { cipher -> message }.
adversary A2(pk:public_key, c:cipher) : bool    { cipher -> message }.

cnst qD : int. (* Maximum number of decryption queries *)

axiom qD_pos : 0 <= qD.

axiom done_in_coq6 : 
  forall (L:int list, x:real),
    x <= (length(L)%r / ((q-1) + 1)%r) =>
    real_of_bool(length(L) <= qD) * x <= qD%r/q%r.

axiom done_in_coq5 : 
  forall (La, Lap, Lc, Ld:int list, x, y, z, w:real),
    0%r <= w => 
    0%r <= x =>
    0%r <= y =>
    0%r <= z =>
    w <= (length (La)%r / (((0 <= (q - 1)) ? (q - 1) : 0) + 1)%r) =>
    z <= (length (Lap)%r / (((0 <= (q - 1)) ? (q - 1) : 0) + 1)%r) =>
    y <= (length (Lc)%r / (((0 <= (q - 1)) ? (q - 1) : 0) + 1)%r) => 
    x <=  (length (Ld)%r / (((0 <= (q - 1)) ? (q - 1) : 0) + 1)%r) =>
    (((((((
     real_of_bool ((length(La) <= qD)) * 
     real_of_bool ((length(Lap) <= qD))) * 
     real_of_bool ((length (Lc) <= qD))) *
     real_of_bool ((length (Ld) <= qD))) * x) * y) * z) * w) <= 
     ((qD%r /q%r) * (qD%r/q%r) * (qD%r/q%r) * (qD%r/q%r)).

unset done_in_coq5, done_in_coq6.

(* **** IND-CCA game for Cramer-Shoup **)
game CCA0 = {
  var x1, x2, y1, y2, z1, z2 : int
  var pg : int
  var hk:int
  var gp, e, f, h : group 

  fun KG(): bool = {
    x1 = [0..q-1]; x2 = [0..q-1];
    y1 = [0..q-1]; y2 = [0..q-1]; 
    z1 = [0..q-1]; z2 = [0..q-1];
    pg = [1..q-1];
    hk = [0..k];
    gp = g ^ pg;
    e = g ^ x1 * gp ^ x2;
    f = g ^ y1 * gp ^ y2;
    h = g ^ z1 * gp ^ z2;
    return true;
  }

  fun Enc (hk0:int, gp0, e0, f0, h0:group, m:message) : cipher = {
    var u : int = [0..q-1];
    var a,ap,b0,c,d:group;
    var v : int;

    a = g^u; ap =gp0^u;
    b0 = h0^u; c = b0 * m;
    v = H(hk0,a,ap,c);
    d = e0^u * f0^(u*v);
    return (a,ap,c,d);    
  }

  var LD : cipher list 
  var cm_def : bool
  var cm : cipher

  fun Dec(ci:cipher) : message = {
    var m:message;
    var a,ap,c,d,bd:group;
    var vd:int;

    if (length(LD) < qD && !(cm_def && ci = cm)) {
      LD = ci::LD;
      (a,ap,c,d) = ci;
      vd = H(hk, a,ap,c);
      if (d = a^(x1+vd*y1) * ap^(x2+vd*y2)) {
        bd = a^z1 * ap^z2;
        m = c * bd^(-1);
      } else { 
        m = bot_message;
      }
    } else {
      m = bot_message;
    }
    return m;
  } 
  
  abs A1 = A1 {Dec}
  abs A2 = A2 {Dec}

  fun Main (): bool = {
    var b, b' : bool;
    var m0,m1:message;
    var b_ : bool;
  
    LD = [];
    cm_def = false;
    cm = bot_cipher;

    b_ = KG();
    (m0,m1) = A1((hk,gp,e,f,h));
    b = {0,1};
    cm = Enc(hk, gp,e,f,h, if b then m0 else m1);
    cm_def = true;
    b' = A2 ((hk,gp,e,f,h), cm);
    return (b = b');
  }   

}.


(* ** Inline KG, Enc,
      replace b0 = h^u by b0 = a^z1*ap^z2  
      replace d = e^u * f^(u*v) by d = a^(x1+v*y1) * ap^(x2+v*y2) 
*)

game CCA1 = CCA0 
  where Main = {
    var b, b' : bool;
    var m0,m1:message;
    var a,ap,b0,c,d:group;
    var u, v : int;

    LD = [];
    cm_def = false;
    cm = bot_cipher;
    x1 = [0..q-1]; x2 = [0..q-1];
    y1 = [0..q-1]; y2 = [0..q-1]; 
    z1 = [0..q-1]; z2 = [0..q-1];
    pg = [1..q-1];
    hk = [0..k];
    gp = g ^ pg;
    e = g ^ x1 * gp ^ x2;
    f = g ^ y1 * gp ^ y2;
    h = g ^ z1 * gp ^ z2;
    (m0,m1) = A1((hk,gp,e,f,h));
    b = {0,1};
    u = [0..q-1];
    a = g^u; ap =gp^u;
    b0 = a^z1 * ap^ z2; c = b0 * (if b then m0 else m1);
    v = H(hk,a,ap,c);
    d = a^(x1+v*y1) * ap^(x2+v*y2);
    cm = (a,ap,c,d);    
    cm_def = true;
    b' = A2 ((hk,gp,e,f,h), cm);
    return (b = b');
  }.   

equiv CCA0_CCA1 : CCA0.Main ~ CCA1.Main : true ==> ={res}
 by auto.

claim Pr_0_1 : CCA0.Main[res] = CCA1.Main[res] 
 using CCA0_CCA1.

unset group_pow_comm, group_mult_comm.

game DDH0 = {
  var x1, x2, y1, y2, z1, z2 : int
  var pg : int
  var hk:int
  var gp, e, f, h : group (*  gp = g ^ pg *)
  var LD : cipher list 
  var cm_def : bool
  var cm : cipher

  fun Dec(ci:cipher) : message = {
    var m:message;
    var a,ap,c,d,bd:group;
    var vd:int;
    if (length(LD) < qD && !(cm_def && ci = cm)) {
      LD = ci::LD;
      (a,ap,c,d) = ci;
      vd = H(hk,a,ap,c);
      if (d = a^(x1+vd*y1) * ap^(x2+vd*y2)) {
        bd = a^z1 * ap^z2;
        m = c * bd^(-1);
      } else { 
        m = bot_message;
      }
    } else {
      m = bot_message;
    }
    return m;
  } 

  abs A1 = A1 {Dec}
  abs A2 = A2 {Dec}

  fun B(g1:group, g2:group, g3:group) : bool = {
    var b, b' : bool;
    var m0,m1:message;
    var a,ap,b0,c,d:group;
    var u, v : int;

    LD = [];
    cm_def = false;
    cm = bot_cipher;
    x1 = [0..q-1]; x2 = [0..q-1];
    y1 = [0..q-1]; y2 = [0..q-1]; 
    z1 = [0..q-1]; z2 = [0..q-1];
    hk = [0..k];
    gp = g1;
    e = g ^ x1 * gp ^ x2;
    f = g ^ y1 * gp ^ y2;
    h = g ^ z1 * gp ^ z2;
    (m0,m1) = A1((hk,gp,e,f,h));
    b = {0,1};
    a = g2; ap =g3;
    b0 = a^z1 * ap^ z2; c = b0 * (if b then m0 else m1);
    v = H(hk,a,ap,c);
    d = a^(x1+v*y1) * ap^(x2+v*y2);
    cm = (a,ap,c,d);    
    cm_def = true;
    b' = A2 ((hk,gp,e,f,h), cm);
    return (b = b');
  }   

  fun Main() : bool = {
    var x, y, z : int;
    var b' : bool;
    x = [1..q-1]; y = [0..q-1]; z = x * y;
    b' = B(g^x, g^y, g^z);
    return b';
  }
}.


equiv CCA1_DDH0 : CCA1.Main ~ DDH0.Main :  true ==> ={res} .
 inline {2}.
 derandomize.
 auto (={LD,cm_def, hk,x1,x2,y1,y2,z1,z2} && (cm_def{1} => ={cm})) .
 swap {2} 1 7; swap {2} 1 9; trivial.
save.

claim Pr_1_DDH0 : CCA1.Main[res] = DDH0.Main[res] 
using CCA1_DDH0.


game DDH1 = DDH0 
  where Main = {
    var x, y, z, u' : int;
    var b' : bool;

    x = [1..q-1]; y = [0..q-1];
    u' = [0..q-1]; z = x * u';
    b' = B(g^x, g^y, g^z);
    return b';
 }.

game CCA2 = CCA1 
  var bad1 : bool
  where Dec = {
    var m:message;
    var a,ap,c,d,bd:group;
    var vd:int;

    if (length(LD) < qD && !(cm_def && ci = cm)) {
      LD = ci::LD;
      (a,ap,c,d) = ci;
      vd = H(hk, a,ap,c);
      if (ap = a^pg) {
        if (d = a^(x1+vd*y1) * ap^(x2+vd*y2)) {
          bd = a^z1 * ap^z2;
          m = c * bd^(-1);
         } else { 
          m = bot_message;
         }
      } else {
        if (d = a^(x1+vd*y1) * ap^(x2+vd*y2)) {
	  bad1 = true;
          bd = a^z1 * ap^z2;
          m = c * bd^(-1);
         } else { 
          m = bot_message;
         }
      } 
    } else {
      m = bot_message;
    }
    return m;
  } 

  and Main = {
    var b, b' : bool;
    var m0,m1:message;
    var a,ap,b0,c,d:group;
    var u, u', v : int;

    LD = [];
    cm_def = false;
    cm = bot_cipher;
    bad1 = false;
    x1 = [0..q-1]; x2 = [0..q-1];
    y1 = [0..q-1]; y2 = [0..q-1]; 
    z1 = [0..q-1]; z2 = [0..q-1];
    pg = [1..q-1];
    hk = [0..k];
    gp = g ^ pg;
    e = g ^ x1 * gp ^ x2;
    f = g ^ y1 * gp ^ y2;
    h = g ^ z1 * gp ^ z2;
    (m0,m1) = A1((hk,gp,e,f,h));
    b = {0,1};
    u = [0..q-1]; u' = [0..q-1];
    a = g^u; ap =gp^u';
    b0 = a^z1 * ap^ z2; c = b0 * (if b then m0 else m1);
    v = H(hk,a,ap,c);
    d = a^(x1+v*y1) * ap^(x2+v*y2);
    cm = (a,ap,c,d);    
    cm_def = true;
    b' = A2 ((hk,gp,e,f,h), cm);
    return (b = b');
  }.

equiv CCA2_DDH1 : CCA2.Main ~ DDH1.Main : true ==> ={res}.
 inline {2}.
 derandomize.
 auto (={LD,cm_def, hk,x1,x2,y1,y2,z1,z2} && (cm_def{1} => ={cm})) .
 push {2} 8;swap {2} [1-2] 9;trivial.
save.

claim Pr_2_DDH1 : CCA2.Main[res] = DDH1.Main[res] 
using CCA2_DDH1.

(* Up to this point we have *)
claim bound_1 : 
 | CCA0.Main[res] - CCA2.Main[res] | = | DDH0.Main[res] - DDH1.Main[res] | .

unset Pr_0_1, Pr_1_DDH0, Pr_2_DDH1.


(* **** Next transformation : Modification of the decryption oracle ***)
(* 
  - Reject if ap != a^pg, 
    Makes a difference only if 
     {ap <> a ^ pg} &&
     {d = a^(x1+H(a,ap,c)*y1) * ap1^(x2+H(a,ap,c)*y2)}
    So if there is a ci = (a,ap,c,d) in LD such that 
     {ap <> a ^ pg} &&
     {d = a^(x1+H(a,ap,c)*y1) * ap1^(x2+H(a,ap,c)*y2)}

  - Next we introduce w = (w1 + pg * w2)%q, for w = x, y, z in the Main, 
    and we modify the decryption oracle using the three invariants, and
    the fact that ap = a ^ pg :
     this means replacing 
         d = a^(x1+vd*y1) * ap^(x2+vd*y2) by d = a^(x + vd*y)
     and bd = a^z1 * ap^z2 by bd = a^z

  - Finally for w = x, y, z we replace 
         w1 = [0..q-1]; w2 = [0..q-1]; w =  (w1 + pg * w2)%q;
    in the Main by 
         w = [0..q-1]; w2 = [0..q-1]; w1 =  (w - pg * w2)%q; 
    Which generate the same distribution for w, w1, w2

  - Remark : We allocate u and u' in the global variables U and U'
             for the next transition
*)
game CCA3 = CCA2
  var x, y, z, U, U' : int
  where Dec = {
    var m:message;
    var a,ap,c,d,bd:group;
    var vd:int;
    if (length(LD) < qD && !(cm_def && ci = cm)) {
      LD = ci::LD;
      (a,ap,c,d) = ci;
      vd = H(hk,a,ap,c);
      if (ap = a^pg) {
        if (d = a^(x + vd*y)) {
          bd = a^z;
          m = c * bd^(-1);
        } else { 
          m = bot_message;
        }
      } else {
        if (d = a^(x1+vd*y1) * ap^(x2+vd*y2)) { bad1 = true; }
        m = bot_message;
      }
    } else { 
      m = bot_message;
    }
    return m;
  }    
  and Main = {
    var b, b' : bool;
    var m0,m1:message;
    var a,ap,b0,c,d:group;
    var v : int;
    LD = [];
    cm_def = false;
    cm = bot_cipher;
    bad1 = false;
    (*  Generation of the secret key *)
    pg = [1..q-1];
    x = [0..q-1]; x2 = [0..q-1]; x1 = (x - pg*x2)%q;
    y = [0..q-1]; y2 = [0..q-1]; y1 = (y - pg*y2)%q; 
    z = [0..q-1]; z2 = [0..q-1]; z1 = (z - pg*z2)%q; 
     (*  Generation of the public key *)
    hk = [0..k];
    gp = g ^ pg;
    e = g ^ x;
    f = g ^ y;
    h = g ^ z;
    b = {0,1};
    U = [0..q-1]; U' = [0..q-1];

    (m0,m1) = A1((hk,gp,e,f,h));
    a = g^U; ap =gp^U';
    b0 = a^z1 * ap^ z2; c = b0 * (if b then m0 else m1);
    v = H(hk,a,ap,c);
    d = a^(x1+v*y1) * ap^(x2+v*y2);
    cm = (a,ap,c,d);    
    cm_def = true;
    b' = A2 ((hk,gp,e,f,h), cm);
    return (b = b');
  }.   

set aux1, aux2.
unset plus_mod_idemp_l, plus_mod_idemp_r, 
      minus_mod_idemp_l, minus_mod_idemp_r.

equiv CCA2_CCA3_Dec : CCA2.Dec ~ CCA3.Dec :
 !bad1{1} && !bad1{2} &&
 ={ci,LD,hk,pg,x1,x2,y1,y2,z1,z2,cm_def,cm} &&
   (x = (x1 + pg* x2)%q){2} &&
   (y = (y1 + pg* y2)%q){2} &&
   (z = (z1 + pg* z2)%q){2}
    ==>
  bad1{1} = bad1{2} &&
  (!bad1{1} =>
    (={res,LD,hk,pg,x1,x2,y1,y2,z1,z2,cm_def,cm} &&
      (x = (x1 + pg* x2)%q){2} &&
      (y = (y1 + pg* y2)%q){2} &&
      (z = (z1 + pg* z2)%q){2})).
wp.
trivial.
set group_mult_comm, group_pow_comm.  
trivial.
save.
   
equiv CCA2_CCA3 : CCA2.Main ~ CCA3.Main : true ==> 
    ={bad1}
    &&
    ( !bad1{1} => ={res} ).
 derandomize.
 auto  
   upto (bad1)
   with (={LD,hk,pg,x1,x2,y1,y2,z1,z2,cm_def,cm} &&
             (x = (x1 + pg* x2)%q){2} &&
             (y = (y1 + pg* y2)%q){2} &&
             (z = (z1 + pg* z2)%q){2}).
 swap {1} 7 -6; !4 rnd. (* u' u b hk *) 
 (* z *)
 pop 1.
 rnd ((z_0 + (pg_0 * z2_0)%q), ((z_0 - pg_0 * z2_0)%q).
 rnd.

 (* y *)
 pop 1.
 rnd ((y_0 + pg_0 * y2_0)%q), ((y_0 - pg_0 * y2_0)%q).
 rnd.

 (* x *)
 pop 1.
 rnd ((x_0 + pg_0 * x2_0)%q), ((x_0 - pg_0 * x2_0)%q).
 rnd.

 (* pg *) 
 rnd. 
 unset group_mult_comm, group_pow_comm.  
 set aux1, aux2.
 trivial.
 
  unset aux1, aux2.
  trivial.
save.

unset group_mult_comm, group_pow_comm.  
unset aux1, aux2.

claim Pr_2_3_bad1 : 
  | CCA2.Main[res] - CCA3.Main[res] | <=  CCA3.Main[bad1] 
 using CCA2_CCA3.


(* Up to this point we have *)
claim bound_2 : 
 | CCA0.Main[res] - CCA3.Main[res] | <=
 | DDH0.Main[res] - DDH1.Main[res] | + CCA3.Main[bad1].

unset bound_1, Pr_2_3_bad1.

(* ** Next Transformation: eliminate the dependence on mb  ***)
(*  
   - We replace
        z2 = [0..q-1]; b0 = a^z1 * ap^ z2; c = b0 * (b ? m0 : m1);
     in the Main by 
          z2 = [0..q-1];
          Rc = (U*(z-pg*z2) + pg*U'*z2 + dlg(b ? m0 : m1))%q ;
          c = g ^ Rc;
   - Since z1 is not used any more, we remove it.

   - We replace 
       z2 = [0..q-1];
       Rc = (U<>U') ? (U*(z-pg*z2) + pg*U'*z2 + dlg(b ? m0 : m1))%q : z2;
     in the Main by
       Rc = [0..q-1];
       z2 = (((Rc-U*z)-dlg(b?m0:m1)) * inv_q((U'-U)*pg))%q;
   - Since z2 is not used any more we remove it
   - We postpone sampling b, wich is not used until the end of the game

   CCA3 and CCA4 are equivalent while U <> U'
*)

game CCA4 = CCA3
 var Rc : int 
 where Main = {
    var b,b': bool;
    var m0,m1:message;
    var a,ap,c,d:group;
    var v, r : int;
    LD = [];
    cm_def = false;
    cm = bot_cipher;
    bad1 = false;
    pg = [1..q-1];
    x = [0..q-1]; x2 = [0..q-1]; x1 = (x - pg*x2)%q;
    y = [0..q-1]; y2 = [0..q-1]; y1 = (y - pg*y2)%q; 
    U = [0..q-1]; U' = [0..q-1];
    z = [0..q-1]; 
    hk = [0..k];
    gp = g ^ pg;
    e = g ^ x;
    f = g ^ y;
    h = g ^ z;
    (m0,m1) = A1((hk,gp,e,f,h));
    a = g^U; ap =gp^U';
    Rc = [0..q-1];
    c = g ^ Rc;
    v = H(hk,a,ap,c);
    d = a^(x1+v*y1) * ap^(x2+v*y2);
    cm = (a,ap,c,d);    
    cm_def = true;
    b' = A2 ( (hk,gp,e,f,h), cm);
    b = {0,1};
    return (b = b');
  }.   

set done_in_coq.

equiv CCA3_CCA4 : CCA3.Main ~ CCA4.Main : true ==>
  (U=U'){1} <=> (U=U'){2} &&
  ( (U<>U'){1} => ={res,bad1}).
 swap {1} [21-22] -9.
 swap {1} [15-16] 1.
 app 15 15 (={LD, cm_def, cm, bad1, pg, x, x2, x1, y, y2, y1, U, U', z, hk} &&
            0 <= U{2} && U{2} <= q-1 &&
            0 <= U'{2} && U'{2} <= q-1 &&
            1 <= pg{2} && pg{2} <= q-1 ).
  (* head of the code *)
  idtac.
  *(rnd;auto) .
  (* tail of the code *)
  case {1}: (U = U').
  (* first case (U=U') *)
  trivial.
  (* second case (U<>U') *)
  pop {2} 10.
  swap{1} [1-2] 8.
  app 12 10(={LD,cm_def,cm,bad1,pg,x,x2,x1,y,y2,y1,U,U',z,hk,a,ap,c,
              b,gp,e,f,h}).
  wp; rnd 
   ((U*(z-pg*Rc) + pg*(U'*Rc) + dlg(b ? m0 : m1))%q),
   ((((Rc-U*z)-dlg(b?m0:m1)) * inv_q((U'-U)*pg))%q).
  auto (={LD,hk,pg,x,x1,x2,y,y1,y2,z,cm_def,bad1,cm}).
  trivial.
  (* tail *)
  auto (={LD,hk,pg,x,x1,x2,y,y1,y2,z,cm_def,bad1,cm}).
save.
unset done_in_coq.

claim bound_4_U_U' : CCA4.Main[U=U'] = 1%r/q%r compute.

claim bound_4_res : CCA4.Main[res] = 1%r/2%r compute.

claim Pr_3_4_res : | CCA3.Main[res] - CCA4.Main[res] | <= CCA4.Main[U=U'] 
 using CCA3_CCA4.

claim Pr_3_bad1_split : 
 CCA3.Main[bad1] = CCA3.Main[bad1 && U=U'] + CCA3.Main[bad1 && U<>U']
 split.

claim Pr_3_4_U_U' : CCA3.Main[bad1 && U=U'] <= CCA4.Main[U=U'] 
 using CCA3_CCA4.

claim Pr_3_4_bad1 : CCA3.Main[bad1 && U<>U'] = CCA4.Main[bad1 && U<>U']
 using CCA3_CCA4.

(* This lemma is just a hint to the prover *)
claim bound_aux_3 :  
   | CCA0.Main[res] - CCA4.Main[res] | <=
   | CCA0.Main[res] - CCA3.Main[res] | + | CCA3.Main[res] - CCA4.Main[res] | .

claim bound_3 : 
 | CCA0.Main[res] -  1%r/2%r | <=
 | DDH0.Main[res] - DDH1.Main[res] | + 2%r * (1%r/q%r) + CCA4.Main[bad1 && U<>U'].


unset bound_2,bound_4_U_U',bound_4_res,Pr_3_4_res,Pr_3_4_bad1,bound_aux_3,
  Pr_3_bad1_split, Pr_3_4_U_U'.

(* ***************** Next transition ****************)
(* We focus on CCA4.Main[bad1 && U<>U']
   - Since  
       a = g^u; ap =gp^u';
       r = [0..q-1];
       c = g ^ r;
       v = H(a,ap,c);
       d = a^(x1+v*y1) * ap^(x2+v*y2);
       cm = (a,ap,c,d);    
     do not depend any more of m0 and m1, we move those instructions
     before the call to A1;
   - We introduce a variable bad_cm which is set when the advervary call
     the decryption oracle with cm in the first part of the game
   - We replace 
       x2 = [0..q-1]; d = a^(x1+v*y1) * ap^(x2+v*y2);
     by
       Rd = [0..q-1]; d = g^Rd;
       x2 = ((Rd - U*(x+v*y))*inv_q((U'-U)*pg) - v*y2)%q;
     This leads to the same distribution.

   We obtain the the game CCA4_1
   - We modify the decryption oracle such that it rejects cm
     This leads to game CCA5
 
   CCA4_1 and CCA5 are equivalent while !bad_cm
*)

game CCA4_1 = CCA4
  var bad_cm : bool
  var Rd : int
  where Dec = {
    var m:message;
    var a,ap,c,d,bd:group;
    var vd:int;

    if (length(LD) < qD && !cm_def && ci = cm) { bad_cm = true;}

    if (length(LD) < qD && !(cm_def && ci = cm)) {
      LD = ci::LD;
      (a,ap,c,d) = ci;
      vd = H(hk,a,ap,c);
      if (ap = a^pg) {
        if (d = a^(x + vd*y)) {
          bd = a^z;
          m = c * bd^(-1);
        } else { 
          m = bot_message;
        }
      } else {
        if (d = a^(x1+vd*y1) * ap^(x2+vd*y2)) { bad1 = true; }
        m = bot_message;
      }
    } else { 
      m = bot_message;
    }
    return m;
  } 
  and Main = {  
    var b' : bool;
    var m0,m1:message;
    var a,ap,c,d:group;
    var v, r : int;
    LD = [];
    cm_def = false;
    cm = bot_cipher;
    bad1 = false;
    bad_cm = false;
    pg = [1..q-1];
    x = [0..q-1]; 
    y = [0..q-1]; y2 = [0..q-1]; y1 = (y - pg*y2)%q; 
    U = [0..q-1]; U' = [0..q-1];
    z = [0..q-1]; 
    hk = [0..k];
    gp = g ^ pg;
    e = g ^ x;
    f = g ^ y;
    h = g ^ z;
    a = g^U; ap =gp^U';
    Rc = [0..q-1];
    c = g ^ Rc;
    v = H(hk,a,ap,c); 
    Rd = [0..q-1];
    x2 = ((Rd - U*(x+v*y))*inv_q((U'-U)*pg) - v*y2)%q;
    x1 = (x - pg*x2)%q;
    d = g^Rd;
    cm = (a,ap,c,d);    
    (m0,m1) = A1( (hk,gp,e,f,h) );
    cm_def = true;
    b' = A2 ( (hk,gp,e,f,h), cm);
    return true;
  }.

game CCA5 = CCA4_1
  where Dec = { 
   var m:message;
    var a,ap,c,d,bd:group;
    var vd:int;

    if (length(LD) < qD && !cm_def && ci = cm) { bad_cm = true;}
    if (length(LD) < qD && !ci = cm) {
      LD = ci::LD;
      (a,ap,c,d) = ci;
      vd = H(hk,a,ap,c);
      if (ap = a^pg) {
        if (d = a^(x + vd*y)) {
          bd = a^z;
          m = c * bd^(-1);
        } else { 
          m = bot_message;
        }
      } else {
        if (d = a^(x1+vd*y1) * ap^(x2+vd*y2)) { bad1 = true; }
        m = bot_message;
      }
    } else { 
      m = bot_message;
    }
    return m;
  }.


equiv CCA4_CCA4_1 : CCA4.Main ~ CCA4_1.Main : true ==> 
   ={U,U'} && ( (U<>U'){1} => ={bad1}).
rnd{1}.
swap {1} [21-26] -1.
swap {1} [7-8] 16.
app 11 12 (={LD, cm_def, cm, bad1, pg, x, y, y2, y1, U, U'} &&
           1 <= pg{1} && pg{1} <= q-1 &&
           0 <= U{1}  && U{1}  <= q-1 &&
           0 <= U'{1} && U'{1} <= q-1 &&
           (y1 = (y-pg*y2)%q){1} && !cm_def{1}
          ).
(* head *)
*(rnd;auto).
(* tail *)
case {1} : (U = U').
(* U = U' *)
trivial.
(* !U = U' *)
auto inv ={LD,hk,pg,x,x1,x2,y,y1,y2,z,cm_def,bad1} && (cm_def{1} => ={cm}).
rnd 
    ((U*((x - pg*Rd)%q+v*(y - pg*y2)%q) + (pg*U')*(Rd+v*y2))%q),
      (((Rd - U*(x+v*y))*inv_q((U'-U)*pg) - v*y2)%q).
set done_in_coq3.
auto;*(rnd;auto).
unset done_in_coq3.
trivial.
save.

equiv auto CCA4_1_CCA5 : CCA4_1.Main ~ CCA5.Main : true ==>
       ={bad_cm} && ({ !bad_cm{1} } => ={bad1,U,U'})
 inv upto {bad_cm} with ={LD,hk,pg,x,x1,x2,y,y1,y2,z,cm_def,bad1,cm}.

claim Pr_CCA4_bad1 : CCA4.Main[bad1 && U<>U'] = CCA4_1.Main[bad1 && U<>U'] 
  using CCA4_CCA4_1 .

claim Pr_CCA4_1_split : CCA4_1.Main[bad1 && U<>U'] =
 CCA4_1.Main[(bad1 && U<>U') && bad_cm] + 
 CCA4_1.Main[(bad1 && U<>U') && !bad_cm]
split.

claim Pr_CCA4_1_bad_cm : CCA4_1.Main[(bad1 && U<>U') && bad_cm] <=
 CCA4_1.Main[bad_cm]
same.

claim Pr_CCA4_1_bad1 : CCA4_1.Main[(bad1 && U<>U') && !bad_cm] <=
 CCA5.Main[bad1 && U<>U'] 
using CCA4_1_CCA5.

(* At this point we have *)
claim bound_4 : 
 | CCA0.Main[res] -  1%r/2%r | <=
                   | DDH0.Main[res] - DDH1.Main[res] | +
                   2%r * (1%r/q%r)  + 
                   CCA5.Main[bad1 && U<>U'] + CCA4_1.Main[bad_cm].

unset bound_3,  Pr_CCA4_bad1,Pr_CCA4_1_split,Pr_CCA4_1_bad_cm, Pr_CCA4_1_bad1.

(************************************************************)
(* We focus on the probability of CCA4_1.[bad_cm] *)
(* The idea is the following:
   - bad_cm can be set only in the first part of the game, it is set 
     when cm is in LD.
   - In this part the adversary does not known cm
   - Futhermore, if we do not focus on bad1, the decryption oracle
     does not depend on x1, y1, x2, y2 (not depending on x2 is crucial)
   - This allows us to see cm as (((g^U,g^Rap),g^Rc),g^Rd)
     where U, Rap, Rc, Rd are uniformly sampled 
     (and independant of the adversary view),
     Hence, the probability that cm is in LD is (|LD|/q)^4
*)

game CCA4_2 = {
  var x, y, y2, z, pg : int
  var hk:int
  var gp, e, f, h : group
  var LD : cipher list
  var cm_def : bool
  var cm : cipher

  var La,Lap,Lc,Ld : int list

  fun Dec1(ci:cipher) : message = {
    var m:message;
    var a,ap,c,d,bd:group;
    var vd:int;
    var aapc : group * group * group;
    var aap : group * group;
    if (length(LD) < qD) { 
      LD = ci::LD;
      (aapc,d) = ci;
      (aap,c) = aapc;
      (a,ap) = aap;
      vd = H(hk,a,ap,c);
      La = dlg(a)::La;
      Lap = dlg(ap)::Lap;
      Lc = dlg(c)::Lc;
      Ld = dlg(d)::Ld;
      vd = H(hk,a,ap,c);
      if (ap = a^pg && d = a^(x + vd*y)) {
          bd = a^z;
          m = c * bd^(-1);
      } else {
        m = bot_message;
      }
    } else { 
      m = bot_message;
    }
    return m;
  }

  fun Dec2(ci:cipher) : message = {
    var m:message;
    var a,ap,c,d,bd:group;
    var vd:int;
    var aapc : group * group * group;
    var aap : group * group;
    if (length(LD) < qD && !(ci = cm)) {
      LD = ci::LD;
      (aapc,d) = ci;
      (aap,c) = aapc;
      (a,ap) = aap;
      vd = H(hk,a,ap,c);
      if (ap = a^pg && d = a^(x + vd*y)) {
          bd = a^z;
          m = c * bd^(-1);
      } else {
        m = bot_message;
      }
    } else { 
      m = bot_message;
    }
    return m;
  }  

  abs A1 = A1 {Dec1}
  abs A2 = A2 {Dec2}

  var U,Rap,Rc,Rd : int

  fun Main (): bool = {
    var b' : bool;
    var m0,m1:message;
    var a,ap,c,d:group;
    var v, r : int;
    LD = [];
    La = [];
    Lap = [];
    Lc = [];
    Ld = [];
    cm_def = false;
    cm = bot_cipher;
    pg = [1..q-1];
    x = [0..q-1]; 
    y = [0..q-1]; y2 = [0..q-1]; 
    z = [0..q-1]; 
    hk = [0..k];
    gp = g ^ pg;
    e = g ^ x;
    f = g ^ y;
    h = g ^ z;
    (m0,m1) = A1( (hk,gp,e,f,h) );
    U = [0..q-1];  Rap = [0..q-1];
    a = g^U; ap =g^Rap;
    Rc = [0..q-1];
    c = g ^ Rc;
    v = H(hk,a,ap,c);
    Rd = [0..q-1];
    d = g^Rd;
    cm = (a,ap,c,d);
    cm_def = true;
    b' = A2 ( (hk,gp,e,f,h), cm);
    return true;
  }
}.


equiv CCA4_1_CCA4_2 : CCA4_1.Main ~ CCA4_2.Main : 
      true ==> 
       { length(La{2}) <= qD } &&
       { length(Lap{2}) <= qD } &&
       { length(Lc{2}) <= qD } &&
       { length(Ld{2}) <= qD } &&
       ({bad_cm{1}} => 
       ( {(in(U,La)){2}} &&
         {(in(Rap,Lap)){2}} &&
         {(in(Rc,Lc)){2}} &&
         {(in(Rd,Ld)){2}} )).
 swap {2} 18 10.
 swap {2} [18-19] -6.

 call inv ={x,y,z,cm,cm_def,LD,pg,hk} &&
           {cm_def{1} = true} &&
           { length(La{2}) <= qD } &&
           { length(Lap{2}) <= qD } &&
           { length(Lc{2}) <= qD } &&
           { length(Ld{2}) <= qD } &&
           ({bad_cm{1}} => 
           ( {(in(U,La)){2}} &&
             {(in(Rap,Lap)){2}} &&
             {(in(Rc,Lc)){2}} &&
             {(in(Rd,Ld)){2}} )).

 auto inv ={U,Rc,Rd,x,y,z,cm,cm_def,LD,pg,hk}  && 
           {(cm = (((g^U,g^Rap),g^Rc),g^Rd)){2}} &&
           {(U = U%q){1}} &&
           {(Rap = Rap%q){2}} &&
           {(Rc = Rc%q){1}} &&
           {(Rd = Rd%q){1}} &&
           {cm_def{1} = false} &&
           { length(La{2}) <= qD } && 
           { length(La{2}) = length(LD{2}) } &&
           { length(Lap{2}) <= qD } &&
           { length(Lap{2}) = length(LD{2}) } &&
           { length(Lc{2}) <= qD } &&
           { length(Lc{2}) = length(LD{2}) } &&
           { length(Ld{2}) <= qD } &&
           { length(Ld{2}) = length(LD{2}) } &&
           ({bad_cm{1}} => 
           ( {(in(U,La)){2}} &&
             {(in(Rap,Lap)){2}} && 
             {(in(Rc,Lc)){2}} &&
             {(in(Rd,Ld)){2}})).
 
 !2 (rnd;auto).
 !2 rnd.
 rnd ((pg * Rap)%q), ((Rap * inv_q(pg))%q).
 set done_in_coq2_1, done_in_coq2_2, mod_mod.
 *(rnd;auto).
 unset done_in_coq2_1, done_in_coq2_2, mod_mod.
save.

claim Pr_CCA4_1 : CCA4_1.Main[bad_cm] <=
      CCA4_2.Main[ in(U,La) &&
                    in(Rap,Lap) &&
                    in(Rc,Lc) &&
                    in(Rd,Ld) && 
                    length(La) <= qD &&
                    length(Lap) <= qD && 
                    length(Lc) <= qD && 
                    length(Ld) <= qD ] 
 using CCA4_1_CCA4_2.


(* "alt-ergo" sems to segfault on this goal, we switch to simplify *)

set done_in_coq5, done_in_coq6.

claim Pr_CCA4_2 : 
 CCA4_2.Main[ in(U,La) &&
                    in(Rap,Lap) &&
                    in(Rc,Lc) &&
                    in(Rd,Ld) && 
                    length(La) <= qD &&
                    length(Lap) <= qD && 
                    length(Lc) <= qD && 
                    length(Ld) <= qD ] <=
   ((qD%r /q%r)*(qD%r/q%r)*(qD%r/q%r)*(qD%r/q%r))
compute.


(* At this point we have *)
claim bound_5 : 
 | CCA0.Main[res] -  1%r/2%r | <=
                   | DDH0.Main[res] - DDH1.Main[res] | +
                   2%r * (1%r/q%r)  + 
                   ((qD%r /q%r)*(qD%r/q%r)*(qD%r/q%r)*(qD%r/q%r)) + 
                   CCA5.Main[bad1 && U<>U'].
unset bound_4, done_in_coq5,  Pr_CCA4_1, Pr_CCA4_2. 

(**** Next transition, we focus on CCA5.Main[bad1 && U<>U'] ****)
(* - Since we are no longer intereseted on bad_cm, we remove it 
   - We make a split the computation of the bound depending on bad2 
*)

game CCA6 = CCA5 
 var bad2 : bool
 where Dec = {
    var m:message;
    var a,ap,c,d,bd:group;
    var vd:int;
    var aapc : group * group * group;
    var aap : group * group;
    if (length(LD) < qD && !ci = cm) {
      LD = ci::LD;
      (aapc,d) = ci;
      (aap,c) = aapc;
      (a,ap) = aap;
      vd = H(hk,a,ap,c);
      if (ap = a^pg) {
        if (d = a^(x + vd*y)) {
          bd = a^z;
          m = c * bd^(-1);
        } else { 
          m = bot_message;
        }
      } else {
        if (d = a^(x1+vd*y1) * ap^(x2+vd*y2)) { 
	  if (vd=H(hk, g^U, gp^U', g^Rc)) {
	     bad2 = true;
          };
          bad1 = true;
        };
        m = bot_message;
      }
    } else { 
      m = bot_message;
    }
    return m;
  }
 and Main = {  
    var b' : bool;
    var m0,m1:message;
    var a,ap,c,d:group;
    var v, r : int;
    LD = [];
    cm_def = false;
    cm = bot_cipher;
    bad1 = false;
    bad2 = false;
    pg = [1..q-1];
    x = [0..q-1]; 
    y = [0..q-1]; y2 = [0..q-1]; y1 = (y - pg*y2)%q; 
    U = [0..q-1]; U' = [0..q-1];
    z = [0..q-1]; 
    hk = [0..k];
    gp = g ^ pg;
    e = g ^ x;
    f = g ^ y;
    h = g ^ z;
    a = g^U; ap =gp^U';
    Rc = [0..q-1];
    c = g ^ Rc;
    v = H(hk,a,ap,c); 
    Rd = [0..q-1];
    x2 = ((Rd - U*(x+v*y))*inv_q((U'-U)*pg) - v*y2)%q;
    x1 = (x - pg*x2)%q;
    d = g^Rd;
    cm = (a,ap,c,d);    
    (m0,m1) = A1( (hk,gp,e,f,h) );
    cm_def = true;
    b' = A2 ( (hk,gp,e,f,h), cm);
    return true;
  }.

equiv auto CCA5_CCA6 : CCA5.Main ~ CCA6.Main : true ==> ={bad1, U, U'}
 inv ={x,y,z,pg,hk,x1,x2,y1,y2,LD,cm,bad1,U,U'}.

claim Pr_CCA5 : CCA5.Main[bad1 && U<>U'] = CCA6.Main[bad1 && U<>U']
 using CCA5_CCA6.

claim Pr_CCA6 : CCA6.Main[bad1 && U<>U'] =
  CCA6.Main[(bad1 && U<>U') && bad2] + CCA6.Main[(bad1 && U<>U') && !bad2]
split.

claim Pr_CCA6_bad2 :
  CCA6.Main[(bad1 && U<>U') && bad2] <=
  CCA6.Main[U<>U' && bad2]
same.

(***** We prove that CCA6.Main[bad2] is small since H is TCR ****)

(* TODO change the type of H to int, group * group * group -> int *)

game TCR = {
  var LD: cipher list
  var U, U', Rc, Rd, x, x1, x2, y, y1, y2, z, hk, pg : int
  var gp, e, f, h, Cola, Colap, Colc : group
  var cm:cipher

  fun Dec (ci:cipher) : message = {
    var m:message;
    var a,ap,c,d,bd:group;
    var vd:int;
    var aapc : group * group * group;
    var aap : group * group;
    if (length(LD) < qD && !ci = cm) {
      LD = ci::LD;
      (aapc,d) = ci;
      (aap,c) = aapc;
      (a,ap) = aap;
      vd = H(hk,a,ap,c);
      if (ap = a^pg) {
        if (d = a^(x + vd*y)) {
          bd = a^z;
          m = c * bd^(-1);
        } else { 
          m = bot_message;
        }
      } else {
        if (d = a^(x1+vd*y1) * ap^(x2+vd*y2) && 
            vd = H(hk, g^U, gp^U', g^Rc))
          { Cola = a;
            Colap = ap;
            Colc = c; };
        m = bot_message;
      }
    } else { 
      m = bot_message;
    }
    return m;
  }

  abs A1 = A1 {Dec}

  abs A2 = A2 {Dec}

  fun CF1() : group * group * group = {
    var a,ap,c:group;
    pg = [1..q-1];
    U = [0..q-1]; U' = [0..q-1];
    gp = g ^ pg;   
    a = g^U; ap =gp^U';
    Rc = [0..q-1];
    c = g ^ Rc;  
    return ((a,ap),c);
  }

  fun CF2(hk1:int) : group * group * group = {
    var b': bool;
    var m0,m1:message;
    var a,ap,c,d:group;
    var v, r : int;
    LD = [];
    Cola = bot_message;
    Colap = bot_message;
    Colc = bot_message;
    x = [0..q-1]; 
    y = [0..q-1]; y2 = [0..q-1]; y1 = (y - pg*y2)%q; 
    z = [0..q-1]; 
    hk = hk1;
    e = g ^ x;
    f = g ^ y;
    h = g ^ z;
    a = g^U; ap =gp^U';
    c = g ^ Rc;
    v = H(hk,a,ap,c); 
    Rd = [0..q-1]; 
    x2 = ((Rd - U*(x+v*y))*inv_q((U'-U)*pg) - v*y2)%q;
    x1 = (x - pg*x2)%q;
    d = g^Rd;
    cm = (a,ap,c,d);    
    (m0,m1) = A1( (hk,gp,e,f,h) );
    b' = A2 ( (hk,gp,e,f,h), cm);
    return ((Cola,Colap),Colc);
  }


  fun Main () : bool = {
    var m0, m1 :  group * group * group;
    var aap0, aap1 : group * group;
    var a0,ap0,c0,a1,ap1,c1 : group;
    var hk1:int;
    m0 = CF1();
    hk1 = [0..k];
    m1 = CF2(hk1);
    (aap0,c0) = m0;
    (a0,ap0) = aap0;
    (aap1,c1) = m1;
    (a1,ap1) = aap1;
    return H(hk1,a0,ap0,c0) = H(hk1,a1,ap1,c1) && !m0 = m1;
  }
}.

(** REMARK: the fact that (U<>U') is not used and can be removed *)
equiv CCA6_TCR : CCA6.Main ~ TCR.Main : true ==>
   {(U<>U'){1}} => { bad2{1}} => {res{2}}.
inline {2} CF2; inline{2} CF1.
swap{1} 6 -5.
swap{1} [11-12] -9.
app 3 3 (={pg,U,U'} && 
           { 1 <= pg{1} } && { pg{1} <= q-1 } &&
           { 0 <= U{1} } && { U{1} <= q-1 } &&
           { 0 <= U'{1} } && { U'{1} <= q-1 } ).
 (* head *)
 do 3 rnd;trivial.
 (* tail *)
 case{1}:(U=U').
 (* U = U' *)
 trivial.
 (* U<>U' *)

 app 24 29 
  (={LD,hk,x,x1,x2,y,y1,y2,z,U,U',Rc,pg,gp,Rd,a,ap,c,d,e,f,h} &&
    {(a = g^U){2}} && {(ap= gp^U'){2}} && {(gp = g^pg){2}} &&
    {(c = g^Rc){2}} && {(d = g^Rd){2}} &&
    {(v = H (hk,a,ap,c)){2}} &&
    {(x1 = (x-pg*x2)%q){2}} && {(y1 = (y-pg*y2)%q){2}} && 
    {(Rd = (U*((x - pg*x2)%q+v*(y - pg*y2)%q) + (pg*U')*(x2+v*y2))%q){2}} &&
    { bad2{1} = false} && { (m0 = ((a, ap), c)){2}} && { (hk = hk1){2}}).
 (* head *)
 swap{1} 18 -17.
 swap{1} 12 -10.
 auto;*(rnd;auto).
 set done_in_coq3.
 trivial.
 unset done_in_coq3.
 (* tail *)
 auto inv ={cm,LD,hk,x,x1,x2,y,y1,y2,z,U,U',Rc,pg,gp} &&
   {(cm =
      (((g^U,gp^U'),g^Rc),
        (g^U)^(x1+H(hk, g^U,gp^U',g^Rc)*y1) * 
           (gp^U')^(x2+H(hk, g^U,gp^U',g^Rc)*y2))){2}} &&
   ({bad2{1}} => ({!(((Cola,Colap),Colc) =((g^U,gp^U'),g^Rc)){2}} &&
                {(H(hk,Cola,Colap,Colc) = H(hk, g^U,gp^U',g^Rc)){2}})).
 trivial.
save.

claim Pr_TCR :  CCA6.Main[U<>U' && bad2] <= TCR.Main[res]
 using CCA6_TCR.

claim bound_6 : 
 | CCA0.Main[res] -  1%r/2%r | <=
 | DDH0.Main[res] - DDH1.Main[res] | + TCR.Main[res] + 
 2%r * (1%r/q%r) + ((qD%r /q%r)*(qD%r/q%r)*(qD%r/q%r)*(qD%r/q%r)) + 
 CCA6.Main[(bad1 && U<>U') && !bad2]. 
                   
unset bound_5, Pr_CCA5, Pr_CCA6, Pr_CCA6_bad2, Pr_TCR. 


(** We Finally we focus on CCA6.Main[(bad1 && U<>U') && !bad2] **)
(* - We assign v=H(hk, g^U, gp^U', g^Rc) to a global variable V
   - Since we consider bad1 only when !bad2, 
     we replace setting bad1 by storing an expression 
     (equal to y2 when bad1 is set and not bad2) in a list Ly2.
     This expression does not depend on x1, x2, y1, y2.
   - We move the assignments to y1 y2 x1 x2 to the end of the game
 
   This leads to the game CCA6_1, and we have 
   
   CCA6.Main[(bad1 && U<>U') && !bad2] <= 
   CCA6_1.Main[y2 in Ly2 && length(Ly2) <= qD]
 
   Since y2 is uniformly and independently sampled, and |Ly2| <= qD, we have 
   CCA6_1.Main[y2 in Ly2] <= qD/q
*)

game CCA6_1 = CCA6
  var Ly2 : int list
  var V : int
  where Dec = {
    var m:message;
    var a,ap,c,d,bd:group;
    var u,u',r,vd:int;
    var aapc : group * group * group;
    var aap : group * group;
    if (length(LD) < qD && !ci = cm) {
      LD = ci::LD;
      (aapc,d) = ci;
      (aap,c) = aapc;
      (a,ap) = aap;
      vd = H(hk,a,ap,c);
      if (ap = a^pg) {
        if (d = a^(x + vd*y)) {
          bd = a^z;
          m = c * bd^(-1);
        } else { 
          m = bot_message;
        }
      } else {
        u = dlg(a);
        u' = (dlg(ap) * inv_q(pg))%q;
        r = dlg(d);
        if ( !vd=V ) 
        {        
           Ly2 = ((((r -u*(x+vd*y))*inv_q((u'-u)*pg) - 
                  (Rd-U*(x+V *y))*inv_q((U'-U)*pg))*inv_q(vd-V))%q) :: Ly2;
        }; 
        m = bot_message;
      }
    } else { 
      m = bot_message;
    }
    return m;
  }
  and Main = {  
    var b' : bool;
    var m0,m1:message;
    var a,ap,c,d:group;
    var r : int;
    LD = [];
    Ly2 = [];
    cm_def = false;
    cm = bot_cipher;
    pg = [1..q-1];
    x = [0..q-1]; 
    y = [0..q-1]; 
    U = [0..q-1]; U' = [0..q-1];
    z = [0..q-1]; 
    hk = [0..k];
    gp = g ^ pg;
    e = g ^ x;
    f = g ^ y;
    h = g ^ z;
    a = g^U; ap =gp^U';
    Rc = [0..q-1];
    c = g ^ Rc;
    V = H(hk,a,ap,c); 
    Rd = [0..q-1];
    d = g^Rd;
    cm = (a,ap,c,d);    
    (m0,m1) = A1( (hk,gp,e,f,h) );
    cm_def = true;
    b' = A2 ( (hk,gp,e,f,h), cm);
    y2 = [0..q-1]; y1 = (y - pg*y2)%q; 
    x2 = ((Rd - U*(x+V*y))*inv_q((U'-U)*pg) - V*y2)%q;
    x1 = (x - pg*x2)%q;
    return true;
  }.

unset group_pow_mod, group_pow_mult, group_pow_comm, group_pow_mult_distr,
  group_mult_assoc, group_mul_pow_distr, group_mult_comm,
  plus_mod_idemp_l, plus_mod_idemp_r, minus_mod_idemp_l, minus_mod_idemp_r,
  mod_small.

set done_in_coq4.

equiv CCA6_CCA6_1 : CCA6.Main ~ CCA6_1.Main : { true } ==> 
   {(!bad2){1}} => {bad1{1}} => { (in(y2,Ly2) && length(Ly2) <= qD){2}}.
swap{2} [27-28] -19.
swap{2} [29-30] -5.
auto inv (={LD,hk,pg,gp,x,x1,x2,y,y1,y2,z,cm,U,U',Rc} && 
    { (0 <= y2){2} } && { (y2 <= q-1){2} } &&
          { (length(Ly2) <=  length(LD)){2} } &&
          { (length(LD) <= qD){2} } &&
          { (x1 = (x - pg*x2)%q){2} } &&
          { (y1 = (y - pg*y2)%q){2} } &&
          { (x2 = ((Rd - U*(x+V*y))*inv_q((U'-U)*pg) - V*y2)%q){2} } &&
          { (V = H(hk, g^U, gp^U', g^Rc)){2} } &&
          { (1 <= pg){2} } && { (pg <= q-1){2} } &&
    ({(!bad2){1}} => {bad1{1}} => { (in(y2,Ly2) && length(Ly2) <= qD){2}})).
*(rnd;auto).
save.
unset done_in_coq4.
 
claim Pr_CCA6_bad1 : CCA6.Main[(bad1 && U<>U') && !bad2] <=
 CCA6_1.Main[in(y2,Ly2) && length(Ly2) <= qD]
using CCA6_CCA6_1.

set done_in_coq6.

claim Pr_CCA6_1 : CCA6_1.Main[in(y2,Ly2) && length(Ly2) <= qD] <= qD%r / q%r
compute.

unset done_in_coq6.

claim conclusion : 
 | CCA0.Main[res] -  1%r/2%r | <=
 | DDH0.Main[res] - DDH1.Main[res] | + TCR.Main[res] + 
 2%r * (1%r/q%r) + (qD%r / q%r) + ((qD%r /q%r)*(qD%r/q%r)*(qD%r/q%r)*(qD%r/q%r)).
