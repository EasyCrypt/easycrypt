cnst k : int.
cnst l : int.
cnst qD : int.

cnst zero_k : bitstring{k}.
cnst zero_l : bitstring{l}.

type pkey.
type skey.
type plaintext  = bitstring{l}.
type ciphertext = bitstring{k} * bitstring{l}.

axiom k_pos : 0 <= k.

axiom l_pos : 0 <= l.

axiom qD_pos : 0 <= qD.

pop KG : () -> pkey * skey.

op key_pair : (pkey, skey) -> bool.

axiom KG() : k1 = KG() ~ k2 = KG() : true ==> k1 = k2 && key_pair(fst(k1), snd(k1)).

op f    : (pkey, bitstring{k} * bitstring{l}) -> bitstring{k} * bitstring{l}.
op finv : (skey, bitstring{k} * bitstring{l}) -> bitstring{k} * bitstring{l}.

axiom finv_l : 
  forall (pk:pkey, sk:skey), key_pair(pk, sk) =>
  forall (xy:bitstring{k} * bitstring{l}), finv(sk, f(pk, xy)) = xy.

axiom finv_r : 
  forall (pk:pkey, sk:skey), key_pair(pk, sk) =>
  forall (xy:bitstring{k} * bitstring{l}), f(pk, finv(sk, xy)) = xy.

(* Second-Input Extractor *)
op sie : (pkey, bitstring{k} * bitstring{l}, bitstring{k}) -> bitstring{l} option.

axiom sie_spec : 
  forall (pk:pkey, sk:skey), key_pair(pk, sk) =>
  forall (y:bitstring{k} * bitstring{l}, r:bitstring{k}, s:bitstring{l}),
    sie(pk, y, r) = Some(s) <=> y = f(pk, (r, s)).

op find_sie_fst : 
  (pkey, bitstring{k} * bitstring{l}, (bitstring{k}, bitstring{l}) map) -> 
  bitstring{k} option.

axiom find_sie_fst_correct :
  forall (pk:pkey, sk:skey), key_pair(pk, sk) =>
  forall (y:bitstring{k} * bitstring{l}, L:(bitstring{k}, bitstring{l}) map),
    in_dom(fst(finv(sk, y)), L) => 
    find_sie_fst(pk, y, L) = Some(fst(finv(sk, y))).

axiom find_sie_fst_complete : 
  forall (pk:pkey, sk:skey), key_pair(pk, sk) =>
  forall (y:bitstring{k} * bitstring{l}, L:(bitstring{k}, bitstring{l}) map),
    !in_dom(fst(finv(sk, y)), L) => 
    find_sie_fst(pk, y, L) = None.

op find_sie_snd : 
  (pkey, bitstring{k}, (bitstring{k} * bitstring{l}, bitstring{l}) map) -> 
  (bitstring{k} * bitstring{l}) option.

axiom find_sie_snd_correct : 
  forall (pk:pkey, sk:skey), key_pair(pk, sk) =>
  forall (y:bitstring{k} * bitstring{l},
          L:(bitstring{k} * bitstring{l}, bitstring{l}) map),
    find_sie_snd(pk, fst(finv(sk, y)), L) = None => 
    !in_dom(y, L).

axiom find_sie_snd_complete : 
  forall (pk:pkey, sk:skey), key_pair(pk, sk) =>
  forall (r:bitstring{k}, L:(bitstring{k} * bitstring{l}, bitstring{l}) map, 
          y:bitstring{k} * bitstring{l}),
    find_sie_snd(pk, r, L) = Some(y) => 
    in_dom(y, L) && r = fst(finv(sk, y)).

(* Common-Input Extractor *)
op cie : (pkey, bitstring{k} * bitstring{l}, bitstring{k} * bitstring{l}) ->
         (bitstring{k} * bitstring{l} * bitstring{l}) option.

axiom cie_spec : 
  forall (pk:pkey, sk:skey), key_pair(pk, sk) =>
  forall (y,z:bitstring{k} * bitstring{l}, r:bitstring{k}, s,t:bitstring{l}),
    cie(pk, y, z) = Some((r, s, t)) <=> 
    y = f(pk, (r, s)) && z = f(pk, (r, t)) && y <> z.

op find_cie : 
  (pkey, bitstring{k} * bitstring{l},
   (bitstring{k} * bitstring{l},bitstring{l}) map) ->
  (bitstring{k} * bitstring{l}) option.

axiom find_cie_correct : 
  forall (pk:pkey, sk:skey), key_pair(pk, sk) =>
  forall (y,z:bitstring{k} * bitstring{l},
          L:(bitstring{k} * bitstring{l}, bitstring{l}) map),
    find_cie(pk, y, L) = Some(z) => 
    in_dom(z, L) && fst(finv(sk, z)) = fst(finv(sk, y)) && y <> z.

axiom find_cie_complete : 
  forall (pk:pkey, sk:skey), key_pair(pk, sk) =>
  forall (y:ciphertext, L:(bitstring{k} * bitstring{l}, bitstring{l}) map),
    find_cie(pk, y, L) = None =>
    forall (y':ciphertext), 
      in_dom(y', L) => fst(finv(sk, y')) <> fst(finv(sk, y)) || y = y'.

(** Derived lemmas, proved either here or in Coq (lemmas.v) *)

prover "alt-ergo", cvc3.

lemma find_cie_correct' : 
  forall (pk:pkey, sk:skey), key_pair(pk, sk) =>
  forall (y,z:bitstring{k} * bitstring{l}, 
          L:(bitstring{k} * bitstring{l}, bitstring{l}) map),
    find_cie(pk, y, L) = Some(z) =>
    cie(pk, y, z) = Some((fst(finv(sk, y)), snd(finv(sk, y)), snd(finv(sk, z)))).

lemma sie_find_sie_fst :
  forall (pk:pkey, sk:skey), key_pair(pk, sk) =>
  forall (y:bitstring{k} * bitstring{l}, L:(bitstring{k}, bitstring{l}) map),
    find_sie_fst(pk, y, L) <> None => 
    sie(pk, y, proj(find_sie_fst(pk, y, L))) = Some(snd(finv(sk, y))).

axiom cie_find_cie :
  forall (pk:pkey, sk:skey), key_pair(pk, sk) =>
  forall (y:bitstring{k} * bitstring{l}, L:(ciphertext,bitstring{l}) map),
    find_cie(pk, y, L) <> None => 
    cie(pk, y, proj(find_cie(pk, y, L))) = 
    Some((fst(finv(sk, y)), snd(finv(sk, y)), 
         snd(finv(sk, proj(find_cie(pk, y,L)))))).

lemma find_sie_fst_upd : 
  forall (pk:pkey, sk:skey), key_pair(pk, sk) =>
  forall (y:bitstring{k} * bitstring{l}, r:bitstring{k}, g:bitstring{l},
          L:(bitstring{k}, bitstring{l}) map),
    find_sie_fst(pk, y, L[r <- g]) = None <=>
    find_sie_fst(pk, y, L) = None && fst(finv(sk, y)) <> r.

lemma find_sie_snd_cie : 
  forall (pk:pkey, sk:skey), key_pair(pk, sk) =>
  forall (y:bitstring{k} * bitstring{l}, L:(ciphertext, bitstring{l}) map),
    find_sie_snd(pk, fst(finv(sk, y)), L) <> None =>
    find_cie(pk, y, L) <> None =>
    let r,s,t = proj(cie(pk, y, proj(find_cie(pk, y, L)))) in y = f(pk, (r, s)).

axiom find_cie_find_sie_snd :
  forall (pk:pkey, sk:skey), key_pair(pk, sk) =>
  forall (y:bitstring{k} * bitstring{l}, L:(ciphertext, bitstring{l}) map),
    find_cie(pk, y, L) = None => 
    !in_dom(y, L) =>
    find_sie_snd(pk, fst(finv(sk, y)), L) = None.

axiom find_sie_snd_upd :
  forall (pk:pkey, sk:skey), key_pair(pk, sk) =>
  forall (y:bitstring{k} * bitstring{l}, r:bitstring{k}, m:bitstring{l},
          L:(ciphertext, bitstring{l}) map),
    find_sie_snd(pk, r, L[y <- m]) = None <=>
    find_sie_snd(pk, r, L) = None && fst(finv(sk, y)) <> r.

axiom find_cie_upd : 
  forall (pk:pkey, sk:skey), key_pair(pk, sk) =>
  forall (y,y':ciphertext, m:bitstring{l}, L:(ciphertext, bitstring{l}) map),
    find_cie(pk, y, L[y' <- m]) = None <=>
    find_cie(pk, y, L) = None && 
    (fst(finv(sk, y)) <> fst(finv(sk, y')) || y = y').

axiom cie_spec' : 
  forall (pk:pkey, sk:skey), key_pair(pk, sk) =>
  forall (y,z:bitstring{k} * bitstring{l}),
    cie(pk, y, z) <> None => fst(finv(sk, y)) = fst(finv(sk, z)).

axiom find_cie_empty : 
  forall (pk:pkey, sk:skey), key_pair(pk, sk) =>
  forall (y:bitstring{k} * bitstring{l}), find_cie(pk, y, empty_map) = None.

axiom find_sie_snd_empty : 
  forall (pk:pkey, sk:skey), key_pair(pk, sk) =>
  forall(r:bitstring{k}), find_sie_snd(pk, r, empty_map) = None.

lemma xor_2 : forall (x,y:bitstring{l}), x ^^ (y ^^ x) = y.

pred eq_except(M1, M2 : ('a, 'b) map, a : 'a) = 
  forall (w: 'a), w <> a => M1[w] = M2[w] && (in_dom(w,M1) <=> in_dom(w,M2)).

lemma eqe_update_diff : 
  forall(M1, M2 : ('a, 'b) map, a, a' : 'a, b : 'b), 
    eq_except(M1, M2, a) => 
    eq_except(M1[a' <- b], M2[a' <- b], a).

lemma eqe_update_same_L : 
  forall(M1, M2 : ('a, 'b) map, a : 'a, b : 'b), 
    eq_except(M1, M2, a) => eq_except(M1[a <- b], M2, a).

lemma eqe_update_same_R : 
  forall(M1, M2 : ('a, 'b) map, a : 'a, b : 'b), 
    eq_except(M1, M2, a) => eq_except(M1, M2[a <- b], a).

type state.

adversary A1() : plaintext * plaintext * state
  { bitstring{k} -> bitstring{l}; ciphertext -> plaintext }.

adversary A2(st:state, c:ciphertext) : bool
  { bitstring{k} -> bitstring{l}; ciphertext -> plaintext }.

(*
** Game CCA:
** This is the standard CCA experiment
*)
game CCA = {
 var pk    : pkey
 var sk    : skey
 var LG    : (bitstring{k}, bitstring{l}) map
 var cstar : ciphertext
 var cdef  : bool
 var q     : int

 fun G(x:bitstring{k}) : bitstring{l} = {
   var g : bitstring{l} = {0,1}^l;
   if (!in_dom(x, LG)) {
     LG[x] = g; 
   }
   return LG[x];
 }

 fun Enc(m:plaintext) : ciphertext = {
   var g : bitstring{l};
   var r : bitstring{k} = {0,1}^k;
   g = G(r);
   return f(pk, (r, g ^^ m));
 }

 fun Dec(c:ciphertext) : plaintext = {
   var r : bitstring{k};
   var g, s, m : bitstring{l};
   if (q < qD && (!cdef || c <> cstar)) {
     q = q + 1;
     (r, s) = finv(sk, c);
     g = G(r);
     m = g ^^ s;
   }
   else {
     m = zero_l;
   }
   return m;
 }

 abs A1 = A1 {G, Dec}
 abs A2 = A2 {G, Dec}

 fun Main() : bool = {
   var m0, m1 : plaintext;
   var b, b' : bool;
   var st : state;
   (pk, sk) = KG();
   LG = empty_map;
   cdef = false;
   q = 0;
   (m0, m1, st) = A1();
   b = {0,1};
   cstar = Enc(b ? m0 : m1);
   cdef = true;
   b' = A2(st, cstar);
   return (b = b');
 }
}.


(*
** Game G1:
** - Introduce bad
** - Hoist sampling of rstar
** - Inline Enc(mb), G(rstar) in Main and remove Enc procedure
*)
game G1 = CCA
 var rstar : bitstring{k}
 var gstar : bitstring{l}
 var bad   : bool

 where G = {
   var g : bitstring{l} = {0,1}^l;
   if(x = rstar) { bad = true; }
   if (!in_dom(x, LG)) {
     LG[x] = g; 
   }
   return LG[x];
 }

 and Main = {
   var m0, m1 : plaintext;
   var b, b' : bool;
   var st : state;
   (pk, sk) = KG();
   rstar = {0,1}^k;
   bad = false;
   LG = empty_map;
   cdef = false;
   q = 0;
   (m0, m1, st) = A1();
   b = {0,1};
   if (!in_dom(rstar, LG)) {
     gstar = {0,1}^l;
     LG[rstar] = gstar;
   }
   else {
     bad = true;
     gstar = LG[rstar];
   }
   cstar = f(pk, (rstar, gstar ^^ (b ? m0 : m1)));
   cdef = true;
   b' = A2(st, cstar);
   return (b = b');
 }.

prover "alt-ergo".
unset all.

equiv CCA_G1 : CCA.Main ~ G1.Main : true ==> ={res}.
proof.
 inline{1} Enc, G; derandomize.
 call (={pk,sk,LG,cstar,cdef,q}); wp.
 auto (={pk,sk,LG,cdef,q} && !cdef{2}).
 swap{1} 2 1; trivial.
save.

claim Pr_CCA_G1 : CCA.Main[res] = G1.Main[res] using CCA_G1.


(*
** Game G2:
** Replace inlined G(rstar) by a random sampling in Main
*)
game G2 = G1
 where Main = {
   var m0, m1 : plaintext;
   var b, b' : bool;
   var st : state;
   (pk, sk) = KG();
   rstar = {0,1}^k;
   bad = false;
   LG = empty_map;
   cdef = false;
   q = 0;
   (m0, m1, st) = A1();
   b = {0,1};
   gstar = {0,1}^l;
   if (in_dom(rstar, LG)) { bad = true; }
   cstar = f(pk, (rstar, gstar ^^ (b ? m0 : m1)));
   cdef = true;
   b' = A2(st, cstar);
   return (b = b');
 }.

set eqe_update_diff, eqe_update_same_L, eqe_update_same_R.

equiv G1_G2 : G1.Main ~ G2.Main : true ==> ={bad} && (!bad{1} => ={res}).
proof.
 call upto (bad) with 
  (={pk,sk,cstar,rstar,gstar,cdef,q} &&
   (bad{1} <=> in_dom(rstar{2}, LG{2})) && eq_except(LG{1}, LG{2}, rstar{1})).
 derandomize; wp.
 call upto (bad) with 
  (={pk,sk,LG,rstar,cdef,q} && !cdef{1} && (bad{1} <=> in_dom(rstar{2}, LG{2}))).
 trivial.
save.

unset eqe_update_diff, eqe_update_same_L, eqe_update_same_R.

claim Pr_G1_G2 : | G1.Main[res] - G2.Main[res] | <= G2.Main[bad]
using G1_G2.


(*
** Game G3:
** Use optimistic sampling to sample sstar instead of gstar, where
**
** G2: gstar = {0,1}^l; sstar = gstar ^^ mb; cstar = f(rstar, sstar)
** G3: sstar = {0,1}^k; gstar = sstar ^^ mb; cstar = f(rstar, sstar)
**
** Remove dependency of b' from b by eliminating gstar as dead-code
** and postponing sampling b
*)
game G3 = G2
 var sstar : bitstring{l}

 where Main = {
   var m0, m1 : plaintext;
   var b, b' : bool;
   var st : state;
   (pk, sk) = KG();
   rstar = {0,1}^k;
   bad = false;
   LG = empty_map;
   cdef = false;
   q = 0;
   (m0, m1, st) = A1();
   if (in_dom(rstar, LG)) { bad = true; }
   sstar = {0,1}^l;
   cstar = f(pk, (rstar, sstar));
   cdef = true;
   b' = A2(st, cstar);
   b = {0,1};
   return (b = b');
 }.

set xor_l_cancel, xor_l_zero_r, xor_l_assoc.

equiv G2_G3 : G2.Main ~ G3.Main : true ==> ={bad,res}.
proof.
 swap{2} 13 -5.
 call (={pk,sk,LG,rstar,cstar,cdef,q,bad}); wp.
 rnd (sstar ^^ (b ? m0 : m1){2}); wp; rnd.
 call (={pk,sk,LG,rstar,cdef,q,bad} && !cdef{1}).
 derandomize; trivial.
save.

unset xor_l_cancel, xor_l_zero_r, xor_l_assoc.

claim Pr_G2_G3  : G2.Main[res] = G3.Main[res] using G2_G3.

claim Pr_G2_G3' : G2.Main[bad] = G3.Main[bad] using G2_G3.

claim Pr_G3     : G3.Main[res] = 1%r / 2%r compute.


(*
** Game G4:
** Introduce LG' to store implicitly-defined values of G(r)
** Inline calls to G in Dec
** Apply optimistic-sampling to sample m rather than LG'[r] in Dec
*)
game G4 = G3
 var LG' : (bitstring{k}, bitstring{l}) map

 where G = {
   var g : bitstring{l} = {0,1}^l;
   if (!in_dom(x, LG)) { 
     if (!in_dom(x, LG')) {
       LG[x] = g;
     }
     else {
       LG[x] = LG'[x];
     }
   }
   return LG[x];
 }

 and Dec = {
   var r' : bitstring{k} option;
   var c' : (bitstring{k} * bitstring{l}) option;
   var r  : bitstring{k};
   var g, s, t, m : bitstring{l};
   if (q < qD && (!cdef || c <> cstar)) {
     q = q + 1;
     r' = find_sie_fst(pk, c, LG);
     if (r' <> None) {
       r = proj(r');
       s = proj(sie(pk, c, r)); (* c = f(r, s) *)
       g = LG[r];
       m = g ^^ s;
     }
     else {
       r' = find_sie_fst(pk, c, LG');
       if (r' <> None) {
         r = proj(r');
         s = proj(sie(pk, c, r)); (* c = f(r, s) *)
         g = LG'[r];
         m = g ^^ s;
       }
       else {
         if (cdef && cie(pk, c, cstar) <> None) {
           (r, s, t) = proj(cie(pk, c, cstar));  
           (* c = f(r, s) && cstar = f(r, t) *)
           g = {0,1}^l;
           LG[r] = g;
           m = g ^^ s;
        }
        else {
          (r, s) = finv(sk, c);
          m = {0,1}^l;
          LG'[r] = m ^^ s;
         }
       }
     }
   }
   else {
     m = zero_l;
   }
   return m; 
 }

 and Main = {
   var m0, m1 : plaintext;
   var b' : bool;
   var st : state;
   (pk, sk) = KG();
   rstar = {0,1}^k;
   sstar = {0,1}^l;
   cstar = f(pk, (rstar, sstar));
   LG = empty_map;
   LG' = empty_map;
   cdef = false;
   q = 0;
   (m0, m1, st) = A1();
   cdef = true;
   b' = A2(st, cstar);
   return true;
 }.

set find_sie_fst_correct, find_sie_fst_complete, sie_find_sie_fst,
  xor_l_cancel, xor_l_zero_r, xor_l_assoc,
  cie_spec', cie_spec, finv_l, finv_r.

equiv G3_G4_Dec : G3.Dec ~ G4.Dec :
 (={pk,sk,rstar,sstar,cstar,cdef,q} &&
  (key_pair(pk, sk) && cstar = f(pk, (rstar,sstar))){2} &&
 (bad{1} <=>
  (in_dom(fst(finv(sk, cstar)), LG) || in_dom(fst(finv(sk, cstar)), LG')){2}) &&
 (forall (x:bitstring{k}),
   in_dom(x, LG{2}) => in_dom(x, LG{1}) && LG{1}[x] = LG{2}[x]) &&
 (forall (x:bitstring{k}),
   !in_dom(x, LG{2}) => in_dom(x, LG{1}) =>  
   in_dom(x, LG'{2}) && LG{1}[x] = LG'{2}[x]) &&
 (forall (x:bitstring{k}),
   !in_dom(x, LG{1}) => !in_dom(x, LG{2}) && !in_dom(x, LG'{2}))).
proof.
 if; [ | trivial].
 inline G.
 case{2}: find_sie_fst(pk,c,LG) <> None.
 condf{1} at 6; [ trivial | ].
 condt{2} last; [ trivial | ].
 derandomize; wp; trivial.
 condf{2} last; [ trivial | ].
 case{2}: find_sie_fst(pk,c,LG') <> None.
 condt{2} last; [ trivial | ].
 condf{1} at 6; [ trivial| ].
 derandomize; wp; trivial.
 condf{2} last; [ trivial | ].
 condt{1} at 6; [ trivial | ].
 case{1}: cdef && cie(pk,c, cstar) <> None.
 condt{1} at 5; [ trivial | ].
 condt{2} last; [ trivial | ].
 derandomize; trivial.
 derandomize; wp. rnd (m_0 ^^ snd(finv(sk,c){2})); trivial.
 unset xor_l_assoc.
 trivial.
save.

equiv G3_G4_Dec : G3.Dec ~ G4.Dec :
 (={pk,sk,rstar,sstar,cdef,q} && !cdef{1} &&
  (key_pair(pk, sk){1}) && (cstar = f(pk, (rstar,sstar))){2} &&
 (bad{1} <=>
  (in_dom(fst(finv(sk, cstar)), LG) || in_dom(fst(finv(sk, cstar)), LG')){2}) &&
 (forall (x:bitstring{k}),
   in_dom(x, LG{2}) => in_dom(x, LG{1}) && LG{1}[x] = LG{2}[x]) &&
 (forall (x:bitstring{k}),
   !in_dom(x, LG{2}) => in_dom(x, LG{1}) =>  
   in_dom(x, LG'{2}) && LG{1}[x] = LG'{2}[x]) &&
 (forall (x:bitstring{k}),
   !in_dom(x, LG{1}) => !in_dom(x, LG{2}) && !in_dom(x, LG'{2}))).
proof.
 if; [ | trivial].
 inline G.
 case{2}: find_sie_fst(pk,c,LG) <> None.
 condf{1} at 6; [ trivial | ].
 condt{2} last; [ trivial | ].
 derandomize; wp; trivial.
 condf{2} last; [ trivial | ].
 case{2}: find_sie_fst(pk,c,LG') <> None.
 condt{2} last; [ trivial | ].
 condf{1} at 6; [ trivial | ].
 derandomize; wp; trivial.
 condf{2} last; [ trivial | ].
 condt{1} at 6; [ trivial | ].
 case{1}: cdef && cie(pk,c,cstar) <> None.
 condt{1} at 5; [ trivial | ].
 condt{2} last; [ trivial | ].
 derandomize; trivial.
 set xor_l_assoc.
 derandomize; wp; rnd (m_0 ^^ snd(finv(sk,c){2})); trivial.
 unset xor_l_assoc.
 trivial.
save.

unset find_sie_fst_correct, find_sie_fst_complete, sie_find_sie_fst,
  xor_l_cancel, xor_l_zero_r, xor_l_assoc, cie_spec', cie_spec.

equiv G3_G4 : G3.Main ~ G4.Main : true ==> 
 (bad{1} <=> 
  (in_dom(fst(finv(sk, cstar)), LG) || in_dom(fst(finv(sk, cstar)), LG')){2}).
 app 1 1 ={pk,sk} && key_pair(pk,sk){1}.
 derandomize; wp; apply: KG(); trivial.
 swap{1} -11; swap{1} 9 -6.
 call
  (={pk,sk,rstar,sstar,cstar,cdef,q} && 
   (key_pair(pk, sk){1}) && (cstar = f(pk, (rstar,sstar))){2} &&
  (bad{1} <=>
    (in_dom(fst(finv(sk, cstar)), LG) || in_dom(fst(finv(sk, cstar)), LG')){2}) &&
  (forall (x:bitstring{k}),
    in_dom(x, LG{2}) => in_dom(x, LG{1}) && LG{1}[x] = LG{2}[x]) &&
  (forall (x:bitstring{k}),
    !in_dom(x, LG{2}) => in_dom(x, LG{1}) =>  
    in_dom(x, LG'{2}) && LG{1}[x] = LG'{2}[x]) &&
  (forall (x:bitstring{k}),
    !in_dom(x, LG{1}) => !in_dom(x, LG{2}) && !in_dom(x, LG'{2}))).
 wp.
 call
  (={pk,sk,rstar,sstar,cdef,q} && !cdef{1} &&
   (key_pair(pk, sk){1}) && (cstar = f(pk, (rstar,sstar))){2} &&
  (bad{1} <=>
    (in_dom(fst(finv(sk, cstar)), LG) || in_dom(fst(finv(sk, cstar)), LG')){2}) &&
  (forall (x:bitstring{k}),
    in_dom(x, LG{2}) => in_dom(x, LG{1}) && LG{1}[x] = LG{2}[x]) &&
  (forall (x:bitstring{k}),
    !in_dom(x, LG{2}) => in_dom(x, LG{1}) =>  
    in_dom(x, LG'{2}) && LG{1}[x] = LG'{2}[x]) &&
  (forall (x:bitstring{k}),
    !in_dom(x, LG{1}) => !in_dom(x, LG{2}) && !in_dom(x, LG'{2}))).
 trivial.
save. 

unset finv_l, finv_r.

claim Pr_G3_G4 : 
  G3.Main[bad] =
  G4.Main[in_dom(fst(finv(sk,cstar)), LG) || in_dom(fst(finv(sk,cstar)), LG')]
using G3_G4.


(*
** Game G5:
** Introduce LD
** Ciphertexts that implicitly-define values of G(r) are stored in LD
** Remove finv from Dec
*)
game G5 = G4
 var LD : (bitstring{k} * bitstring{l}, bitstring{l}) map

 where G = {
   var c : ciphertext option;
   var g : bitstring{l} = {0,1}^l;
   if (!in_dom(x, LG)) { 
     c = find_sie_snd(pk, x, LD);
     if (c = None) {
       LG[x] = g;
     }
     else {
       LG[x] = LD[proj(c)] ^^ proj(sie(pk, proj(c), x));
     }
   }
   return LG[x];
 }

 and Dec = {
   var r' : bitstring{k} option;
   var c' : (bitstring{k} * bitstring{l}) option;
   var r  : bitstring{k};
   var g, s, t, m : bitstring{l};
   if (q < qD && (!cdef || c <> cstar)) {
     q = q + 1;
     r' = find_sie_fst(pk, c, LG);
     if (r' <> None) {
       r = proj(r');
       s = proj(sie(pk, c, r)); (* c = f(r, s) *)
       g = LG[r];
       m = g ^^ s;
     }
     else {
       if (in_dom(c, LD)) {
         m = LD[c];
       }
       else {
         c' = find_cie(pk, c, LD);
         if (c' <> None) {
           (r, s, t) = proj(cie(pk, c, proj(c'))); 
           (* c = f(r, s) && c' = f(r, t) *)
           g = LD[proj(c')] ^^ s;
           m = g ^^ t;
         }
         else {
           if (cdef && cie(pk, c, cstar) <> None) {
             (r, s, t) = proj(cie(pk, c, cstar)); 
             (* c = f(r, s) && cstar = f(r, t) *)
             g = {0,1}^l;
             LG[r] = g;
             m = g ^^ s;
           }
           else {
             m = {0,1}^l;
             LD[c] = m;
           }
         }
       }
     }
   }
   else {
     m = zero_l;
   }
   return m; 
 }

 and Main = {
   var m0, m1 : plaintext;
   var b' : bool;
   var st : state;
   (pk, sk) = KG();
   rstar = {0,1}^k;
   sstar = {0,1}^l;
   cstar = f(pk, (rstar, sstar));
   bad = false;
   LG = empty_map;
   LD = empty_map;
   cdef = false;
   q = 0;
   (m0, m1, st) = A1();
   cdef = true;
   b' = A2(st, cstar);
   return true;
 }.

set find_sie_fst_correct, find_sie_fst_complete, sie_find_sie_fst, xor_2.

equiv G4_G5_Dec : G4.Dec ~ G5.Dec : 
 (={pk,sk,LG,cstar,cdef,q} && key_pair(pk, sk){1} &&
  (forall (x:ciphertext),
    find_sie_fst(pk{1}, x, LG'{1}) = None <=> 
    find_cie(pk{2}, x, LD{2}) = None && !in_dom(x, LD{2})) &&
  (forall (r:bitstring{k}),
    !in_dom(r,LG'{1}) <=> find_sie_snd(pk{2}, r, LD{2}) = None) &&
  (forall (x:ciphertext),
   let r,s = finv(sk{1}, x) in 
     (in_dom(x, LD{2}) => in_dom(r, LG'{1}) && LG'{1}[r] = s ^^ LD{2}[x]))).
proof.
 if; [ trivial | ].
 case{1}: find_sie_fst(pk, c, LG) <> None.
 condt last; trivial.
 condf last; [ trivial | trivial | ].
 case{2}: in_dom(c, LD).
 condt{2} last; [ trivial | ].
 condt{1} last; [ trivial | ].
 trivial.
 condf{2} last; [ trivial | ].
 case{1}: find_sie_fst(pk, c, LG') <> None.
 condt{1} last; [ trivial | ].
 condt{2} last; [ trivial | ].
 trivial.
 app 0 0
  (={c,pk,sk,LG,cstar,cdef} && key_pair(pk,sk){1} &&
   (forall (x:ciphertext),
      find_sie_fst(pk,x,LG'){1} = None <=> 
      find_cie(pk,x,LD){2} = None && !in_dom(x, LD{2})) &&
   (forall (x: ciphertext),
     let r,s = finv(sk{1}, x) in 
     in_dom(x,LD{2}) => in_dom(r,LG'{1}) && LG'{1}[r] = s ^^ LD{2}[x]) &&
   (cdef{2} <> true || c{2} <> cstar{2}) &&
   !in_dom(c,LD){2} &&
   let c' = find_cie(pk, c, LD){2} in
     c' <> None && in_dom(proj(c'), LD{2})).
 set find_cie_correct.
 trivial.
 unset find_cie_correct. 
 set sie_find_sie_fst, cie_find_cie, find_cie_correct',
     cie_spec, finv_l, finv_r, xor_l_cancel, xor_l_zero_r, xor_l_assoc.
 app 0 0 (
  ={c,pk,sk,LG,cstar,cdef} && key_pair (pk{1},sk{1}) &&
  find_sie_fst(pk,c,LG'){1} <> None &&
  (forall (x_0:ciphertext),
  let r,s = finv(sk{1},x_0) in 
    in_dom(x_0,LD{2}) => LG'{1}[r] = s ^^ LD{2}[x_0]) &&
  let c' = find_cie(pk, c, LD){2} in
  let r', s, t = proj(cie(pk, c, proj(c'))){2} in
  let r = proj(find_sie_fst(pk, c, LG')){1} in
    c' <> None &&
    r = r' &&
    c{1} = f(pk, (r, s)){1} &&
    proj(c') = f(pk, (r, t)){2} && 
    in_dom(proj(c'), LD{2}) &&
    r = fst(finv(sk{1}, proj(c')))).
 trivial.
 app 0 0 (
   let c' = find_cie(pk, c, LD){2} in
   let _, s, t = proj(cie(pk, c, proj(c'))){2} in
   let r = proj(find_sie_fst(pk, c, LG')){1} in
     sie(pk,c,r){1} = Some(s) &&
     LG'{1}[r] = t ^^ LD{2}[proj(c')]).
 trivial.
 trivial.

 condf{1} last; [ trivial | ].
 condf{2} last; [ trivial | ].
 case{1}: cdef && cie(pk, c, cstar) <> None.
 condt{1} last; [ trivial | ].
 condt{2} last; [ trivial | ].
 trivial.
 condf{1} last; [ trivial | ].
 condf{2} last; [ trivial | ].
 set find_sie_fst_upd, find_sie_snd_upd, find_cie_upd.
 trivial.
 trivial.
save.

timeout 5.

equiv G4_G5_G : G4.G ~ G5.G : 
  (={pk,sk,LG,cstar,cdef,q} && key_pair(pk, sk){1} &&
  (forall (x:ciphertext),
    find_sie_fst(pk{1}, x, LG'{1}) = None => 
    find_cie(pk{2}, x, LD{2}) = None && !in_dom(x, LD{2})) &&
  (forall (r:bitstring{k}),
    !in_dom(r,LG'{1}) <=> find_sie_snd(pk{2}, r, LD{2}) = None) &&
  (forall (x:ciphertext),
    let r,s = finv(sk{1}, x) in 
    in_dom(x, LD{2}) => in_dom(r, LG'{1}) && LG'{1}[r] = s ^^ LD{2}[x])).
proof.
 case{1}: !in_dom(x, LG).
 condt last; [ trivial | trivial | ].
 case{1}: !in_dom(x, LG').
 condt{1} last; [ trivial | ].
 condt{2} last; [ trivial | ].
 trivial.
 condf{1} last; [ trivial | ].
 condf{2} last; [ trivial | ].
 unset xor_2.
 set find_sie_snd_complete, xor_l_comm.
 trivial.
 app 0 0 (
   ={x,pk,sk,LG} && key_pair(pk,sk){1} &&
   let c' = find_sie_snd(pk,x,LD){2} in
     c' <> None && in_dom (x,LG'){1} &&
     LG'{1}[fst(finv(sk{1},proj(c')))] = 
     snd(finv(sk{1},proj(c'))) ^^ LD{2}[proj(c')]); trivial.
 condf last; trivial.
save.

set find_sie_snd_empty, find_cie_empty.

equiv G4_G5 : G4.Main ~ G5.Main : true ==> 
 (in_dom(fst(finv(sk,cstar)), LG) || in_dom(fst(finv(sk,cstar)), LG')){1} =>
 (in_dom(fst(finv(sk,cstar)), LG) || 
  find_sie_snd(pk,fst(finv(sk,cstar)), LD) <> None){2}.
proof.
 app 1 1 ={pk,sk} && key_pair(pk{1},sk{1}).
 derandomize; wp; apply: KG(); trivial.
 auto 
  (={pk,sk,LG,cstar,cdef,q} && key_pair(pk,sk){1} &&
  (forall (x:ciphertext),
    find_sie_fst(pk{1},x,LG'{1}) = None <=> 
    find_cie(pk{2},x,LD{2}) = None && !in_dom(x,LD{2})) &&
  (forall (r:bitstring{k}),
    !in_dom(r,LG'{1}) <=> find_sie_snd(pk{2}, r, LD{2}) = None) &&
  (forall (x:ciphertext),
    let r,s = finv(sk{1},x) in 
    in_dom(x, LD{2}) => in_dom(r, LG'{1}) && LG'{1}[r] = s ^^ LD{2}[x])).
 trivial.
save.

claim Pr_G4_G5 : 
  G4.Main[in_dom(fst(finv(sk,cstar)), LG) || in_dom(fst(finv(sk,cstar)), LG')] <=
  G5.Main[in_dom(fst(finv(sk,cstar)), LG) || 
          find_sie_snd(pk,fst(finv(sk,cstar)), LD) <> None] 
using G4_G5.


game OW = {
 var pk    : pkey
 var sk    : skey
 var LG    : (bitstring{k}, bitstring{l}) map
 var LD    : (bitstring{k} * bitstring{l}, bitstring{l}) map
 var cstar : ciphertext
 var cdef  : bool
 var q     : int

 fun G(x:bitstring{k}) : bitstring{l} = {
   var c : ciphertext option;
   var g : bitstring{l} = {0,1}^l;
   if (!in_dom(x, LG)) { 
     c = find_sie_snd(pk, x, LD); (* t_sie * qD *)
     if (c = None) {
       LG[x] = g;
     }
     else {
       LG[x] = LD[proj(c)] ^^ proj(sie(pk,proj(c), x));
     }
   }
   return LG[x];
 }

 fun Dec(c:ciphertext) : plaintext = {
   var r' : bitstring{k} option;
   var c' : (bitstring{k} * bitstring{l}) option;
   var r  : bitstring{k};
   var g, s, t, m : bitstring{l};
   if (q < qD && (!cdef || c <> cstar)) {
     q = q + 1;
     r' = find_sie_fst(pk, c, LG); (* t_sie * qG *)
     if (r' <> None) {
       r = proj(r');
       s = proj(sie(pk, c, r));
       g = LG[r];
       m = g ^^ s;
     }
     else {
       if (in_dom(c, LD)) {
         m = LD[c];
       }
       else {
         c' = find_cie(pk, c, LD); (* t_cie * qD *)
         if (c' <> None) {
           (r, s, t) = proj(cie(pk, c, proj(c')));
           g = LD[proj(c')] ^^ s;
           m = g ^^ t;
         }
         else {
           if (cdef && cie(pk, c, cstar) <> None) { (* t_cie *)
             (r, s, t) = proj(cie(pk, c, cstar));
             g = {0,1}^l;
             LG[r] = g;
             m = g ^^ s;
           }
           else {
             m = {0,1}^l;
             LD[c] = m;
           }
         }
       }
     }
   }
   else {
     m = zero_l;
   }
   return m; 
 }

 abs A1 = A1 {G, Dec}
 abs A2 = A2 {G, Dec}

 fun B(z:bitstring{k} * bitstring{l}) : bitstring{k} * bitstring{l} = {
   var m0, m1 : plaintext;
   var b' : bool;
   var r' : bitstring{k} option;
   var r : bitstring{k};
   var s, t : bitstring{l};
   var c : ciphertext option;
   var st : state;
   LG = empty_map;
   LD = empty_map;
   cstar = z;
   cdef = false;
   q = 0;
   (m0, m1, st) = A1();
   cdef = true;
   b' = A2(st, cstar);  
   r' = find_sie_fst(pk, cstar, LG); (* t_sie * qG *)
   if (r' <> None) {
     r = proj(r');
     s = proj(sie(pk, cstar, r));
   }
   else 
   {
     c = find_cie(pk, cstar, LD); (* t_cie * qD *)
     if (c <> None) {
       (r, s, t) = proj(cie(pk, cstar, proj(c)));
     }
     else {
       r = zero_k;
       s = zero_l;
     }
   }
   return (r, s);
 }

 var xstar : bitstring{k}
 var ystar : bitstring{l}

 fun Main() : bool = {
   var x : bitstring{k};
   var y : bitstring{l};
   (pk, sk) = KG();
   xstar = {0,1}^k;
   ystar = {0,1}^l;
   (x,y) = B(f(pk, (xstar,ystar)));
   return (f(pk, (x,y)) = f(pk, (xstar,ystar)));  
 }
}.

set find_cie_find_sie_snd, find_sie_snd_cie, find_cie_correct'.

equiv G5_OW : G5.Main ~ OW.Main : true ==>
 in_dom(fst(finv(sk{1},cstar{1})), LG{1}) ||
 find_sie_snd(pk{1},fst(finv(sk{1},cstar{1})), LD{1}) <> None => 
 !in_dom(cstar{2}, LD{2}) => res{2}.
proof.
 app 1 1 ={pk,sk} && key_pair(pk{1},sk{1}).
 derandomize; wp; apply: KG(); trivial.
 inline B; derandomize.
 app 15 13 (={pk,sk,LG,LD,cstar,cdef,q} && key_pair(pk,sk){1} && 
   (cstar = f(pk,(xstar,ystar))){2} ).
 auto (={pk,sk,LG,LD,cstar,cdef,q} && key_pair(pk,sk){1}); trivial.
 trivial.
save.

unset find_cie_find_sie_snd, find_sie_snd_cie, find_cie_correct'.

claim Pr_G5_OW' : 
  G5.Main[in_dom(fst(finv(sk,cstar)), LG) ||
          find_sie_snd(pk,fst(finv(sk,cstar)), LD) <> None] <= 
  OW.Main[res || in_dom(cstar, LD)]
using G5_OW.

claim Pr_OW : 
  OW.Main[res || in_dom(cstar,LD)] <= OW.Main[res] + OW.Main[in_dom(cstar,LD)]
compute.

claim Pr_G5_OW : 
  G5.Main[in_dom(fst(finv(sk,cstar)), LG) ||
          find_sie_snd(pk,fst(finv(sk,cstar)), LD) <> None] <= 
  OW.Main[res] + OW.Main[in_dom(cstar, LD)].

claim CCA_OW : 
  | CCA.Main[res] - 1%r / 2%r | <= OW.Main[res] + OW.Main[in_dom(cstar, LD)].

(*
** Follows a rather technical sequence of games to bound 
** OW.Main[in_dom(cstar,LD)]
*)

game OW1 = {
 var pk    : pkey
 var sk    : skey
 var LG    : (bitstring{k}, bitstring{l}) map
 var LD    : (bitstring{k} * bitstring{l}, bitstring{l}) map
 var LC    : ciphertext list
 var cstar : ciphertext
 var cdef  : bool
 var q     : int

 fun G(x:bitstring{k}) : bitstring{l} = {
   var c : ciphertext option;
   var g : bitstring{l} = {0,1}^l;
   if (!in_dom(x, LG)) { 
     c = find_sie_snd(pk, x, LD); (* t_sie * qD *)
     if (c = None) {
       LG[x] = g;
     }
     else {
       LG[x] = LD[proj(c)] ^^ proj(sie(pk, proj(c), x));
     }
   }
   return LG[x];
 }

 fun Dec1(c:ciphertext) : plaintext = {
   var r' : bitstring{k} option;
   var c' : (bitstring{k} * bitstring{l}) option;
   var r  : bitstring{k};
   var g, s, t, m : bitstring{l};
   if (q < qD) {
     q = q + 1;
     r' = find_sie_fst(pk, c, LG); (* t_sie * qG *)
     if (r' <> None) {
       r = proj(r');
       s = proj(sie(pk, c, r));
       g = LG[r];
       m = g ^^ s;
     }
     else {
       if (in_dom(c, LD)) {
         m = LD[c];
       }
       else {
         c' = find_cie(pk, c, LD); (* t_cie * qD *)
         if (c' <> None) {
           (r, s, t) = proj(cie(pk, c, proj(c')));
           g = LD[proj(c')] ^^ s;
           m = g ^^ t;
         }
         else {
           m = {0,1}^l;
           LD[c] = m;
           LC = c :: LC;
         }
       }
     }
   }
   else {
     m = zero_l;
   }
   return m; 
 }

 fun Dec2(c:ciphertext) : plaintext = {
   var r' : bitstring{k} option;
   var c' : (bitstring{k} * bitstring{l}) option;
   var r  : bitstring{k};
   var g, s, t, m : bitstring{l};
   if (q < qD && (!cdef || c <> cstar)) {
     q = q + 1;
     r' = find_sie_fst(pk, c, LG); (* t_sie * qG *)
     if (r' <> None) {
       r = proj(r');
       s = proj(sie(pk, c, r));
       g = LG[r];
       m = g ^^ s;
     }
     else {
       if (in_dom(c, LD)) {
         m = LD[c];
       }
       else {
         c' = find_cie(pk, c, LD); (* t_cie * qD *)
         if (c' <> None) {
           (r, s, t) = proj(cie(pk, c, proj(c')));
           g = LD[proj(c')] ^^ s;
           m = g ^^ t;
         }
         else {
           if (cdef && cie(pk, c, cstar) <> None) { (* t_cie *)
             (r, s, t) = proj(cie(pk, c, cstar));
             g = {0,1}^l;
             LG[r] = g;
             m = g ^^ s;
           }
           else {
             m = {0,1}^l;
             LD[c] = m;
           }
         }
       }
     }
   }
   else {
     m = zero_l;
   }
   return m; 
 }

 abs A1 = A1 {G, Dec1}
 abs A2 = A2 {G, Dec2}

 var zstar : bitstring{k} * bitstring{l}

 fun Main() : bool = {
   var m0, m1 : plaintext;
   var b' : bool;
   var st : state;
   (pk, sk) = KG();
   LG = empty_map;
   LD = empty_map;
   LC = [];
   cdef = false;
   q = 0;
   (m0, m1, st) = A1();
   zstar = ({0,1}^k, {0,1}^l);
   cstar = f(pk, zstar);
   cdef = true;
   b' = A2(st, cstar);  
   return true;
 }
}.

equiv OW_OW1 : OW.Main ~ OW1.Main : 
 true ==> in_dom(cstar, LD){1} => mem(cstar{2}, LC{2}).
proof.
 inline B; derandomize; wp.
 swap{2} [11-12] -6.
 call (={pk,sk,LG,LD,cstar,cdef,q} && cdef{1} &&
   (in_dom(cstar, LD){1} => mem(cstar{2}, LC{2}))).
 wp.
 call (={pk,sk,LG,LD,cstar,cdef,q} && !cdef{1} &&
   (in_dom(cstar, LD){1} => mem(cstar{2}, LC{2}))).
 trivial.
save.

claim Pr_OW_OW1 : OW.Main[in_dom(cstar, LD)] <= OW1.Main[mem(cstar, LC)]
using OW_OW1.

op msb  : bitstring{k+l} -> bitstring{k}.
op lsb  : bitstring{k+l} -> bitstring{l}.
op [++] : (bitstring{k}, bitstring{l}) -> bitstring{k+l} as app_kl.

axiom app_inj : forall (z:bitstring{k+l}), (msb(z) ++ lsb(z)) = z.

axiom rnd_pair() : 
  xy1 = ({0,1}^k, {0,1}^l) ~ xy2 = {0,1}^(k+l) : 
  true ==> xy1 = (msb(xy2), lsb(xy2)).

game OW2 = OW1 
 var zstar' : bitstring{k+l}

 where Main = {
   var m0, m1 : plaintext;
   var b' : bool;
   var st : state;
   (pk, sk) = KG();
   LG = empty_map;
   LD = empty_map;
   LC = [];
   cdef = false;
   q = 0;
   (m0, m1, st) = A1();
   zstar' = {0,1}^(k+l);
   cstar = f(pk, (msb(zstar'), lsb(zstar')));
   cdef = true;
   b' = A2(st, cstar);  
   return true;
 }.

equiv OW1_OW2 : OW1.Main ~ OW2.Main : true ==> ={cstar, LC}.
proof.
 app 7 7 (={pk,sk,st,LG,LD,LC,cdef,q}).
 call (={pk,sk,LG,LD,LC,cdef,q}). 
 derandomize; trivial.
 app 2 2 (={pk,sk,st,LG,LD,LC,cdef,q,cstar}).
 wp; apply: rnd_pair(); trivial.
 auto (={pk,sk,LG,LD,LC,cdef,q,cstar}).
save. 

claim Pr_OW1_OW2 : OW1.Main[mem(cstar, LC)] = OW2.Main[mem(cstar, LC)]
using OW1_OW2.


game OW3 = OW2 
 var LZ : bitstring{k+l} list

 where Dec1 = {
   var r' : bitstring{k} option;
   var c' : (bitstring{k} * bitstring{l}) option;
   var r  : bitstring{k};
   var g, s, t, m : bitstring{l};
   if (q < qD) {
     q = q + 1;
     r' = find_sie_fst(pk, c, LG); (* t_sie * qG *)
     if (r' <> None) {
       r = proj(r');
       s = proj(sie(pk, c, r));
       g = LG[r];
       m = g ^^ s;
     }
     else {
       if (in_dom(c, LD)) {
         m = LD[c];
       }
       else {
         c' = find_cie(pk, c, LD); (* t_cie * qD *)
         if (c' <> None) {
           (r, s, t) = proj(cie(pk, c, proj(c')));
           g = LD[proj(c')] ^^ s;
           m = g ^^ t;
         }
         else {
           m = {0,1}^l;
           LD[c] = m;
           LZ = (fst(finv(sk, c)) ++ snd(finv(sk, c))) :: LZ;
         }
       }
     }
   }
   else {
     m = zero_l;
   }
   return m; 
 }

 and Main = {
   var m0, m1 : plaintext;
   var b' : bool;
   var st : state;
   (pk, sk) = KG();
   LG = empty_map;
   LD = empty_map;
   LZ = [];
   cdef = false;
   q = 0;
   (m0, m1, st) = A1();
   zstar' = {0,1}^(k+l);
   cstar = f(pk, (msb(zstar'), lsb(zstar')));
   cdef = true;
   b' = A2(st, cstar);  
   return true;
 }.

set qD_pos, k_pos, l_pos.

equiv OW2_OW3 : OW2.Main ~ OW3.Main : 
  true ==> 
  (length(LZ{2}) <= qD) &&
  (mem(cstar{1}, LC{1}) => mem(msb(zstar'{2}) ++ lsb(zstar'{2}), LZ{2})).
proof.
 app 1 1 ={pk,sk} && key_pair(pk{1},sk{1}).
 derandomize; wp; apply: KG(); trivial.
 call (={pk,sk,LG,LD,cstar,cdef,q,zstar'} && key_pair(pk,sk){1} && cdef{1} &&
  cstar{1} = f(pk{1},(msb(zstar'{1}),lsb (zstar'{1}))) &&
  length(LZ{2}) <= q{2} && q{2} <= qD &&
  (mem(cstar{1}, LC{1}) => mem(zstar'{2}, LZ{2}))).
 wp; rnd.
 call (={pk,sk,LG,LD,cdef,q} && key_pair(pk,sk){1} && !cdef{1} &&
  length(LZ{2}) <= q{2} && q{2} <= qD &&
  (forall (z:bitstring{k+l}),
    mem(f(pk{1}, (msb(z), lsb(z))), LC{1}) => mem(z, LZ{2}))).
 trivial. 
save.

claim Pr_OW2_OW3 :
  OW2.Main[mem(cstar, LC)] <= OW3.Main[mem(zstar', LZ) && length(LZ) <= qD]
using OW2_OW3.

claim Pr_OW3 :
  OW3.Main[mem(zstar', LZ) && length(LZ) <= qD] <= qD%r / (2 ^ (k+l))%r
compute.

claim conclusion : 
  | CCA.Main[res] - 1%r / 2%r | <= OW.Main[res] + qD%r / (2 ^ (k+l))%r.
