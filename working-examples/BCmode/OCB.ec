checkproof.
include "array.ec".
checkproof.

(* Instantiation of the signature *)

cnst n : int.

axiom n_pos : 0 <= n.

type block = bitstring{n}.  

type nonce = block.

op of_int : int -> block.

op gen_nonce (c:int, nc:block) = of_int(c).
(* [gen_nonce(i,b)] generate a new nonce. [i] is a counter, it will be 
different for each call to [gen_nonce]. [b] is a random block *)

type skey. (* type of secret keys used in the block cipher *)
type okey = int.

pop gen_skey : () -> skey.
op gen_okey () = 0.
(* [gen_skey()] is a random operator generating a new [skey] 
   [gen_okey()] is a random operator generating a new [okey] *)

type secret = block list. (* type of secrets used in the scheme *)

op init_global_secret () = [].
cnst sg : int = 1.
lemma sg_pos : 0 <= sg.
op gen_global_presecret (s : secret) = bs0_n.

op init_secret (nc:nonce, ok:okey) = [].
cnst sl : int = 1.  (* number of calls to F needed to generate the secret *)
lemma sl_pos : 0 <= sl.
op gen_presecret (nc:nonce, s:secret) = nc ^^ hd(s).


type intermediate = block list.

op [*] : (block, block) -> block as mult_block.
op gamma : int -> block.


op gen (nc:nonce, s:secret, inter:intermediate) =
  let gL = hd(tl(s)) in
  let gR = hd(s) in
  let i = length(inter) in
  (gamma(i) * gL) ^^ gR.

(* [gen(nc,s,inter)] build a new block [E_|inter|] *)

op oper (b1,b2:block) = b1 ^^ b2.
op F    : (skey, block) -> block.

(** Definitions of the generic games *)
include "generic_game.ec".


game OCBCPA = {
  var p : int
  var b : bool
  var SK : skey
  var count : int
  var L : block

  fun KG () : skey = {
    var kg_sk : skey;
    kg_sk = gen_skey ();
    return (kg_sk);
  }

  fun Enc (sk : skey, m : message) : cipher = {
    var c : block array;
    var E,X,C, R, nc : block;
    var j : int;
    c = make (length (m),bs0_n);
    nc = of_int(p);
    R = F(sk,nc ^^ L);
    j = 0;
    while (j < length (m))
    {
      E = (gamma(j)*L) ^^ R;
      X = E ^^ (m ~> j);
      C = F (sk,X);
      c = c <~ (j,C);
      j = j + 1;
    }
    
    p = p + 1;
    return (nc,c);
  }

  fun LR (m0, m1 : message) : cipher = {
    var cb : cipher;
    if (length (m0) = length (m1) && p < q && count + length (m0) <= sigma)
    {
    
      cb = Enc (SK, if b then m0 else m1);
      count = count + length (m0);
    }
    else
    { 
        cb = (bs0_n,make (0,bs0_n));
    }
    return cb;
  }

  abs A = A{LR}

  fun Main () : bool = {
    var b' : bool;
    SK = KG ();
    b = {0,1};
    p = 0;
    count = 0;
    L = F(SK, bs0_n); 
    b' = A ();
    return b = b';
  }
}.

equiv OCBCPA_CPA_LR : OCBCPA.LR ~ CPA.LR : 
   (={b,count,p} && global_secret{2} = [L{1}] && fst(K{2}) = SK{1}).
 if;[ | trivial ].
 inline Enc;wp.
 while : ={j,m,c,sk} &&
               length(inter{2}) = j{2} &&
               sec{2} = [R{1};L{1}].
   trivial.
 condt{2} last ;[ trivial | ].
 condf{2} last;trivial.
save.

equiv OCBCPA_CPA : OCBCPA.Main ~ CPA.Main : true ==> ={res}.
 inline KG.
 auto (={b,count,p} && global_secret{2} = [L{1}] && fst(K{2}) = SK{1}).

 condt{2} last;[trivial | ].
 condf{2} last; trivial.
save.

game G3 = {
  var p,count : int
  var b : bool
  var L : block
  var LB : block list
  var bad: bool

  fun LR(m0, m1 : message) : cipher = {
    var cb : cipher;
    var nc:nonce;
    var Mp : message;
    var c : block array;
    var E,X,C,Rp : block;
    var j : int;

    if (length(m0) = length(m1) && p < q && count + length(m0) <= sigma) {
      Mp = b ? m0 : m1;
      c = make(length(m0), bs0_n);
      j = 0;
      nc = of_int(p);
      bad = bad || mem(nc ^^ L,LB);
      LB = (nc ^^ L) :: LB;
      Rp = {0,1}^n;
      while (j < length(m0)) {
        E = (gamma(j)*L) ^^ Rp;
        X = E ^^ (Mp ~> j);
        bad = bad || mem(X,LB);
        LB= X:: LB;
        C = {0,1}^n;
        c = c <~(j,C);
        j = j + 1;
      }
      p = p + 1;
      cb = (nc, c);      
      count = count + length(m0);
    } else {
      cb = (bs0_n,make(0,bs0_n));
    }
    return cb;
  }  

  abs A = A{LR}

  fun Main () : bool = {
    var b' : bool;
    bad = false;
    LB = [];
    b = {0,1};
    p = 0; count = 0;
    L = {0,1}^n;
    LB = [bs0_n];
    b' = A ();
    return b = b';
  }
}.

(* proved in generic_priv.ec *)
claim claim3 : | CPA.Main[res] - 1%r/2%r | <=
    | PRP0.Main[res] - PRP1.Main[res] | +  max_call%r * ((max_call - 1)%r / (2^n)%r) +
    G2.Main[bad]
admit.

equiv G2_G3_LR : G2.LR ~ G3.LR : (={p,count,b,bad,LB} && global_secret{1} = [L{2}]).
if;[wp|trivial].
while : = {j,m0,Mp,c,LB,bad} && sec{1} = [Rp{2};L{2}] && length(inter{1}) = j{1}.
 trivial.
condt{1} last;[ trivial | condf{1} last;trivial].
save.

equiv G2_G3 : G2.Main ~ G3.Main : true ==> ={bad}.
call (={p,count,b,bad,LB} && global_secret{1} = [L{2}]).
condt{1} last;[ trivial | condf{1} last;wp].
condt{1} last;[ trivial | ].
derandomize;trivial.
save.

claim Pr_G2_G3 : G2.Main[bad] = G3.Main[bad]
using G2_G3.

lemma max_call_def : max_call = 1 + sigma + q.

claim claim4 : | CPA.Main[res] - 1%r/2%r | <=
    | PRP0.Main[res] - PRP1.Main[res] | +  (1+sigma + q)%r * ((sigma+q)%r / (2^n)%r) +
    G3.Main[bad].
unset max_call_def, Pr_G2_G3, claim3.

(* We need to bound the probability of bad in G3.
   bad is set in G3 if p ^^ L is in LB or ((gamma(j)*L) ^^ Rp) ^^ Mp[j] is in LB.
   In LR, we have the following precondition:
       x in LB =>
         1/ x = 0
         2/ x = i ^^ L with i < p
         3/ x = ((gamma(j)*L) ^^ Ri) ^^ Mi[j] with i < p
   Now, bad is set before the loop if p ^^ L is in LB:
         1.1/ p ^^ L = 0 this implies L = p 
              we add p in a list Lp, we require that L is not in Lp
              the length of Lp is bounded by q
         1.2/ p ^^ L = i ^^ L, impossible since i < p
         1.3/ p ^^ L = (gamma(j) * L) ^^ Ri ^^ Mi[j] with i < p
              L ^^ gamma(j) * L = p ^^ Ri ^^ Mi[j]
              (1 ^^ gamma(j)) * L = p ^^ Ri ^^ Mi[j]
              L = (p ^^ Ri ^^ Mi[j]) * inv (1^^gamma(j)).
              this is true if gamma(j) <> 1.
              We add  (p ^^ Ri ^^ Mi[j]) * inv (1^^gamma(j)) in a list LpRiMi 
              (using the operator build_pRiMi),
              we require that L is not in LpRiMi.
   During the loop we have: 
       x in LB =>  
         1/ x = 0
         2/ x = i ^^ L with i <= p
         3/ x = ((gamma(l)*L) ^^ Ri) ^^ Mi[l] with i <= p 
         4/ x = ((gamma(l)*L) ^^ Rp) ^^ Mp[l] with l < j 
    Now, bad is set in the loop if ((gamma(j)*L) ^^ Rp) ^^ Mp[j] is in LB:
         2.1/ ((gamma(j)*L) ^^ Rp) ^^ Mp[j] = 0
               this implies Rp = (gamma(j) * L) ^^ M_p[j]
               we set bad1 if Rp is in the corresponding list (build_jLMpj)
         2.2/ ((gamma(j)*L) ^^ Rp) ^^ Mp[j] = i ^^ L with i <= p
              L = (i ^^ Rp ^^ Mp[j]) * inv (1^^gamma(j))
              this is true if gamma(j) <> 1.
              We add  (i ^^ Rp ^^ Mp[j]) * inv (1^^gamma(j)) in a list LpRpMp 
              (using the operator build_pRpMp),
              we require that L is not in LpRpMp. 
         2.3/ ((gamma(j)*L) ^^ Rp) ^^ Mp[j] = ((gamma(l)*L) ^^ Ri) ^^ Mi[l] with i < p
              Rp = (gamma(j) * L) ^^ Mp[j] ^^ (gamma(l) * L) ^^ Ri ^^ Mi[l]
              We set bad2 Rp is in the corresponding list (build_jLMplLRiMi)
         2.4/ ((gamma(j)*L) ^^ Rp) ^^ Mp[j] = ((gamma(l)*L) ^^ Rp) ^^ Mp[l] with l < j
              L = (Mp[j] ^^ Mp[k]) * (gamma(l) ^^ gamma(j))^-1
              remark: 0 <= l < j < 2^n-1 => gamma(j) <> gamma(l)
              we add (Mp[j] ^^ Mp[l]) * (gamma(l) ^^ gamma(j))^-1 in a list LMpMpjl
              using the operator build_LMpMpjl.
              we require that L is not in LMpMpjl.
*)

(** Declaration of the operators and the corresponding axiom *)

pred is_iL(x:block, p:int, L:block) = 
  exists (i:int), 0 <= i && i < p && x = of_int(i) ^^ L.

pred is_jLRM (x:block, L:block, Log:(block*message)array, p:int) =
  exists (i,j:int),
    let Ri = fst(Log~>i) in
    let Mi = snd(Log~>i) in
    0 <= i && i < p &&
    0 <= j && j < length(Mi) &&
    x = (gamma(j) * L) ^^ Ri ^^ (Mi~>j).

(* Case 1.1: trivial *) 

lemma case_1_1 : forall (L:block, p:int), of_int(p) ^^ L = bs0_n => L = of_int(p).
unset case_1_1.

(* Case 1.2 *)

axiom q_2n : q <= 2^n.

axiom of_int_inv : forall (x,y:int), 
   0 <= x => x < 2^n =>
   0 <= y => y < 2^n =>
   x <> y =>
   of_int(x) <> of_int(y).

lemma xor_inj : forall (x1,x2,y:block), x1 ^^ y = x2 ^^ y => x1 = x2.

lemma case_1_2 : forall (p:int,L:block), 
     0 <= p => p < q =>
     !is_iL(of_int (p) ^^ L,p,L).
unset case_1_2.

(* Case 1.3 *)
op inv : block -> block.
axiom inv_spec : forall (x:block), x <> bs0_n => x * inv(x) = of_int(1).
axiom mult_1 : forall (x:block), x * of_int(1) = x.
axiom mult_comm : forall (x,y:block), x * y = y * x.
axiom mult_assoc :  forall (x,y,z:block), x * (y * z) = (x * y) * z.
axiom mult_distr : forall (x,y,z:block), (y ^^ z) * x = (y * x) ^^ (z * x).

lemma case_1_3_aux1 : forall (L:block, j:int),
   L ^^ (gamma(j) * L) = (of_int(1) ^^ gamma(j)) * L.

axiom gamma_diff_1 : forall (j:int), gamma(j) <> of_int(1).

lemma gamma_diff_1' : forall (j:int), 
    (of_int(1) ^^ gamma(j)) <> bs0_n.
unset gamma_diff_1.

lemma inv_mult : forall (x,y,a,b:block),
   x <> bs0_n =>
   x * y = a ^^ b =>
   y = (a^^b) * inv(x).

axiom case_1_3_2_2_aux : 
   forall (Ri,L:block, Mi:message, p, j:int), 
       of_int(p) ^^ L = (gamma (j) * L) ^^ Ri ^^ (Mi ~> j) =>
       L ^^ (gamma(j) * L) = Ri ^^ (Mi~>j) ^^ of_int(p).

lemma case_1_3_2_2: 
   forall (Ri,L:block, Mi:message, p, j:int), 
       of_int(p) ^^ L = (gamma (j) * L) ^^ Ri ^^ (Mi ~> j) =>
       L = (Ri ^^ (Mi~>j) ^^ of_int(p)) * inv(of_int(1) ^^ gamma(j)).
unset  case_1_3_aux1, gamma_diff_1', inv_mult, case_1_2_2_2_aux.

op build_pRiMi : (int, (block*message) array) -> block list.

axiom build_pRiMi_spec : forall (p,i,j:int, Log : (block*message) array),
   let Ri = fst(Log~>i) in
   let Mi = snd(Log~>i) in
   0 <= i => i < p =>
   0 <= j => j < length(Mi) =>
   mem((Ri ^^ (Mi~>j) ^^ of_int(p)) * inv(of_int(1) ^^ gamma(j)), 
       build_pRiMi(p,Log)).

axiom case_1_3 : forall (Log:(block * message) array, p:int, L:block),
  0 <= p => p < q => 
  is_jLRM(of_int(p)^^L, L, Log, p) =>
  mem(L,build_pRiMi(p,Log)).
(*
Proof.
 intros Log p L W1 W2 (i,(j,H));simpl in H;decompose [and] H;clear H.
 apply case_1_3_2_2 in H5;rewrite H5.
 apply build_pRiMi_spec;trivial.
Qed.
*)
unset case_1_3_2_2, build_pRiMi_spec.
set case_1_1, case_1_2.

lemma case_1 : forall (LB:block list, Log:(block * message) array, p:int, L:block),
  (forall (x:block)[mem(x,LB)], mem(x,LB) =>
    (x = bs0_n || is_iL(x, p, L) || is_jLRM (x, L, Log, p))) =>
  0 <= p => p < q => 
  mem(of_int(p)^^L, LB) =>
  (L = of_int(p) || mem(L,build_pRiMi(p,Log))).
unset case_1, case_1_2, case_1_3. 

(* Now we focus on the second case *)

op build_jLMpj : (block, message) -> block list.

axiom build_jLMpj_spec : forall (L:block, Mp:message, j:int),
   0 <= j => j < length(Mp) =>
   mem((gamma(j) * L) ^^ (Mp~>j), build_jLMpj(L,Mp)).

lemma case_2_1_aux : forall  (L,Rp:block, Mp:message, j:int),
   ((gamma(j)*L) ^^ Rp) ^^ (Mp~>j) = bs0_n =>
   Rp = (gamma(j)*L) ^^ (Mp~>j).

lemma case_2_1 : forall  (L,Rp:block, Mp:message, j:int),
   0 <= j => j < length(Mp) =>
   ((gamma(j)*L) ^^ Rp) ^^ (Mp~>j) = bs0_n =>
   mem(Rp,  build_jLMpj(L,Mp)).
unset build_jLMpj_spec, case_2_1_aux, case_2_1.

op build_pRpMp : (block,message,int) -> block list.

axiom build_pRpMp_spec : forall (Rp:block,Mp:message,p,i,j:int),
   0 <= i => i <= p =>
   0 <= j => j < length(Mp) => 
   mem((Rp ^^ (Mp~>j)^^of_int(i)) * inv(of_int(1)^^gamma(j)), build_pRpMp(Rp,Mp,p)).

set case_1_3_2_2.

axiom case_2_2 : forall (L,Rp,x:block, p,j:int,Mp:message),
   0 <= j => j < length(Mp) =>
   is_iL(x,p+1,L) =>
   ((gamma(j)*L) ^^ Rp) ^^ (Mp~>j) = x =>
   mem(L,build_pRpMp(Rp,Mp,p)).
(* 
Proof.
 intros L Rp p j Mp W1 W2 (i,H);decompose [and] H;clear H.
 apply eq_sym in H3;apply case_1_3_2_2 in H3;rewrite H3 at 1.
 apply (build_pRpMp_spec L Rp Mp p i j);auto with zarith.
Qed.
*)
unset case_1_3_2_2, build_pRpMp_spec, case_2_2.

lemma case_2_3_aux : 
   forall (Rp,Ri,L:block, Mp,Mi:message, l, j:int), 
       (gamma (l) * L) ^^ Rp ^^ (Mp ~> l) = (gamma(j) * L) ^^ Ri ^^ (Mi ~> j) =>
       Rp = (gamma(j) * L) ^^ Ri ^^ (Mi ~> j) ^^ (Mp~>l) ^^ (gamma(l) * L).

op build_jLMplLRiMi : 
   (block,message,(block*message) array, int) -> block list.

axiom build_jLMplLRiMi_spec : 
  forall (L:block,Mp:message,Log:(block*message) array, p,j,i,l:int),
    let Ri = fst(Log~>i) in
    let Mi = snd(Log~>i) in
    0 <= i => i < p =>
    0 <= j => j < length(Mp) =>
    0 <= l => l < length(Mi) =>
    mem( (gamma(l) * L) ^^ Ri ^^ (Mi ~> l) ^^ (Mp~>j) ^^ (gamma(j) * L),
        build_jLMplLRiMi(L,Mp,Log,p)).

axiom case_2_3 : 
   forall (L,Rp:block,Mp:message,Log:(block*message) array, p,j:int),
   0 <= j => j < length(Mp) =>
   is_jLRM((gamma (j) * L) ^^ Rp ^^ (Mp ~> j), L, Log, p) =>
   mem(Rp, build_jLMplLRiMi(L,Mp,Log,p)).
(*
Proof.
 intros L Rp Mp Log p j W1 W2 (i,(l,H));simpl in H;decompose [and] H;clear H.
 apply case_2_3_aux in H5;rewrite H5 at 1.
 apply (build_jLMplLRiMi_spec L Mp Log p j i l);trivial.
Qed.
*)
unset  case_2_3_aux,  build_jLMplLRiMi_spec, case_2_3. 

(* we need 2^n - 2, since we do not allows 1 (gamma_diff_1) *)
axiom gamma_diff_lt : forall (i,j:int),
   0 <= i => i < j => j < 2^n - 1 => (gamma(i) ^^ gamma(j)) <> bs0_n.

axiom case_2_4_aux :
   forall (Rp,L:block, Mp:message, l, j:int),
       0 <= l => l < j => j < 2^n - 1 =>  
       (gamma (j) * L) ^^ Rp ^^ (Mp ~> j) = (gamma(l) * L) ^^ Rp ^^ (Mp ~> l) =>
       L = ((Mp ~>l) ^^ (Mp ~>j)) * inv(gamma(l) ^^ gamma(j)).
(* Proof in Coq 
Proof. 
 intros Rp L Mp l j H1 H2 H3 H4.
 apply inv_mult.
 apply gamma_diff_lt;trivial.
 rewrite mult_comm, mult_distr, !(mult_comm L).
 apply xor_inj with (aget Mp j).
 rewrite !xor_n_assoc, xor_n_cancel, xor_n_zero_r.
 apply xor_inj with  (mult_block (gamma l) L).
 rewrite xor_n_comm, <- !xor_n_assoc, xor_n_cancel, 
   (xor_n_comm bs0_n), xor_n_zero_r, xor_n_comm.
 apply xor_inj with Rp.
 rewrite !xor_n_assoc, xor_n_comm, (xor_n_comm (aget Mp l));trivial.
*)

op build_LMpMpjl : (block,message) -> block list.

axiom build_LMpMpjl_spec : forall (Rp:block,Mp:message,j,l:int),
    0 <= l => l < j => j < length(Mp) => 
    mem(((Mp ~>l) ^^ (Mp ~>j)) * inv(gamma(l) ^^ gamma(j)), 
        build_LMpMpjl(Rp,Mp)).

axiom case_2_4 : forall (L,Rp:block,Mp:message,j,l:int),
    0 <= l => l < j => j < length(Mp) => length(Mp) < 2^n =>
    (gamma (j) * L) ^^ Rp ^^ (Mp ~> j) = (gamma(l) * L) ^^ Rp ^^ (Mp ~> l) =>
    mem(L, build_LMpMpjl(Rp,Mp)).
(*
Proof. 
 intros L Rp Mp j l W1 W2 W3 W4 H.
 apply case_2_4_aux in H;auto with zarith. 
 rewrite H;apply build_LMpMpjl_spec;trivial.
Qed.
*)

unset gamma_diff_lt, case_2_4_aux, build_LMpMpjl_spec.
set case_2_1, case_2_2, case_2_3.
axiom sigma_2n : sigma < 2^n.

lemma case_2_aux : 
   forall (LB:block list, L,Rp:block,Mp:message,Log:(block*message)array,p,j:int),
   let x = (gamma (j) * L) ^^ Rp ^^ (Mp ~> j) in
   (x = bs0_n || is_iL(x, p+1, L) || is_jLRM (x, L, Log, p) ||
    exists (l:int), 0 <= l && l < j && x = (gamma(l) * L) ^^ Rp ^^ (Mp ~> l)) =>
   0 <= j => j < length(Mp) => length(Mp) <= sigma =>
   mem((gamma (j) * L) ^^ Rp ^^ (Mp ~> j), LB) => 
   (mem (Rp,build_jLMpj (L,Mp)) || mem (L,build_pRpMp (Rp,Mp,p)) ||
    mem (Rp,build_jLMplLRiMi (L,Mp,Log,p)) ||  mem(L, build_LMpMpjl(Rp,Mp))).

lemma case_2 : 
   forall (LB:block list, L,Rp:block,Mp:message,Log:(block*message)array,p,j:int),
   (forall (x:block), mem(x,LB) =>
      (x = bs0_n || is_iL(x, p+1, L) || is_jLRM (x, L, Log, p) ||
        exists (l:int), 0 <= l && l < j && x = (gamma(l) * L) ^^ Rp ^^ (Mp ~> l))) =>
   0 <= j => j < length(Mp) => length(Mp) <= sigma =>
   mem((gamma (j) * L) ^^ Rp ^^ (Mp ~> j), LB) => 
   (mem (Rp,build_jLMpj (L,Mp)) || mem (L,build_pRpMp (Rp,Mp,p)) ||
    mem (Rp,build_jLMplLRiMi (L,Mp,Log,p)) ||  mem(L,build_LMpMpjl(Rp,Mp))).
unset sigma_2n, case_2_1, case_2_2, case_2_3, case_2_4, case_2_aux.    
unset case_1, case_2.

game G4 = {
  var p,count : int
  var b,bad1,bad2 : bool
  var L : block
  var Log : (block * message) array
  var Lp,LpRiMi,LpRpMp,LLMpMpjl : block list


  fun LR(m0, m1 : message) : cipher = {
    var cb : cipher;
    var nc:nonce;
    var Mp : message;
    var c : block array;
    var E,X,C,Rp : block;
    var j : int;

    if (length(m0) = length(m1) && p < q && count + length(m0) <= sigma) {
      Rp = {0,1}^n;
      Mp = b ? m0 : m1;
      c = make(length(m0), bs0_n);
      j = 0;
      nc = of_int(p);
      (* 1.1 *) Lp = nc :: Lp;  (* 1.1 *)    
      (* 1.2 *) (* absurd *)
      (* 1.3 *) LpRiMi = build_pRiMi (p,Log) ++ LpRiMi; 
      (* 2.1 *) bad1 = bad1 || mem (Rp,build_jLMpj (L,Mp)); 
      (* 2.2 *) LpRpMp = build_pRpMp (Rp,Mp,p) ++ LpRpMp;
      (* 2.3 *) bad2 = bad2 || mem (Rp,build_jLMplLRiMi(L,Mp,Log,p));
      (* 2.4 *) LLMpMpjl = build_LMpMpjl (Rp,Mp) ++ LLMpMpjl;

      while (j < length(m0)) {
        C = {0,1}^n;
        c = c <~(j,C);
        j = j + 1;
      }
      Log = Log <~(p, (Rp,Mp)); 
      p = p + 1;
      cb = (nc, c);      
      count = count + length(m0);
    } else {
      cb = (bs0_n,make(0,bs0_n));
    }
    return cb;
  }  
  
  abs A = A{LR}

  fun Main () : bool = {
    var b' : bool;
    b = {0,1};
    p = 0; count = 0;
    bad1 = false; bad2 = false;
    Log = make(q,(bs0_n,make(0,bs0_n)));
    Lp = []; LpRiMi = []; LpRpMp = []; LLMpMpjl = [];
    L = {0,1}^n;
    b' = A ();
    return b = b';
  }
}.

axiom is_jLRM_upd :  
  forall (x,L,Rp:block,Mp:message, Log:(block*message) array, p:int),
    is_jLRM(x,L,Log,p) =>
    is_jLRM(x,L,Log<~(p,(Rp,Mp)),p + 1).
(*
Proof.
 intros x L Rp Mp Log p (i,(j,H)).
 simpl in H;decompose [and] H; exists i;exists j.
 rewrite aget_aset_diff;simpl;auto with zarith.
Qed.
*)

equiv G3_G4_LR : G3.LR ~ G4.LR :
   (={L,b,p,count} &&
    0 <= p{2} && 0 <= count{2} && 
    length(Log{2}) = q && 
    (bad{1} => 
      (mem(L, Lp){2} || mem(L,LpRiMi){2} ||
       bad1{2} || mem(L,LpRpMp){2} || bad2{2} || mem(L,LLMpMpjl){2})) &&
    (forall (x:block), mem(x,LB{1}) =>
      ( x = bs0_n || is_iL(x,p{2},L{2}) || is_jLRM(x,L{2},Log{2},p{2})))).
if;[ | trivial].
swap{1} 7 -6.
app 1 1 (={m0,m1,Rp,L,b,p,count} &&
         0 <= p{2} && 0 <= count{2} && length (Log{2}) = q &&
         (bad{1} = true =>
           (mem (L{2},Lp{2}) || mem (L{2},LpRiMi{2}) ||
            bad1{2} || mem (L{2},LpRpMp{2}) || bad2{2}  || mem (L{2},LLMpMpjl{2}))) &&
          (forall (x : block),
            mem (x,LB{1}) =>
              (x = bs0_n ||is_iL(x,p{2},L{2}) ||
               is_jLRM(x,L{2},Log{2},p{2}))) &&
          length (m0{2}) = length (m1{2}) &&
          p{2} < q && count{2} + length (m0{2}) <= sigma).
 trivial.
app 6 10 
   (={L,b,p,count,m0,Rp,Mp,nc,c,j} &&
    0 <= p{2} && 0 <= count{2} && 
    length(Log{2}) = q && 
    length(m0{2}) = length(Mp{2}) && 
    p{2} < q && count{2} + length (m0{2}) <= sigma && j{2} = 0 &&
    (bad{1} => 
      (mem(L, Lp){2} || mem(L,LpRiMi){2} ||
       bad1{2} || mem(L,LpRpMp){2} || bad2{2} || mem(L,LLMpMpjl){2})) &&
    (forall (x:block), mem(x,LB{1}) =>
      (x = bs0_n || is_iL(x,p{2}+1,L{2}) || is_jLRM(x,L{2},Log{2},p{2}))) &&
    (mem(Rp,build_jLMpj (L,Mp)){2} => bad1{2}) &&
    (mem(Rp,build_jLMplLRiMi (L,Mp,Log,p)){2} => bad2{2})) &&
    (mem(L,build_pRpMp (Rp,Mp,p)){2} => mem(L,LpRpMp){2}) &&
    (mem(L,build_LMpMpjl (Rp,Mp)){2} => mem(L,LLMpMpjl){2}).
 set case_1. trivial.
while >> : (={L,b,p,count,m0,Rp,Mp,nc,c,j} &&
    0 <= p{2} && 0 <= count{2} && 
    length(Log{2}) = q && 
    length(m0{2}) = length(Mp{2}) && 
    p{2} < q && count{2} + length (m0{2}) <= sigma && 
    0 <= j{2} && j{2} <= length(Mp{2}) &&
    (bad{1} => 
      (mem(L, Lp){2} || mem(L,LpRiMi){2} ||
       bad1{2} || mem(L,LpRpMp){2} || bad2{2} || mem(L,LLMpMpjl){2})) &&
    (forall (x:block), mem(x,LB{1}) =>
      (x = bs0_n || is_iL(x,p{2}+1,L{2}) || is_jLRM(x,L{2},Log{2},p{2}) ||
       exists (l : int),
         0 <= l && l < j{2} && x = (gamma(l) * L{2}) ^^ Rp{2} ^^ (Mp{2}~>l))) &&
    (mem(Rp,build_jLMpj (L,Mp)){2} => bad1{2}) &&
    (mem(Rp,build_jLMplLRiMi (L,Mp,Log,p)){2} => bad2{2})) &&
    (mem(L,build_pRpMp (Rp,Mp,p)){2} => mem(L,LpRpMp){2}) &&
    (mem(L,build_LMpMpjl (Rp,Mp)){2} => mem(L,LLMpMpjl){2}).
 set case_2. trivial.
trivial.
save.

equiv G3_G4 : G3.Main ~ G4.Main : true ==> 
   bad{1} => 
      (mem(L, Lp){2} || mem(L,LpRiMi){2} ||
       bad1{2} || mem(L,LpRpMp){2} || bad2{2} || mem(L,LLMpMpjl){2})
by auto (={L,b,p,count} &&
    0 <= p{2} && 0 <= count{2} && 
    length(Log{2}) = q && 
    (bad{1} => 
      (mem(L, Lp){2} || mem(L,LpRiMi){2} ||
       bad1{2} || mem(L,LpRpMp){2} || bad2{2} || mem(L,LLMpMpjl){2})) &&
    (forall (x:block), mem(x,LB{1}) =>
      ( x = bs0_n || is_iL(x,p{2},L{2}) || is_jLRM(x,L{2},Log{2},p{2})))).

claim Pr_G3_G4_aux : G3.Main[bad] <=
   G4.Main[bad1 || bad2 || mem(L,Lp++LpRiMi++LpRpMp++LLMpMpjl)]
using G3_G4.

claim Pr_G4 : G4.Main[bad1 || bad2 || mem(L,Lp++LpRiMi++LpRpMp++LLMpMpjl)] 
   <= G4.Main[bad1] +G4.Main[bad2] + G4.Main[mem(L,Lp++LpRiMi++LpRpMp++LLMpMpjl)]
compute. 

claim Pr_G3_G4 : G3.Main[bad] <=
   G4.Main[bad1] +G4.Main[bad2] + G4.Main[mem(L,Lp++LpRiMi++LpRpMp++LLMpMpjl)].
unset Pr_G3_G4_aux, Pr_G4.

claim claim5 : | CPA.Main[res] - 1%r/2%r | <=
    | PRP0.Main[res] - PRP1.Main[res] | +  (1+sigma + q)%r * ((sigma+q)%r / (2^n)%r) +
    G4.Main[bad1] +G4.Main[bad2] + G4.Main[mem(L,Lp++LpRiMi++LpRpMp++LLMpMpjl)].
unset Pr_G3_G4, claim4.

(* We have to bound 
   1/ G4.Main[bad1] 
      bad1 is set in LR is Rp is in build_jLMpj(L,Mp).
      The length of build_jLMpj(L,Mp) is length(Mp).
      So the probability is 
          Sum(i=0..q-1) length(Mi)/2^n =
          (Sum(i=0..q-1) length(Mi))/2^n <= sigma /2^n
      In Certicrypt we will use the following invariant :
          1_bad1 + 1_!bad * (sigma - Sum(i=0..p-1) length(Mi))/2^n
      furthermore Sum(i=0..p-1) length(Mi) = count,
      So we can use 1_bad1 + 1_!bad * (sigma - count)/2^n
      We will get sigma/2^n
   2/ G4.Main[bad2]
      bad2 is set in LR is Rp is in  build_jLMplLRiMi(L,Mp,Log).
      Then length of build_jLMplLRiMi(L,Mp,Log).
          length(Mp) * Sum(i=0..p-1) length(Mi) <= length(Mp) * sigma
      we get sigma^2
      In Certicrypt we will use the following invariant :
          1_bad1 + 1_!bad * (sigma - count)*sigma/2^n
   3/ G4.Main[mem(L,Lp++LpRiMi++LpRpMp++LLMpMpjl)]
      The length of L is bounded by q.
      The length of LpRiMi is bounded by Sum(p=0..q-1) Sum(i=0..p-1) length(Mi)
         So its bounded by q * sigma
      The length of LpRpMp is bounded Sum(p=0..q-1) p * length(Mp) <=
                Sum(p=0..q-1) q * length(Mp) <=
                q * Sum(p=0..q-1) length(Mp) <= q * sigma
      The length of LLMpMpjl is 
          Sum(p=0..q-1) Sum(j=1 .. length(Mp)-1) j - 1 =
          Sum(p=0..q-1) Sum(j=0 .. length(Mp)-2) j =
          Sum(p=0..q-1) (length(Mp) - 2) * (length(Mp) - 1) / 2 =
          1/2 * Sum(p=0..q-1) length(Mp)^2 - 3/2 * Sum(p=0..q-1) length(Mp) + q <=
          (sigma^2 - 3*sigma - 2q) /2  
*)

claim Pr_bad1 : G4.Main[bad1] <= sigma%r/(2^n)%r
admit.

claim Pr_bad2 : G4.Main[bad2] <= (sigma^2)%r/(2^n)%r
admit.

(* We focus on 
   G4.Main[mem(L,Lp++LpRiMi++LpRpMp++LLMpMpjl)] *)

game G5 = {
  var p,count : int
  var b : bool
  var L : block
  var Log : (block * message) array
  var Lp,LpRiMi,LpRpMp,LLMpMpjl : block list


  fun LR(m0, m1 : message) : cipher = {
    var cb : cipher;
    var nc:nonce;
    var Mp : message;
    var c : block array;
    var E,X,C,Rp : block;
    var j : int;

    if (length(m0) = length(m1) && p < q && count + length(m0) <= sigma) {
      Rp = {0,1}^n;
      Mp = b ? m0 : m1;
      c = make(length(m0), bs0_n);
      j = 0;
      nc = of_int(p);
      (* 1.1 *) Lp = nc :: Lp;  (* 1.1 *)    
      (* 1.3 *) LpRiMi = build_pRiMi (p,Log) ++ LpRiMi; 
      (* 2.2 *) LpRpMp = build_pRpMp (Rp,Mp,p) ++ LpRpMp;
      (* 2.4 *) LLMpMpjl = build_LMpMpjl (Rp,Mp) ++ LLMpMpjl;

      while (j < length(m0)) {
        C = {0,1}^n;
        c = c <~(j,C);
        j = j + 1;
      }
      Log = Log <~(p, (Rp,Mp)); 
      p = p + 1;
      cb = (nc, c);      
      count = count + length(m0);
    } else {
      cb = (bs0_n,make(0,bs0_n));
    }
    return cb;
  }  
  
  abs A = A{LR}

  fun Main () : bool = {
    var b' : bool;
    b = {0,1};
    p = 0; count = 0;
    Log = make(q,(bs0_n,make(0,bs0_n)));
    Lp = []; LpRiMi = []; LpRpMp = []; LLMpMpjl = [];
    b' = A ();
    L = {0,1}^n;
    return b = b';
  }
}.

op sum_length : ((block*message) array, int) -> int.

axiom sum_length_upd : 
   forall (Log:(block*message) array, p:int, Rp:block,Mp:message),
     0 <= p => p < length(Log) =>
     sum_length(Log<~(p,(Rp,Mp)), p+1) = sum_length(Log,p) + length(Mp).

axiom length_build_pRiMi : forall (Log:(block*message) array, p:int),
     0 <= p => p < length(Log) =>
     length(build_pRiMi(p,Log)) = sum_length(Log,p).

axiom length_build_pRpMp : forall (Rp : block, Mp : message, p: int),
    0 <= p =>
    length(build_pRpMp(Rp,Mp,p)) = p * length(Mp).

axiom length_build_LMpMpjl : forall (Rp : block, Mp : message),
    length(build_LMpMpjl (Rp,Mp)) <= length(Mp)^2.
(* The real length is (length(Mp) - 2) * (length(Mp) -1),
   so we can improve the bound *)

axiom sum_square_le : forall (x,y:int), 0 <= x => 0 <= y => x^2 + y^2 <= (x+y)^2.

equiv G4_G5_LR : G4.LR ~ G5.LR : 
                 (={b,p,count,Log,Lp,LpRiMi,LpRpMp,LLMpMpjl} &&
                  length(Log{2}) = q &&
                  0 <= count{2} && count{2} <= sigma &&
                  0 <= p{2} && p{2} <= q &&
                  count{2} = sum_length(Log{2},p{2}) &&
                  length(Lp{2}) <= p{2} &&
                  length(LpRiMi{2}) <= p{2} * sigma &&
                  length(LpRpMp{2}) <= q * count{2} &&
                  length(LLMpMpjl{2}) <= (count{2})^2).
if;[ wp | trivial].
while : ={j,c,m0};[ trivial | ].
trivial.
app 0 0 (length (LpRpMp{2}) <= q * count{2} &&
         0 <= p{2} &&
         p{2} * length(m0{2}) <= q * length(m0{2}) &&         
         length(m0{2}) = length(if b{2} then m0{2} else m1{2})).
trivial.
trivial.
admit.
save.

axiom sum_length_0 : forall (Log : (block*message) array),
   sum_length(Log,0) = 0.

equiv G4_G5 : G4.Main ~ G5.Main : true ==>
     ={L,Lp,LpRiMi,LpRpMp,LLMpMpjl} &&
     length(Lp{2}) <= q &&
     length(LpRiMi{2}) <= q * sigma &&
     length(LpRpMp{2}) <= q * sigma &&
     length(LLMpMpjl{2}) <= (sigma)^2.
swap{2} -1.
app 12 10 
  (={L,Lp,LpRiMi,LpRpMp,LLMpMpjl} &&
    0 <= count{2} && count{2} <= sigma &&
    0 <= p{2} && p{2} <= q &&
    count{2} = sum_length(Log{2},p{2}) &&
    length(Lp{2}) <= p{2} &&
    length(LpRiMi{2}) <= p{2} * sigma &&
    length(LpRpMp{2}) <= q * count{2} &&
    length(LLMpMpjl{2}) <= (count{2})^2 &&
    p{2} * sigma <= q * sigma &&
    q * count{2} <= q * sigma && 
    (count{2})^2 <= sigma^2);[ | trivial].
app 12 10  (={L,Lp,LpRiMi,LpRpMp,LLMpMpjl} &&
    0 <= count{2} && count{2} <= sigma &&
    0 <= p{2} && p{2} <= q &&
    count{2} = sum_length(Log{2},p{2}) &&
    length(Lp{2}) <= p{2} &&
    length(LpRiMi{2}) <= p{2} * sigma &&
    length(LpRpMp{2}) <= q * count{2} &&
    length(LLMpMpjl{2}) <= (count{2})^2);[ | trivial].
eqobs_in (={b,p,count,Log,Lp,LpRiMi,LpRpMp,LLMpMpjl})
                 (length(Log{2}) = q &&
                  0 <= count{2} && count{2} <= sigma &&
                  0 <= p{2} && p{2} <= q &&
                  count{2} = sum_length(Log{2},p{2}) &&
                  length(Lp{2}) <= p{2} &&
                  length(LpRiMi{2}) <= p{2} * sigma &&
                  length(LpRpMp{2}) <= q * count{2} &&
                  length(LLMpMpjl{2}) <= (count{2})^2)
         (={L,Lp,LpRiMi,LpRpMp,LLMpMpjl});trivial.
save.

claim Pr_G4_G5 : 
  G4.Main[mem(L,Lp++LpRiMi++LpRpMp++LLMpMpjl)] =
  G5.Main[mem(L,Lp++LpRiMi++LpRpMp++LLMpMpjl) && 
          length(Lp++LpRiMi++LpRpMp++LLMpMpjl) <=  q + 2*q*sigma + sigma^2]
using G4_G5. 

lemma sigma2_pos : 0 <= sigma^2.
lemma bound_pos : 0 <= q + 2*q*sigma + sigma^2.

claim Pr_G5 :  
   G5.Main[mem(L,Lp++LpRiMi++LpRpMp++LLMpMpjl) && 
           length(Lp++LpRiMi++LpRpMp++LLMpMpjl) <=  q + 2*q*sigma + sigma^2] <=
    (q + 2*q*sigma + sigma^2)%r/(2^n)%r
compute.

claim conclusion : 
  | CPA.Main[res] - 1%r/2%r | <=
     | PRP0.Main[res] - PRP1.Main[res] | +  
       (1+sigma + q)%r * ((sigma+q)%r / (2^n)%r) +
       sigma%r/(2^n)%r +(sigma^2)%r/(2^n)%r + 
       (q + 2*q*sigma + sigma^2)%r/(2^n)%r.

(* The final bound is
   (1+sigma+q)(sigma+q) + sigma + sigma^2 + q + 2*q*sigma + sigma^2 =
   3*sigma^2 + 4*q*sigma + 2*sigma + 2q + q^2
*)
