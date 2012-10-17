type group
type pkey = group
type skey = int
type message
type signature = group 

// generator of the group 
cnst g : group

cnst bottom : message 

// queries
cnst q   : int
cnst req : int

cnst _pk : pkey
cnst _sk : skey


op (*)     : group, group -> group = mult
op (^)     : group, int -> group   = pow
op pairing : group, group -> group = pairing
op dlg     : group -> int          = dlg // discrete logarithm in base g

axiom req_pos : {0 < req }

axiom req_pos_real : { 0%r < 1%r/req%r }

axiom group_pow_mult :
 forall (x:int, y:int). { (g ^ x) ^ y == g ^ (x * y) } 

axiom group_pow_add : 
 forall (x:int, y:int). { g ^ (x + y) == (g ^ x) * (g ^ y) }

axiom pow_mod : 
 forall (z:int). { g ^ (z%q) == g ^ z }

axiom mod_add : 
 forall (x:int, y:int). { (x%q + y)%q == (x + y)%q }

axiom mod_sub : 
 forall (x:int, y:int). { (x%q - y)%q == (x - y)%q } 

axiom mod_small : 
 forall (x:int). { 0 <= x } => { x < q } => { x%q == x}


axiom dlg_pow : forall (x:group). { g^dlg(x) == x }

axiom pow_dlg : forall (a:int). { dlg(g^a) == a%q }

axiom dlg_bound : forall (x:group). { 0 <= dlg(x) } /\ { dlg(x) <= q-1 }


axiom pairing_spec : forall (g1: group, g2: group, a: int, b:int ).
      {pairing (g1 ^ a, g2 ^ b) == (pairing (g1, g2))^(a*b)}

axiom pairing_prop : forall (g1: group, a: int, b:int ).
      {pairing (g1 ^(a*b) , g1) == pairing (g1^a, g1^b) } 

axiom pairing_comm : forall (g1: group, g2: group, a:int, b:int). 
      {pairing (g1^a, g2^b) == pairing (g2^b, g1^a)} 


axiom pk_sk: forall (t:int).  
      {pairing (g^(_sk *t),g) == pairing (_pk, g^t)}

axiom pk_sk_prop: forall (t:int).
      {_pk ^ t == (g^t)^(_sk)}

axiom sk_pk : forall (t:int).
      {_pk ^ t == (g^(_sk)) ^t }

      
/* ********************** end of axioms **********************************/

adversary A(pk:pkey) : message * signature { message -> group; message -> signature}

prover "alt-ergo"

//initial game
game BLS = {
     var S : message list
     var V : (message, group) map
     var i : int
     var pk: pkey
     var sk: skey

     fun H(m: message) : group = {
     	 var t : int = [0..q-1];
	 if (!in_dom(m,V)) {
	    i = i + 1;
	    V[m] = g ^ t; 
	    };
	    return V[m];
     }

     fun Sign (m: message) : signature = {
     	 var h : group;
	 S = m :: S;
	 h = H(m) ; 
	 return (h ^ sk) ;
     }

     abs A = A {H, Sign}

     fun Main() : bool = {
     	 var h     : group;
	 var sigma : signature;
	 var m_adv : message;
	 (pk, sk) = (_pk, _sk);
	 V = empty_map();
	 S = [];
	 i = 0; 
	 (m_adv, sigma) = A (pk); 
	 h = H(m_adv); 
	 return ((pairing( sigma, g) == pairing (h, pk)) && !in (m_adv,S));
     }
}


game G1 = BLS
     var W : (int, message) map
     var I : (message, int) map
     var t': int
     var j : int
     var m_adv : message
     var sigma : signature

     where H = {
     	   var t: int = [0..q-1];
	   if (!in_dom(m,V)){
	      i = i+1;
	      W[i] = m;
	      I[m] = i;
	      V[m] = g^t;
	   };
	   return V[m];
     }
     
     and Main = {
     	 var h: group;
	 (pk, sk) = (_pk, _sk);
	 V = empty_map();
	 W = empty_map();
	 I = empty_map();
	 S = [];
	 i = 0; 
	 (m_adv, sigma) = A (pk); 
	 t' = [0..q-1];
	 if (!in_dom(m_adv,V)) {V[m_adv] = g^t';};
	 h = V[m_adv]; 
	 j = [1..req];
	 return ((pairing (sigma,g) == pairing (h, pk)) && !in (m_adv,S));
     }

equiv BLS_G1 : BLS.Main ~ G1.Main : {true}==> ={res} /\ { i{2} <= i{1} };;
inline{1} H; derandomize; wp;;
auto inv ={V,S,i,pk,sk};;
push{2} 1; rnd; trivial;;
save;;

claim Pr_BLS_G1: BLS.Main [res && i <= req] <= G1.Main [res && i <= req]
using BLS_G1;;

prover simplify;;

unset pairing_spec, pairing_prop, pairing_comm, 
      pk_sk, pk_sk_prop, sk_pk, mod_sub, mod_add,
      group_pow_add, group_pow_mult, pow_mod;;


equiv auto  G1_G1: G1.Main ~ G1.Main:  {true} ==> ={I,i,j,m_adv,res} /\
 ({ (res && !in_dom(m_adv,I)){1} } =>
        { (pairing (sigma, g) == (pairing (g^t', pk))) {2} }) /\
 forall (m:message). { in_dom(m,I{1}) } => { (1 <= I[m] && I[m] <= i){2} } /\
 forall (m:message). { in_dom(m,I{1}) } => { (in_dom(I[m],W) && W[I[m]] == m){2} }
  inv ={V,S,i,pk,sk,I} /\ { 0 <= i{1} } /\
 forall (m:message). { in_dom(m,V{1}) == in_dom(m,I{1}) } /\
 forall (m:message). { in_dom(m,I{1}) } => { (1 <= I[m] && I[m] <= i){2}} /\
 forall (m:message). 
  { in_dom(m,I{1}) } => { (in_dom(I[m],W) && W[I[m]] == m){2} };;


claim Pr_G1: G1.Main [res && i<= req] * 1%r / req%r <=
      	     G1.Main [res && in_dom(j,W) && W[j] == m_adv] + 1%r / q%r * 1%r/req%r
admit;;

game G2 = G1 
     var b: int

     where H = { 
     	   var t: int;
	   if (!in_dom(m,V) && !in_rng(m, W) && !(m == W[j] && j <= i)){
	      i = i+1;
	      W[i] = m;
	      I[m] = i;
	      t = [0..q-1];
	      V[m] = g^t;
	   };
	   return V[m];	    
     }

     and Main= {
	(pk, sk) = (_pk, _sk);
	 V = empty_map();
	 W = empty_map();
	 I = empty_map();
	 S = [];
	 i = 0;
	 sigma = g; 
	 t' = 0;  
	 b = 0; 
	 m_adv = bottom;
	 j = [1..req];
	 (m_adv, sigma) = A(pk);

	 if (i<j) {b = [0..q-1];} else {b = dlg(V[W[j]]) /* i.e. b = t */;}
 
	 return ((pairing (sigma,g) == pairing (V[m_adv], pk)) && !in (m_adv,S));
     }    

prover simplify;;

 equiv auto G1_G2 : G1.Main ~ G2.Main : 
    {true} ==> { (in_dom(j,W) && W[j] == m_adv){1} } => ={j,W,m_adv,res}
    inv ={V,S,W,I,i,pk,sk} /\ { 0 <= i{1} } /\
     (forall (m:message). { !in_dom(m,V{1}) } => 
                          { (!in_rng(m,W) && !(m == W[j] && j <= i)){2} }) /\ 
     (forall (m:message). { in_dom(m,I{1}) == in_dom(m,V{1}) }) /\
     (forall (m:message). { in_dom(m,I{1}) } => { (1 <= I[m] && I[m] <= i){1}}) /\
     (forall (m:message). 
      { in_dom(m,I{1}) } => { (in_dom(I[m],W) && W[I[m]] == m){1} }) /\
     (forall (k:int). 
      { in_dom(k,W{1}) } => { (in_dom(W[k],I) && I[W[k]] == k){1} });;


prover "alt-ergo";;

claim Pr_G1_G2 : G1.Main[res && in_dom(j, W) && W[j] == m_adv] <= 
      	         G2.Main[res && in_dom(j, W) && W[j] == m_adv]
using G1_G2;;

claim Pr_BLS_G2: BLS.Main[res && i <= req] * 1%r / req%r <=
      	       	  G2.Main[res && in_dom(j,W) && W[j] == m_adv] + 1%r/q%r * 1%r/req%r;;


//Fix the answer to the j-th hash query
game G3 = G2
     where H = { 
     	   var t: int;
	   if (!in_dom(m,V) && !in_rng(m, W) && !(m == W[j] && j <= i)){
	      i = i+1;
	      W[i] = m;
	      I[m] = i;
	      if (i == j) {V[m] = g^b;} else { t = [0..q-1]; V[m] = g^t;}
	   };
	   return V[m];	    
     }	   

     and Main = {
	 (pk, sk) = (_pk, _sk);
	 V = empty_map();
	 W = empty_map();
	 I = empty_map();
	 S = [];
	 i = 0;
	 sigma = g; 
	 t' = 0;  
	 b = 0; 
	 m_adv = bottom;
	 j = [1..req];

	 if (i<j) {b = [0..q-1];} else {b = dlg(V[W[j]]);}

	 (m_adv, sigma) = A(pk); 
	 return ((pairing (sigma, g) == pairing (V[m_adv], pk)) && !in (m_adv,S));
     }


equiv auto G2_G3 : G2.Main ~ G3.Main : {true} ==> ={W,j,m_adv,res}
 eager 
 if (i < j) { b = [0..q-1]; } else { b = dlg(V[W[j]]); };;
// swap condition for H
derandomize;;
case{1} : in_dom(m,V) || in_rng(m,W) || (m == W[j] && in_dom(j,W));;
push{1} 1;; wp;; rnd;; rnd;; trivial;;
 
case{1} : i+1 == j;;
wp; rnd; rnd; trivial;;
push{1} 1; wp; rnd; rnd; trivial;;
save;;

// head => eq
rnd; wp; trivial;;

// tail => eq
trivial;; 
save;;


claim Pr_G2_G3 : G2.Main[res && in_dom(j,W) && W[j] == m_adv] == 
       	       	 G3.Main[res && in_dom(j,W) && W[j] == m_adv]
using G2_G3;;


//Simplify G3
game G4 = G3
     where H = { 
     	   var t: int = [0..q-1];
	   if (!in_dom(m,V)){
	      i = i+1;
	      W[i] = m;
	      I[m] = i;
	      if (i == j) {V[m] = g^b;} else {V[m] = g^t;}
	   };
	   return V[m];	    
     }	   

     and Main = {
	 (pk, sk) = (_pk, _sk);
	 V = empty_map();
	 W = empty_map();
	 I = empty_map();
	 S = [];
	 i = 0;
	 j = [1..req];
	 b = [0..q-1];
	 (m_adv, sigma) = A(pk); 
	 return ((pairing (sigma, g) == pairing (V[m_adv], pk)) && !in (m_adv,S));
     }


equiv auto G3_G4 : G3.Main ~ G4.Main : {true} ==> ={W,j,m_adv,res}
 inv ={V,S,W,I,i,pk,sk,b,j} /\
     forall (m:message). {!in_dom(m,V{1})} => 
                         {!in_rng(m,W{1}) && !(m == W[j] && j<=i){1}};;

claim Pr_G3_G4 : G3.Main[res && in_dom(j,W) && W[j] == m_adv] == 
      	       	 G4.Main[res && in_dom(j,W) && W[j] == m_adv]
using G3_G4;;


// At this point we have
claim Pr_BLS_G4 : BLS.Main[res && i <= req] * 1%r/req%r <= 
                  G4.Main[res && in_dom(j,W) && W[j] == m_adv] + 1%r/q%r * 1%r/req%r;;

game G5 = G4
      var P : (message, group) map

       where H = { 
       	   var t: int = [0..q-1];
	   if (!in_dom(m,V)){
	      i = i+1;
	      W[i] = m;
	      I[m] = i;
	      P[m] = pk ^ t ;
	      if (i == j) {V[m] = g^b;} else {V[m] = g^t;}
	   };
	   return V[m];	    
     }	   

     and Main = {
	 (pk, sk) = (_pk, _sk);
	 V = empty_map();
	 W = empty_map();
	 I = empty_map();
	 P = empty_map();
	 S = [];
	 i = 0;
	 j = [1..req];
	 b = [0..q-1];
	 (m_adv, sigma) = A(pk); 
	 return ((pairing (sigma, g) == pairing (V[m_adv], pk)) && !in (m_adv,S));
     }

equiv G4_G5 : G4.Main ~ G5.Main : {true} ==> ={W,j,m_adv,res};;
auto inv ={V,W,I,S,pk,sk,i,j,b} /\ {pk{1} == _pk && sk{1} == _sk};;
rnd; rnd; trivial;;
save;;

claim Pr_G4_G5 : G4.Main[res && in_dom(j,W) && W[j] == m_adv] == 
      	       	 G5.Main[res && in_dom(j,W) && W[j] == m_adv]
using G4_G5;;

game G6 = G5
     where Sign = {
     	 var h : group;
	 S = m :: S;
	 h = H(m); 
	 return P[m];
}  

prover simplify;; 

set pk_sk_prop;;

equiv auto G5_G6 : G5.Main ~ G6.Main :
       {true} ==> { !(j <= i && in(W[j],S)){1} } => ={W,j,m_adv,res}
       inv upto { j <= i && in(W[j],S) }
       with 
        ={V,W,I,S,pk,sk,i,j,b} /\ {pk{2} == _pk && sk{2} == _sk} /\
	 (forall (m:message).    
	   { (in_dom(m,V) && !(I[m] == j)){2}} => { (P[m] == V[m]^sk){2} }) /\
	 (forall (k:int). 
	   { in_dom(k,W{2}) } => { k <= i{2} } ) /\
	 (forall (m:message).
	   { in_dom(m,V{2}) } => { (in_dom(I[m],W) && W[I[m]] == m){2} });;


equiv auto G5_G5 : G5.Main ~ G5.Main : {true} ==> 
 ={W,S,j,m_adv,res} /\ ({ res{1} } => { !(in(m_adv,S)){1} })
 inv ={V,W,I,S,pk,sk,i,j,b};;

prover "alt-ergo"

claim Pr_G5_aux : G5.Main[res && in_dom(j,W) && W[j] == m_adv] ==
      		  G5.Main[res && !in(m_adv,S) && in_dom(j,W) && W[j] == m_adv]
using G5_G5;; 

claim Pr_G5_G6a : G5.Main[res && !in(m_adv,S) && in_dom(j,W) && W[j] == m_adv] <= 
                  G6.Main[res && in_dom(j,W) && W[j] == m_adv]
using G5_G6;;

claim Pr_G5_G6 : G5.Main[res && in_dom(j,W) && W[j] == m_adv] <= 
      	       	 G6.Main[res && in_dom(j,W) && W[j] == m_adv];;



game CDH = {
      var V   : (message, group) map
      var P   : (message, group) map
      var y'  : group
      var pk' : pkey
      var i,j : int

      fun H(m:message) : group = {
      	  var t : int = [0..q-1]; 
	  if (!in_dom(m, V)) { 
	     i = i + 1;
	     P[m] = pk' ^ t;
	     if (i == j) { V[m] = y'; } else { V[m] = g ^ t; }
	  };
   	  return V[m];
      }

      fun Sign(m:message) : signature = {
      	  var h : group;
   	  h = H(m);
   	  return P[m];
      }

      abs A = A {H, Sign}

      fun I(pk:pkey, y:group) : group = {
      	  var m : message;
      	  var sigma : signature;

      	  V = empty_map();
      	  P = empty_map();
      	  i = 0;
      	  j = [1..req];
      	  pk' = pk;
      	  y' = y;
      	  (m, sigma) = A(pk);
      	  return sigma;
      }

      fun Main() : bool = {
      	  var b : int = [0..q-1];
  	  var y : group = g ^ b;
 	  var x : group;
  	  var pk : pkey;
  	  var sk : skey;

	  (pk, sk) = (_pk, _sk);
  	  x = I(pk, y);
  	  return (pairing (x, g) == pairing (y, pk));
      }
}


prover simplify;;

equiv G6_CDH : G6.Main ~ CDH.Main : 
 {true} ==> { (res && in_dom(j,W) && W[j] == m_adv){1} } => { res{2} };;
inline{2} I; derandomize; wp;;
auto inv ={V,P,i,j} /\ { g^b{1} == y'{2} } /\ { pk{1} == pk'{2} }
 /\ ({ (in_dom(j,W)){1} } => { (in_dom(W[j],V) && V[W[j]] == g^b){1} });;
push{1} 1; rnd; rnd; trivial;;
save;;

claim Pr_G6_CDH : G6.Main[res && in_dom(j,W) && W[j] == m_adv] <= CDH.Main[res]
using G6_CDH;;

claim Pr_BLS_CDH : BLS.Main[res && i <= req] * 1%r / req%r <=  
      	       	   CDH.Main[res] + 1%r/q%r * 1%r/req%r;;
