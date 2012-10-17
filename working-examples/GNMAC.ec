/*********************************************************************
 * GNMAC.ec
 *
 * This file proves that the GNMAC construction is secure as a PRF
 * assuming the compression function h is a PRF. 
 * The proof follows [1]
 *
 * Since NMAC is a special case of the GNMAC construction where the
 * input message is padded to to a block boundary, PRF-security of
 * NMAC follows. This means that padding plays no role in the
 * PRF-security of NMAC.
 *
 * [1] M. Bellare. New proofs for NMAC and HMAC: Security without
 * collision-resistance. In Advances in Cryptology – CRYPTO 2006
 *******************************************************************/

cnst c : int
cnst b : int
cnst fpad : bitstring{b-c}

type B     = bitstring{b}
type Bstar = B list

op head : Bstar -> B = head

axiom head_def :
 forall (m:B, M:Bstar).
 { head(m :: M) == m }


op tail : Bstar -> Bstar = tail

axiom tail_def :
 forall (m:B, M:Bstar).
 { tail(m :: M) == M }


op drop : int, Bstar -> Bstar = drop

axiom drop_def_1 :
 forall (n:int, M:Bstar).
 { n <= 0 } => { drop(n, M) == M }

axiom drop_def_2 :
 forall (n:int).
 { drop(n, []) == [] }

axiom drop_def_3 :
 forall (n:int, m:B, M:Bstar).
 { 1 <= n } => { drop(n, m :: M) == drop(n - 1, M) }


op take : int, Bstar -> Bstar = take

axiom take_def_1 :
 forall (n:int, M:Bstar).
 { n <= 0 } => { take(n, M) == [] }

axiom take_def_2 :
 forall (n:int).
 { take(n, []) == [] }

axiom take_def_3 :
 forall (n:int, m:B, M:Bstar).
 {1 <= n} => { take(n, M) == m :: take(n-1, M) }


op (||)  : bitstring{c}, bitstring{b-c} -> bitstring{b} = append
op h     : bitstring{c}, B -> bitstring{c} = h
op hstar : bitstring{c}, Bstar -> bitstring{c} = hstar
op GNMAC : bitstring{c}, bitstring{c}, Bstar -> bitstring{c} = GNMAC

axiom hstar_def_1 :
 forall (K:bitstring{c}, m:B).
 { hstar(K, m :: []) == h(K, m) }

axiom hstar_def_2 :
 forall (K:bitstring{c}, m1:B, M:Bstar).
 { hstar(K, m1 :: M) == hstar(h(K, m1), M) }

axiom GNMAC_def :
 forall (K_out:bitstring{c}, K_in:bitstring{c}, M:Bstar).
 { GNMAC(K_out, K_in, M) == h(K_out, hstar(K_in, M) || fpad) }


/*** BEGIN Claim 3.5 ***/
game G1 = {

  fun Main (M1:Bstar, M2:Bstar, l:int) : bool = {
    var m1 : int;
    var a, a1, a2  : bitstring{c};
 
    m1 = length(M1);
    a = {0,1}^c;
    a1 = l < m1 ? hstar(a, drop(l, take(m1, M2))) : a;   // a1 = foldl h g(M2[l]) M2[l+1..m1]
    a2 = hstar(a1, drop(m1, M2));           // a2 = foldl h a1 M2[m1+1..m2]
  
    return (a1 == a2);
  }
}

game G_RF = {
  var L : (B, bitstring{c}) map
  
  fun g (m:B) : bitstring{c} = {
    var x : bitstring{c} = {0,1}^c;
    if (!in_dom(m, L)) { L[m] = x; };
    return L[m];
  }

  fun A1 (M1:Bstar, M2:Bstar, l:int) : bool = {
    var M  : Bstar;
    var m1 : int;
    var a, a1, a2  : bitstring{c};
 
    m1 = length(M1);
    a = g(head(drop(l-1,M2)));              // a = g(M2[l])
    a1 = hstar(a, drop(l, take(m1, M2)));   // a1 = foldl h g(M2[l]) M2[l+1..m1]
    a2 = hstar(a1, drop(m1, M2));           // a2 = foldl h a1 M2[m1+1..m2]
  
    return (a1 == a2);  
  }

  fun Main (M1:Bstar, M2:Bstar, l:int) : bool = {
    var r : bool;
    
    L = empty_map();
    r = A1(M1, M2, l);
    return r;
  }
}

equiv G1_GRF : G1.Main ~ G_RF.Main : ={M1,M2} /\ { l{1} == l{2}-1 } ==> ={res}
 inline {2};;
 derandomize;;
 wp;;
 rnd;;
 trivial;;
 save;;

/*
claim G1_GRF : G1.Main[ res ] == G_RF.Main[ res ] using G1_GRF;;
*/


game G_h = {
  var K : bitstring{c}

  fun g (m:B) : bitstring{c} = {
    return h(K, m);
  }

  fun A1 (M1:Bstar, M2:Bstar, l:int) : bool = {
    var m1 : int;
    var a, a1, a2  : bitstring{c};
 
    m1 = length(M1);
    a = g(head(drop(l-1,M2)));              // a = g(M2[l])
    a1 = hstar(a, drop(l, take(m1, M2)));   // a1 = foldl h g(M2[l]) M2[l+1..m1]
    a2 = hstar(a1, drop(m1, M2));           // a2 = foldl h a1 M2[m1+1..m2]
  
    return (a1 == a2);  
  }

  fun Main (M1:Bstar, M2:Bstar, l:int) : bool = {
    var r : bool;
    
    K = {0,1}^c;
    r = A1(M1, M2, l);
    return r;
  }
}

/* TODO: prove these axioms in Coq */
axiom head_drop_take :
 forall (M:Bstar, m:int, n:int).
 { n < length(M) && n < m} =>
 { head(drop(n, take(m, M))) == head(drop(n, M)) }

axiom head__drop :
 forall (M:Bstar, n:int).
 { n < length(M) } =>
 { head(drop(n, M)) :: drop(n + 1, M) == drop(n, M) }

axiom length_take :
 forall (M:Bstar, n:int).
 { n <= length(M) } => { length(take(n, M)) == n }


equiv G1_Gh : G1.Main ~ G_h.Main :	
 ={M1,M2} /\ { l{2} == l{1} + 1 } /\ 
 { 1 <= l{2} && l{2} <= length(M1{2}) && length(M1{2}) < length(M2{2}) } ==> 
 ={res}
 inline {2};;
 derandomize;;
 wp;;
 rnd;;
 trivial;;
 save;;

/*
claim G1_Gh : G1.Main[ res ] == G_h.Main[ res ] using G1_Gh;;
*/

/*** END Claim 3.5 ***/


/*** BEGIN Claim 3.6 ***/

/* TODO: use 'where' clause to factor code in game definitions */
game G_RF2 = {
  var L : (B, bitstring{c}) map
  
  fun g (m:B) : bitstring{c} = {
    var x : bitstring{c} = {0,1}^c;
    if (!in_dom(m, L)) { L[m] = x; };
    return L[m];
  }

  fun A2 (M1:Bstar, M2:Bstar) : bool = {
    var m1 : int;
    var a, a1, a2  : bitstring{c};
    var y : B;
  
    m1 = length(M1);
    a = g(head(drop(m1, M2)));             // a = g(M2[m1+1])
    a2 = hstar(a, drop(m1 + 1, M2));       // a2 = foldl h a M2[m1+2..m2]

    y = {0,1}^b \ head(drop(m1, M2)) :: [];
    a1 = g(y);
    
    return (h(a2, y) == a1);
  }

  fun Main (M1:Bstar, M2:Bstar) : bool = {
    var r : bool;
    
    L = empty_map();
    r = A2(M1, M2);
    return r;
  }
}


game G_RF2' = {
  fun Main (M1:Bstar, M2:Bstar) : bool = {
    var m1 : int;
    var a, a1, a2  : bitstring{c};
    var y : B;
    
    m1 = length(M1);
    a = {0,1}^c;
    a2 = hstar(a, drop(m1 + 1, M2));

    y = {0,1}^b \ head(drop(m1, M2)) :: [];
    a1 = {0,1}^c;
    return (h(a2,y) == a1);  
  }
}

equiv RF2_RF2' : G_RF2.Main ~ G_RF2'.Main : ={M1, M2} ==> ={res}
inline;; wp;;
app 9 3 ={m1,a,a2,M2} /\ { M2_0{1} == M2{2} } /\
        (forall (m:B). { in_dom(m,L{1}) == (m == head(drop(m1{1},M2{1}))) });;
derandomize;; wp;; rnd;; trivial;;
app 1 1 ={m1,a2,y,M2} /\ { !(in_dom(y{1}, L{1})) };;
rnd;; trivial;;
rnd;; trivial;;
save;;

/*
claim Pr_RF2_RF2' : G_RF2.Main [ res ] == G_RF2'.Main [ res ] using RF2_RF2'
*/

claim Pr_RF2 : G_RF2'.Main [ res ] == 1%r / (2^c)%r
 compute;;


game G_h2 = {
  var K : bitstring{c}

  fun g (m:B) : bitstring{c} = {
    return h(K, m);
  }

  fun A2 (M1:Bstar, M2:Bstar) : bool = {
    var m1 : int;
    var a, a1, a2  : bitstring{c};
    var y : B;
  
    m1 = length(M1);
    a = g(head(drop(m1, M2)));             // a = g(M2[m1+1])
    a2 = hstar(a, drop(m1 + 1, M2));       // a2 = foldl h a M2[m1+2..m2]

    y = {0,1}^b \ head(drop(length(M1), M2)) :: [];
    a1 = g(y);
    
    return (h(a2, y) == a1);
  }

  fun Main (M1:Bstar, M2:Bstar) : bool = {
    var r : bool;
    
    K = {0,1}^c;
    r = A2(M1, M2);
    return r;
  }
}

prover "alt-ergo";;

/* TODO: add Boolean implication as primitive operator */
equiv G1_Gh2 : G1.Main ~ G_h2.Main : 
 ={M1,M2} /\ { l{1} == length(M1{1}) && length(M1{2}) < length(M2{2}) } ==> 
 { !res{1} || res{2} }
inline{2};;
app 2 4 { a{1} == K{2} && m1{1} == m1{2} && l{1} == m1{1} && 
          m1{2} == length(M1{1}) && M2{1} == M2{2} && M2{2} == M2_0{2} &&
	  length(M1{1}) < length(M2{2}) };;
wp;; rnd;; trivial;;
wp;;
pop{2} 3;;
app 0 1 { a{1} == K{2} && m1{1} == m1{2} && l{1} == m1{1} && 
          m1{2} == length(M1{1}) && M2{1} == M2{2} && M2{2} == M2_0{2} &&
	  length(M1{1}) < length(M2{2}) };;
trivial;;
case{2} : (hstar(h(K, head(drop(m1, M2 ))), drop(m1 + 1, M2)) == K);;
trivial;;
trivial;;
save;;

/*
claim Pr_Gh2 : G1.Main [ res ] <= G_h2.Main [ res ] using G1_Gh2
*/
/*** END Claim 3.6 ***/


/*** BEGIN Claim 3.7 ***/

game G_h3 = {
  var K : bitstring{c}

  fun g (m:B) : bitstring{c} = {
    return h(K, m);
  }

  fun A1 (M1:Bstar, M2:Bstar, l:int) : bool = {
    var m1 : int;
    var a, a1, a2  : bitstring{c};
 
    m1 = length(M1);
    a = g(head(drop(l-1,M2)));              // a = g(M2[l])
    a1 = hstar(a, drop(l, take(m1, M2)));   // a1 = foldl h g(M2[l]) M2[l+1..m1]
    a2 = hstar(a1, drop(m1, M2));           // a2 = foldl h a1 M2[m1+1..m2]
  
    return (a1 == a2);  
  }

  fun A2 (M1:Bstar, M2:Bstar) : bool = {
    var m1 : int;
    var a, a1, a2  : bitstring{c};
    var y : B;
  
    m1 = length(M1);
    a = g(head(drop(m1, M2)));             // a = g(M2[m1+1])
    a2 = hstar(a, drop(m1 + 1, M2));       // a2 = foldl h a M2[m1+2..m2]

    y = {0,1}^b \ head(drop(length(M1), M2)) :: [];
    a1 = g(y);
    
    return (h(a2, y) == a1);
  }

  fun A3 (M1:Bstar, M2:Bstar) : bool = {
    var l, m1 : int;
    var r : bool;

    m1 = length(M1);
    l = [1..m1 + 1];
    if (l == m1 + 1) { 
      r = A2(M1, M2); 
    } 
    else { 
      r = A1(M1, M2, l); 
    }
    return r;
  }

  fun Main (M1:Bstar, M2:Bstar) : bool = {
    var r : bool;
    
    K = {0,1}^c;
    r = A3(M1, M2);
    return r;
  }
}


game G_RF3 = {
  var L : (B, bitstring{c}) map
  
  fun g (m:B) : bitstring{c} = {
    var x : bitstring{c} = {0,1}^c;
    if (!in_dom(m, L)) { L[m] = x; };
    return L[m];
  }

  fun A1 (M1:Bstar, M2:Bstar, l:int) : bool = {
    var M  : Bstar;
    var m1 : int;
    var a, a1, a2  : bitstring{c};
 
    m1 = length(M1);
    a = g(head(drop(l-1,M2)));              // a = g(M2[l])
    a1 = hstar(a, drop(l, take(m1, M2)));   // a1 = foldl h g(M2[l]) M2[l+1..m1]
    a2 = hstar(a1, drop(m1, M2));           // a2 = foldl h a1 M2[m1+1..m2]
  
    return (a1 == a2);  
  }

  fun A2 (M1:Bstar, M2:Bstar) : bool = {
    var m1 : int;
    var a, a1, a2  : bitstring{c};
    var y : B;
  
    m1 = length(M1);
    a = g(head(drop(m1, M2)));             // a = g(M2[m1+1])
    a2 = hstar(a, drop(m1 + 1, M2));       // a2 = foldl h a M2[m1+2..m2]

    y = {0,1}^b \ head(drop(length(M1), M2)) :: [];
    a1 = g(y);
    
    return (h(a2, y) == a1);
  }

  fun A3 (M1:Bstar, M2:Bstar) : bool = {
    var l, m1 : int;
    var r : bool;

    m1 = length(M1);
    l = [1..m1 + 1];
    if (l == m1 + 1) { 
      r = A2(M1, M2); 
    } 
    else { 
      r = A1(M1, M2, l); 
    }
    return r;
  }

  fun Main (M1:Bstar, M2:Bstar, l:int) : bool = {
    var r : bool;
    
    L = empty_map();
    r = A3(M1, M2);
    return r;
  }
}
/*** END Claim 3.7 ***/


/* Lemma 3.1 */
cnst n : int

axiom n_positive : { 1 <= n }
