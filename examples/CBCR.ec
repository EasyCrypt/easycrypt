(* 
** We prove that Cipher Block Chaining mode with a random 
** initialization vector (CBC$) is IND-CPA secure
** under the assumption that the underlying block cipher E 
** is a prf 
*)

(* We first develop a theory of arrays,
** ideally we could include this in the EasyCrypt prelude and
** add sugar syntax
*)
type 'a array.

op length : 'a array -> int.

op make : (int,'a) -> 'a array. 

op [~>] : ('a array, int) -> 'a as aget.

op [<~] : ('a array, int * 'a) -> 'a array as aset.

axiom length_pos : forall (t:'a array), 0 <= length(t).

axiom length_make : forall (a:'a, len:int),
  0 <= len => length(make(len,a)) = len.

axiom length_aset : forall (t : 'a array, i:int, a:'a),
  length(t <~ (i,a)) = length(t).

axiom aget_aset_same : forall (t:'a array, i:int, a:'a),
  0 <= i => i < length(t) => (t <~ (i,a)) ~> i = a.

axiom aget_aset_diff : forall (t:'a array, i,j:int, a:'a),
  i <> j => ((t <~ (i,a)) ~> j) = (t ~> j).

(** Block cipher *)
cnst k, l : int.

axiom l_pos : 0 <= l.

type key   = bitstring{k}.

type block = bitstring{l}.

op E : (key,block) -> block.

(*
** A message is an array of blocks. We do not fix the length
** of the array.
** An alternative formulation will be to model messages as bitstrings
** of arbitrary length and give a function mapping messages to arrays
*)

type message = block array.

type cipher  = block array.

(*
** We use a definition of CPA where the adversary has access 
** to an LR oracle and can make more than one query 
*)

adversary A() : bool { (message, message) -> cipher }.

(*
** q is the maximun number of block cipher queries 
** (made by the LR oracle) allowed in game CPA 
*)

cnst q : int.
axiom q_pos : 0 <= q.

game CPA = {
  fun KG () : key = {
    var Ke : key = {0,1}^k;
    return Ke;
  }
  
  fun Enc(Ke:key, m:message) : cipher = {
    var p : block;
    var c : cipher = make(length(m)+1,bs0_l);
    var i : int = 0;
    c = c <~ (i, {0,1}^l);
    while (i < length(m)) {
      p = (c ~>(i)) ^^ (m~>i);
      i = i + 1;
      c = c <~ (i, E(Ke,p));
    }
    return c;
  }

  (* LR oracle :
  ** rejects a query if the size of messages differ 
  ** or if number of block cipher queries made so far is 
  ** greater or equal than q
  *)
  
  var b : bool
  var K : key
  var count : int

  fun LR(m0,m1:message) : cipher = {
    var cb : cipher;
    if (length(m0) = length(m1) && count + length(m0) <= q) {
      cb = Enc(K, b ? m0 : m1);
      count = count + length(m0);
    } else {
      cb = make(0,bs0_l);
    }
    return cb;
  }
  
  abs A = A {LR}

  fun Main () : bool = {
    var b' : bool;
    K = KG();
    b = {0,1};
    count = 0;
    b' = A ();
    return b = b';
  } 
}.

(*
** First transition: we transform game CPA into
**  game PRF0, i.e. we build an adversary B against the
**  PRF-security of E.
**
**  Import points are:
**  - B does not have access to K
**  - B can make queries to a block cipher oracle
*)

game PRF0 = {
  var K : key
 
  fun BC (bl:block) : block = {
    var be : block;
    be = E(K,bl);
    return be;
  }

  (** Definition of adversary B *)
  var b : bool
  var count : int

  fun LR(m0,m1:message) : cipher = {
    var c : cipher;
    var p,ci : block;
    var m : message;
    var i : int;
    
    if (length(m0) = length(m1) && count + length(m0) <= q) {
      m = b ? m0 : m1;
      c =  make(length(m0)+1,bs0_l);
      i = 0;
      c = c <~ (i, {0,1}^l);
      while (i < length(m0)) {
        p = (c ~>i) ^^ (m~>i);
        ci = BC(p);
        i = i + 1;
        c = c <~ (i, ci);
      } 
      count = count + length(m0);
    } else {
      c = make(0,bs0_l);
    }
    return c;
  }
  
  abs A = A {LR}

  fun B () : bool = {
    var b' : bool;
    b = {0,1};
    count = 0;
    b' = A ();
    return b = b';
  }

  fun Main () : bool = {
    var d : bool;
    K = {0,1}^k;
    d = B ();
    return d;
  } 
}.

game PRF1 = PRF0 
   var L : (block,block) map

   where BC = {
     if (!in_dom(bl,L)) { L[bl] = {0,1}^l;}
     return L[bl];
   }

   and Main = {
     var d : bool;
     L = empty_map;
     d = B ();
     return d;
   }.

equiv CPA_PRF0_LR : CPA.LR ~ PRF0.LR : ={m0,m1,K,b,count} ==> ={res,K,b,count}.
proof.
 if;[ | trivial].
 inline Enc;wp.
 while : ={m,c,i} && Ke{1} = K{2} && length(m{1}) = length(m0{2}).
   inline BC;trivial.
 derandomize;trivial.
save.

equiv CPA_PRF0 : CPA.Main ~ PRF0.Main : true ==> ={res}.
proof.
 inline B, KG;wp.
 call (={K,b,count}) using CPA_PRF0_LR.
 trivial.
save.

claim Pr_CPA_PRF0 : CPA.Main[res] = PRF0.Main[res]
using CPA_PRF0.

claim claim1 :
  | CPA.Main[res] - 1%r/2%r | <=
  | PRF0.Main[res] - PRF1.Main[res] | + | PRF1.Main[res] - 1%r/2%r |.

unset Pr_CPA_PRF0.

(* Second step *)

game G1 = PRF1 
  var bad : bool

  where LR = {
    var c : cipher;
    var p,ci : block;
    var m : message;
    var i : int;
    
    if (length(m0) = length(m1) && count + length(m0) <= q) {
      m = b ? m0 : m1;
      c =  make(length(m0)+1,bs0_l);
      i = 0;
      ci = {0,1}^l;
      c = c <~ (i, ci);
      while (i < length(m0)) {
        p = (c ~>i) ^^ (m~>i);
        ci = {0,1}^l;
        if (in_dom(p,L)) { bad = true; ci = L[p]; }
        else { L[p] = ci;}
        i = i + 1;
        c = c <~ (i, ci);
      } 
      count = count + length(m0);
    } else {
      c = make(0,bs0_l);
    }
    return c;
  }
  and Main = {
     var d : bool;
     bad = false;
     L = empty_map;
     d = B ();
     return d;
   }.

equiv PRF1_G1_LR : PRF1.LR ~ G1.LR : ={m0,m1,b,count,L} ==> ={res,b,count,L}.
proof.
 if; [wp | trivial].
 while: ={m0,m,c,i,L}.
   inline BC; derandomize; trivial.
 derandomize; trivial.
save.

equiv PRF1_G1 : PRF1.Main ~ G1.Main : true ==> ={res} 
by auto (={b,count,L}).

claim PR_PRF1_G1 : PRF1.Main[res] = G1.Main[res]
using PRF1_G1.


(* Step 3: we apply the Fundamental Lemma *)
game G2 = {
  var b, bad : bool
  var count : int
  var S : block list

  fun LR(m0,m1:message) : cipher = {
    var c : cipher;
    var p,ci : block;
    var m : message;
    var i : int;
    
    if (length(m0) = length(m1) && count + length(m0) <= q) {
      m = b ? m0 : m1;
      c =  make(length(m0)+1,bs0_l);
      i = 0;
      ci = {0,1}^l;
      c = c <~ (i, ci);
      while (i < length(m0)) {
        p = (c ~>i) ^^ (m~>i);
        if (mem(p,S)) { bad = true; }
        S = p :: S;
        ci = {0,1}^l;
        i = i + 1;
        c = c <~ (i, ci);
      } 
      count = count + length(m0);
    } else {
      c = make(0,bs0_l);
    }
    return c;
  }
  
  abs A = A {LR}

  fun Main () : bool = {  
    var b': bool;
    bad = false;
    S = [];
    b = {0,1};
    count = 0;
    b' = A ();
    return b = b';
  }
}.

equiv G1_G2_LR : G1.LR ~ G2.LR : 
  !bad{1} && ={m0,m1,bad,count,b} && 
  forall (p:block), in_dom(p,L{1}) <=> mem(p,S{2})
  ==>
  ={bad} && 
  (!bad{1} => 
     ={res,count,b} && 
     forall (p:block), in_dom(p,L{1}) <=> mem(p,S{2})).
proof.
  if; [wp | trivial].
  while: ={i,m0,m,bad} && (!bad{1} => ={c} &&  
         forall (p:block), in_dom(p,L{1}) <=> mem(p,S{2})).
    swap{2} 4 -2; trivial. 
  derandomize; trivial. 
save.

equiv G1_G2 : G1.Main ~ G2.Main : true ==> ={bad} && (!bad{1} => ={res})
by auto upto (bad) with 
   (={count,b} && forall (p:block), in_dom(p,L{1}) <=> mem(p,S{2})) 
   using G1_G2_LR.

claim Pr_G1_G2 : | G1.Main[res] - G2.Main[res] | <= G2.Main[bad]
using G1_G2.

(* We have to prove that 
    1)    G2.Main[res] = 1/2 
    2)    G2.Main[bad] <= q^2/2^l
   We start by 1, we simply remove the dependence to b in LR.
   This is possible, since we do not care about bad
*)

game G2' = G2 
   remove S, bad

   where  LR = {
    var c : cipher;
    var ci : block;
    var i : int;
    
    if (length(m0) = length(m1) && count + length(m0) <= q) {
      c =  make(length(m0)+1,bs0_l);
      i = 0;
      ci = {0,1}^l;
      c = c <~ (i, ci);
      while (i < length(m0)) {
        ci = {0,1}^l;
        i = i + 1;
        c = c <~ (i, ci);
      } 
      count = count + length(m0);
    } else {
      c = make(0,bs0_l);
    }
    return c;
  }

  and Main = {
    var b': bool;
    count = 0;
    b' = A ();
    b = {0,1};
    return b = b';
  }.   

equiv G2_G2'_LR : G2.LR ~ G2'.LR : ={m0,m1,count} ==> ={res,count}.
proof.
  if; [ wp | trivial].
  while: ={m0,i,c}; trivial.
save.

equiv G2_G2' : G2.Main ~ G2'.Main : true ==> ={res,count}
by auto (={count}).
  
claim Pr_G2_G2' : G2.Main[res] = G2'.Main[res]
using G2_G2'.

claim Pr_G2'_aux : G2'.Main[res] <= 1%r/2%r
compute.

(* 
** The following does not succeed because we are not able 
** to prove that the function is lossless due to the while loop in LR 
*)
claim Pr_G2' : G2'.Main[res] = 1%r/2%r
admit.

claim claim2 :
  | CPA.Main[res] - 1%r/2%r | <=
  | PRF0.Main[res] - PRF1.Main[res] | + G2.Main[bad].

unset Pr_G2'_aux, Pr_G2', G2_G2', PRF1_G1, claim1.

(* We now bound the probability of bad in G2 *)

game G3 = {
  var b, bad : bool
  var count : int
  var S : block list

  fun sample_p () : block = {
    var p:block;
    if (length(S) < q) { 
      p = {0,1}^l;
      if (mem(p,S)) { bad = true; }
      S = p :: S;
    } else { 
      p = bs0_l;
    }
    return p;
  }

  fun LR (m0, m1 : message) : cipher = {
    var c : cipher;
    var p,ci : block;
    var m : message;
    var i : int;
    if (length(m0) = length(m1) && count + length(m0) <= q) {
      m = b ? m0 : m1;
      c =  make(length(m0)+1,bs0_l);
      i = 0;
    
      while (i < length(m0)) {
        p = sample_p();
        ci = (p) ^^ (m~>i);
        c = c <~ (i, ci);
        i = i + 1;
      } 
      ci = {0,1}^l;
      c = c <~ (length(m0), ci);
      count = count + length(m0);
    } else {
      c = make(0,bs0_l);
    }
    return c;
  }
    
  abs A = A{LR}

  fun Main () : bool = {
    var b' : bool;
    bad = false;
    S = [];
    b = {0,1};
    count = 0;
    b' = A ();
    return b = b';
  }
}.


equiv G2_G3_LR : G2.LR ~ G3.LR :
  (={count,bad,S,b} && length(S{2}) = count{2} && count{2} <= q).
proof.
 if;[ wp | trivial].
 case : (length(m0) = 0).
   condf{1} last;condf{2} at 4;trivial.
 splitw{1} last : (i < length(m0) - 1).
 condt{2} at 4;[ trivial | ].
 app 5 7 (={m,m0,m1,count,c,b} && 
            0 <= i{1} && i{1} < length(m0{1}) && 
            length(S{2}) = count{2} + i{2} &&
            count{2} + length (m0{2}) <= q &&
            i{2} = i{1} + 1 &&
            length(c{1}) = length(m0{1}) + 1 &&
            let p' = ((c ~> i) ^^ (m ~> i)){1} in
            S{2} = p' :: S{1} &&
            (bad{2} <=> bad{1} || mem(p',S{1}))).
  inline sample_p.
  condt{2} at 4;[trivial | ].
  wp;rnd (p_0 ^^ ((m~>i){2}));trivial.
 while>> : (={c} && 
            0 <= i{1} && i{1} <= length(m0{1}) - 1 && 
            length(S{2}) = count{2} + i{2} &&
            i{2} = i{1} + 1 &&
            length(c{1}) = length(m0{1}) + 1 &&
            let p' = ((c ~> i) ^^ (m ~> i)){1} in
            S{2} = p' :: S{1} &&
            (bad{2} <=> bad{1} || mem(p',S{1}))).
   inline sample_p.
   condt{2}; wp.
   rnd (p_0 ^^ (m~>i){2});trivial.
 condt{1}; condf{1} last; trivial.
save.

equiv G2_G3 : G2.Main ~ G3.Main : true ==> ={bad} && length(S{2}) <= q
by auto (={bad,S,b,count} && length(S{2}) = count{2} && count{2} <= q).

claim Pr_G2_G3 : G2.Main[bad] = G3.Main[bad && length(S) <= q]
using G2_G3.

claim Pr_bad : G3.Main[bad && length(S) <= q] <= q%r * (q%r / (2^l)%r)
compute 2 bad, length(S). 

claim Conclusion : 
  | CPA.Main[res] - 1%r/2%r | <=
  | PRF0.Main[res] - PRF1.Main[res] | + q%r*q%r / (2^l)%r.
