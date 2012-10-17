include "array.ec".

(* Instanciation of the signature *)
cnst n : int.
axiom n_pos : 0 <= n.
type block = bitstring{n}.  

type nonce = block.

op gen_nonce (c:int, nc:block) = nc.

type skey. (* the type of the secret key used in the block cipher *)
type okey = int.

pop gen_skey : () -> skey.
op gen_okey () = 0.

(* [gen_skey()] is a random operator generating a new [skey]
   [gen_okey()] is a random operator generating a new [okey] *)

type secret = block list. (* the type of the secrets used in the scheme *)

op init_global_secret () = [].
cnst sg : int = 0.
lemma sg_pos : 0 <= sg.
op gen_global_presecret (s:secret) = bs0_n.

op init_secret (nc: nonce, ok:okey) = [].

cnst sl : int = 0.

lemma sl_pos : 0 <= sl.

op gen_presecret (nc:nonce, sec:secret) = bs0_n.

type intermediate = block list.

op gen (nc:nonce, sec:secret, inter:intermediate) = 
  if length(inter) = 0 then nc else hd(inter).

(* [gen(nc,s,inter)] build a new block [E_|inter|] *)

op oper (b1,b2: block) = b1 ^^ b2.

op F    : (skey, block) -> block.

(** q is the maximun number of block cipher request 
    (made by the LR oracle) allowed in the game CPA.
    so the maximun number of block cipher request (in the game CPA) is q + global_secret_F 
*)

include "generic_game.ec".

game CBCCPA = {
  var p : int
  var b : bool
  var SK : skey
  var count : int

  fun KG () : skey = {
    var kg_sk : skey;
    kg_sk = gen_skey ();
    return (kg_sk);
  }

  fun Enc (sk : skey, m : message) : cipher = {
    var c : block array;
    var nc,E,X,C : block;
    var j : int;
    c = make (length (m),bs0_n);
    j = 0;
    nc = {0,1}^n;
    E = nc;
    while (j < length (m))
    {
      X = E ^^ (m ~> j);
      C = F (sk,X);
      c = c <~ (j,C);
      E = C;
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
    b' = A ();
    return b = b';
  }
}.

equiv CBCCPA_CPA_LR : CBCCPA.LR ~ CPA.LR : 
   (={b,count,p} &&
    global_secret{2} = [] &&
    fst(K{2}) = SK{1}).
 if;[ | trivial ].
 inline Enc;wp.
 while : ={j,m,c,sk} && 
               if inter{2} = [] then E{1} = nc{2} else E{1} = hd(inter{2}).
   trivial.
 condf{2} last;trivial.
save.

equiv CBCCPA_CPA : CBCCPA.Main ~ CPA.Main : true ==> ={res}.
 auto (={b,count,p} &&
       global_secret{2} = [] &&
       fst(K{2}) = SK{1}).
 condf{2} last;inline KG;trivial.
save.

claim Pr_CBCCPA_CPA : CBCCPA.Main[res] = CPA.Main[res]
using CBCCPA_CPA.

game G3 = {
  var p,count : int
  var b,bad : bool
  var LB : block list

  fun sample_p () : block = {
    var x:block;
    if (length(LB) < sigma) { 
      x = {0,1}^n;
      if (mem(x,LB)) { bad = true;} 
      LB = x :: LB;
    } else { 
      x = bs0_n;
    }
    return x;
  }
  
  fun LR (m0, m1 : message) : cipher = {
    var cb : cipher;
    var Mp : message;
    var c : block array;
    var nc,X : block;
    var j : int;
    if (length (m0) = length (m1) && p < q && count + length (m0) <= sigma) {    
      Mp = if b then m0 else m1;
      c = make (length (m0),bs0_n);
      j = 0;
      while (j < length(m0))
      {
        X = sample_p();
        if (j = 0) {
          nc = X ^^ (Mp~>0);
        } else {
          c = c <~ (j-1,X ^^ (Mp~>j));
        }
        j = j + 1;
      }
      X = {0,1}^n;
      if (j = 0) {
        nc = X;
      } else {
        c = c <~ (j-1,X);
      }
      p = p + 1;
      cb = (nc,c);
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
    bad = false;
    LB = [];
    b = {0,1};
    p = 0;
    count = 0;
    b' = A ();
    return b = b';
  }  
}.

equiv G2_G3_LR : G2.LR ~ G3.LR : 
   (={p,count,bad,LB,b} && length(LB{2}) = count{2} && count{2} <= sigma).
 if;[ wp | trivial].
 case : (length(m0) = 0).
   derandomize;wp.
   condf{1} last;condf{1} last;condf{2} last;trivial.
 splitw{1} last : (j < length(m0) - 1).
 condt{2} last; [ trivial | ].
 app 9 6 (={Mp,m0,m1,p,count,c,nc,b} && 
            j{1} = 0 && 0 < length(m0{1}) && 
            length(LB{1}) = count{1} &&
            count{2} + length (m0{2}) <= sigma &&
            j{2} = j{1} + 1 &&
            length(c{1}) = length(m0{1}) &&
            inter{1} = [] &&
            let x = (nc ^^ (Mp ~> 0)){1} in
            LB{2} = x :: LB{1} && 
            (bad{2} <=> bad{1} || mem(x,LB{1}))).
   condf{1} last.
   inline sample_p.
   derandomize; wp.
   rnd (x_0 ^^ ((b ? m0 : m1) ~>0){2});trivial.
 while>> : (={Mp,m0,m1,p,count,c,nc,b} && 
            (j{1} = length(inter{1})) &&
            (0 < length(inter{1}) => hd(inter{1}) = (c~>(j-1)){1}) &&
            0 <= j{1} && j{1} <= length(m0{1}) - 1 && 
            length(LB{2}) = count{2} + j{2} &&
            count{2} + length (m0{2}) <= sigma &&
            j{2} = j{1} + 1 &&
            length(c{1}) = length(m0{1}) &&
            let x = (if j = 0 then nc ^^ (Mp~>0) else (c~>j-1)^^(Mp~>j)){1} in
            LB{2} = x :: LB{1} &&
            (bad{2} <=> bad{1} || mem(x,LB{1}))).
   inline sample_p.
   condt{2}.
   condf{2} at 5;[trivial | ].
   wp; rnd (x ^^ (Mp{2}~>j{2}));trivial.
 condt{1}; condf{1} last.
 trivial.
save.

equiv G2_G3 : G2.Main ~ G3.Main : true ==> ={bad} && length(LB{2}) <= sigma.
 auto (={p,count,bad,LB,b} && length(LB{2}) = count{2} && count{2} <= sigma).
 condf{1} last.
 trivial.
save.

claim Pr_G2_G3 : G2.Main[bad] = G3.Main[bad && length(LB) <= sigma]
using G2_G3.

claim Pr_bad : G3.Main[bad && length(LB) <= sigma] <= sigma%r * ((sigma-1)%r / (2^n)%r)
compute 2 bad, length(LB). 

(* This claim is proved in generic_priv.ec *)
claim claim3 : | CPA.Main[res] - 1%r/2%r | <=
    | PRP0.Main[res] - PRP1.Main[res] | +  max_call%r * ((max_call - 1)%r / (2^n)%r) +
    G2.Main[bad]
admit.

claim claim3' : | CBCCPA.Main[res] - 1%r/2%r | <=
    | PRP0.Main[res] - PRP1.Main[res] | +  sigma%r * ((sigma - 1)%r / (2^n)%r) +
    G2.Main[bad].

unset claim3, Pr_CBCCPA_CPA.

claim conclusion : | CBCCPA.Main[res] - 1%r/2%r | <=
    | PRP0.Main[res] - PRP1.Main[res] | +  
    sigma%r * ((sigma - 1)%r / (2^n)%r) +
    sigma%r * ((sigma - 1)%r / (2^n)%r).
