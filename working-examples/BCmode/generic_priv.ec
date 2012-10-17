
include "array.ec".

(** Specific part of the scheme *)

include "signature.ec".

(** Generic part of the sheme, i.e. the template *)

include "generic_game.ec". 

game PRF1 = PRP1
   where BC = {
     var be : block = {0,1}^n;
     if (length(LB) < max_call) {
       if (!in_dom(bl,BCm)) { 
         if (mem(be,LB)) { bad_prp = true; }
         BCm[bl] = be;
       } else { 
         be = BCm[bl]; 
       }
       LB = be :: LB;
     } else {
       be = bs0_n;
     }
     return be;
   }
   and Main = {
     var d : bool;
     BCm = empty_map;
     LB = [];
     bad_prp = false;
     d = B ();
     return d;
   }.
  
timeout 2.

equiv CPA_PRP0_LR : 
  CPA.LR ~ PRP0.LR : 
    (={b,p,count,global_secret} && K{1} = (SK{2},OK{2}) && 
    length(LB{2}) <= sg + count{2} + p{2} * sl && 
    bounded(0,p{2},q) && bounded(0,count{2},sigma)).
 if;[ | trivial].
 inline Enc;wp.
 while : ={c,j,nc,sec,inter} && m{1} = Mp{2} && sk{1} = SK{2} && 
    length(m{1}) = length(m0{2}) &&
    (length(LB) <= sg + count + (p+1) * sl + j){2} && 
    bounded(0,j{2},length(m0{2})) &&
     bounded(0,p{2}+1,q) && bounded(0,count{2}+ length(m0{2}),sigma).
   inline BC;trivial.
 while : ={k,nc,sec} && sk{1} = SK{2} &&
    (length(LB) <= sg + count + p * sl + k){2} && 
     bounded(0,k{2},sl) &&
     bounded(0,p{2}+1,q) && bounded(0,count{2}+ length(m0{2}),sigma).
   inline BC;trivial.
 trivial.
save.


equiv CPA_PRP0 : CPA.Main ~ PRP0.Main : true ==> ={res}.
  inline B, KG;wp.
  call (={b,p,count,global_secret} && K{1} = (SK{2},OK{2}) && 
        length(LB{2}) <= sg + count{2} + p{2} * sl && 
         bounded(0,p{2},q) && bounded(0,count{2},sigma)).
  while : ={k,global_secret} && sk{1} = SK{2} && (length(LB) <= k){2} && 
     (length(LB) <= sg){2}.
   inline BC;trivial.
  swap{2} 3 1;trivial.
save.

claim Pr_CPA_PRP0 : CPA.Main[res] = PRP0.Main[res]
using CPA_PRP0.

claim claim1 :
  | CPA.Main[res] - 1%r/2%r | <=
    | PRP0.Main[res] - PRP1.Main[res] | + 
    | (PRP1.Main[res] - PRF1.Main[res])| + |(PRF1.Main[res] - 1%r/2%r) |.

unset Pr_CPA_PRP0.

(* Second step : we apply the prp/prf switching lemma *)

equiv PRP1_PRF1_BC_true : PRP1.BC ~ PRF1.BC : 
     ={bad_prp} && bad_prp{1}
   ==>
     ={bad_prp} && bad_prp{1}.
wp;rnd{1};rnd;trivial.
save.

equiv PRP1_PRF1_BC : PRP1.BC ~ PRF1.BC : 
     ={bad_prp} && !bad_prp{1} && ={bl,BCm,LB}
   ==>
     ={bad_prp} && (!bad_prp{1} => ={res,BCm,LB}).
wp;rnd{1};rnd;trivial.
save.

equiv PRP1_PRF1_LR : PRP1.LR ~ PRF1.LR :   
   !bad_prp{1} && ={bad_prp,m0,m1,b,BCm,LB,count,p,OK,global_secret}
       ==>
   ={bad_prp} && (!bad_prp{1} => ={res,b,BCm,LB,count,p,OK,global_secret}).
if;[ wp | trivial ].
while : ={m0,nc,bad_prp,j} && (!bad_prp{1} => ={BCm,LB,sec,Mp,inter,c}).
  wp.
  case : bad_prp.
    call using PRP1_PRF1_BC_true;trivial.
  call using PRP1_PRF1_BC;trivial.
while : ={m0,nc,bad_prp,k} && (!bad_prp{1} => ={BCm,LB,sec}).
  wp.
  case : bad_prp.
    call using PRP1_PRF1_BC_true;trivial.
  call using PRP1_PRF1_BC;trivial.
trivial.
save.

equiv PRP1_PRF1 : PRP1.Main ~ PRF1.Main : true ==>
     ={bad_prp} && (!bad_prp{1} => ={res}).
inline B;wp.
call upto (bad_prp)
  with (={b,BCm,LB,count,p,OK,global_secret})
  using PRP1_PRF1_LR.
while : ={bad_prp,k} && (!bad_prp{1} => ={BCm,LB,global_secret}).
  wp.
  case : bad_prp.
    call using PRP1_PRF1_BC_true;trivial.
  call using PRP1_PRF1_BC;trivial.
trivial.
save.

claim Pr_PRP1_PRF1 : | PRP1.Main[res] - PRF1.Main[res] | <= PRF1.Main[bad_prp]
using PRP1_PRF1.

(* We bound the probability of bad_prp *)
equiv PRF1_PRF1_B : PRF1.BC ~ PRF1.BC :
   (={bad_prp,BCm,LB} && (length(LB{2}) <= max_call))
by auto (true). 

equiv PRF1_PRF1 : PRF1.Main ~ PRF1.Main : 
  true ==> ={bad_prp} && length(LB{2}) <= max_call.
inline B.
auto (={bad_prp,BCm,LB,count,p,global_secret,b,OK} && length(LB{2}) <= max_call).
eqobs_in (={bad_prp,BCm,LB})
         ((length(LB{2}) <= max_call))
         (={bad_prp,BCm,LB,count,p,global_secret,b,OK}).
trivial.
save.

claim Pr_PRF1_bad_prp : 
   PRF1.Main[bad_prp] = PRF1.Main[bad_prp && length(LB) <= max_call]
using PRF1_PRF1.

claim Pr_PRF1_bad_prp_bound :  
  PRF1.Main[bad_prp && length(LB) <= max_call] <=
      max_call%r * ((max_call - 1)%r / (2^n)%r)
compute 3 (bad_prp), (length(LB)). 

claim claim2 :  | CPA.Main[res] - 1%r/2%r | <=
    | PRP0.Main[res] - PRP1.Main[res] | +  (max_call)%r * ((max_call - 1)%r / (2^n)%r) +
    | PRF1.Main[res] - 1%r/2%r |.
unset claim1, Pr_PRF1_bad_prp_bound, Pr_PRF1_bad_prp, Pr_PRP1_PRF1.

(* Step 3 : we inline BC, we introduce the bad event *)

game G1 = {
  var global_secret : secret
  var p : int
  var b : bool
  var OK : okey
  var count : int
  var BCm : (block,block)map
  var bad : bool

  fun LR(m0, m1 : message) : cipher = {
    var cb : cipher;
    var nc, rnc:nonce;
    var sec : secret;
    var Mp : message;
    var c : block array;
    var E,X,C : block;
    var inter : block list;
    var j,k : int;
    var aux,aux' : block;

    if (length(m0) = length(m1) && p < q && count + length(m0) <= sigma) {
      Mp = b ? m0 : m1;
      c = make(length(m0), bs0_n);
      inter = [];
      j = 0;
      k = 0;
      rnc = {0,1}^n;
      nc = gen_nonce(p,rnc);
      sec = init_secret (nc, OK) ++ global_secret;
      while (k < sl) {
        aux = gen_presecret(nc,sec);
        aux' = {0,1}^n;
        if (in_dom(aux,BCm)) {
          bad = true;
          aux' = BCm[aux];
        } else {
          BCm[aux] = aux';
        }
        sec = aux' :: sec;
        k = k + 1;
      }
      while (j < length(m0)) {
        E = gen(nc,sec, inter);
        X = oper(E,Mp~>(j));
        C = {0,1}^n;
        if (in_dom(X,BCm)) {
          bad = true;
          C = BCm[X];
        } else {
          BCm[X] = C;
        }
        inter = C :: inter;
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
    var k : int;
    var aux,aux' : block;
    bad = false;
    BCm = empty_map;
    b = {0,1};
    OK = gen_okey ();
    p = 0; count = 0;
    global_secret = init_global_secret ();
    k = 0;
    while (k < sg)
    {
      aux = gen_global_presecret (global_secret);
      if (!in_dom(aux,BCm)) {
        BCm[aux] = {0,1}^n;
      }
      global_secret = BCm[aux] :: global_secret;
      k = k + 1;
    }
    b' = A ();
    return b = b';
  }
}.

equiv PRF1_G1_LR : PRF1.LR ~ G1.LR : 
    (={count,p,BCm,OK, global_secret,b} && 
       length(LB{1}) <= sg + count{1} + p{1} * sl && 
       bounded(0,p{1},q) && bounded(0,count{1},sigma)).
 if;[wp | trivial].
 while : ={m0,Mp,c,j,BCm,inter,sec,nc} && 
    (length(LB) <= sg + count + (p+1) * sl + j){1} && 
     bounded(0,j{1},length(m0{1})) &&
     bounded(0,p{1}+1,q) && bounded(0,count{1}+ length(m0{1}),sigma).
   inline BC;derandomize;trivial.
 while : ={k,BCm,nc,sec} && 
   (length(LB) <= sg + count + p * sl + k){1} && 
   bounded(0,k{1},sl) &&
   bounded(0,p{1}+1,q) && bounded(0,count{1}+ length(m0{1}),sigma).
   inline BC;derandomize;trivial.
 trivial.
save.

equiv PRF1_G1 : PRF1.Main ~ G1.Main : true ==> ={res}.
 inline B.
 auto (={count,p,BCm,OK, global_secret,b} &&  
         length(LB{1}) <= sg + count{1} + p{1} * sl && 
         bounded(0,p{1},q) && bounded(0,count{1},sigma)).
 while : ={k,global_secret,BCm} &&  (length(LB) <= k){1} && 
                 (length(LB) <= sg){1}.
   inline BC;derandomize;trivial.
 trivial. 
save.

claim PR_PRF1_G1 : PRF1.Main[res] = G1.Main[res]
using PRF1_G1.

(* Step 4: we apply upto bad *)

equiv G1_G2_LR : G1.LR ~ G2.LR : 
  !bad{1} && ={m0,m1,bad,count,p,b,OK,global_secret} && 
    forall (x:block), in_dom(x,BCm{1}) <=> mem(x,LB{2})
  ==>
  ={bad} && 
  (!bad{1} => 
     ={res,count,p,b,OK} && 
     forall (x:block), in_dom(x,BCm{1}) <=> mem(x,LB{2})).
  if;[wp | trivial].
  while : ={j,m0,Mp,nc,bad} && 
                  (!bad{1} => ={c,sec,inter} &&  
                     forall (x:block), in_dom(x,BCm{1}) <=> mem(x,LB{2})).
    swap{2} 5 -2;trivial. 
  while : ={k,nc,bad,inter} && 
                  (!bad{1} => ={sec} &&  
                     forall (x:block), in_dom(x,BCm{1}) <=> mem(x,LB{2})).
    swap{2} 4 -2;trivial. 
  trivial. 
save.

equiv G1_G2 : G1.Main ~ G2.Main : true ==> ={bad} && (!bad{1} => ={res}).
  auto upto (bad) with 
    (={count,p,b,OK,global_secret} && 
       forall (x:block), in_dom(x,BCm{1}) <=> mem(x,LB{2})) 
    using G1_G2_LR.
  while : ={global_secret,k,BCm} &&
    forall (x:block), in_dom(x,BCm{1}) <=> mem(x,LB{2}).
    derandomize;trivial.
  trivial.
save.

claim Pr_G1_G2 : | G1.Main[res] - G2.Main[res] | <= G2.Main[bad]
using G1_G2.

(* We have to 
    1)    prove that G2.Main[res] = 1/2 
    2)    then bound the probability of G2.Main[bad]
   We start by 1, we simply remove the dependence to b in LR.
*)

game G2' = G2 
  remove BCm,LB, bad, global_secret, OK
  where LR = {
    var cb : cipher;
    var nc, rnc:nonce;
    var c : block array;
    var X,C : block;
    var inter : block list;
    var j : int;
    var aux,aux' : block;

    if (length(m0) = length(m1) && p < q && count + length(m0) <= sigma) {
      c = make(length(m0), bs0_n);
      inter = [];
      j = 0;
      rnc = {0,1}^n;
      nc = gen_nonce(p,rnc);
      while (j < length(m0)) {
        C = {0,1}^n;
        inter = C :: inter;
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
  and Main = {
    var b' : bool;
    p = 0; count = 0;
    b' = A ();
    b = {0,1};  
    return b = b';
  }.

equiv G2_G2'_LR : G2.LR ~ G2'.LR : (={count,p}).
  if;[ wp | trivial].
  while : ={m0,j,c};[trivial | ].
  while{1} : ={m0,j,c};trivial.
save.

equiv G2_G2' : G2.Main ~ G2'.Main : true ==> ={res}.
  swap{2} -1.
  auto (={count,p}).
  while{1} : true; derandomize; trivial.
save.

claim Pr_G2_G2' : G2.Main[res] = G2'.Main[res]
using G2_G2'.

claim Pr_G2'_aux : G2'.Main[res] <= 1%r/2%r
compute.
(* The following does not success because we are not able 
   to prove that the function is lossless, this come from
   the while loop in LR *)
claim Pr_G2' : G2'.Main[res] = 1%r/2%r
admit.

claim claim3 :
  | CPA.Main[res] - 1%r/2%r | <=
  | PRP0.Main[res] - PRP1.Main[res] | +  
  max_call%r * ((max_call - 1)%r / (2^n)%r) + G2.Main[bad].

unset Pr_G2'_aux, Pr_G2', G2_G2', PRF1_G1, claim2.
