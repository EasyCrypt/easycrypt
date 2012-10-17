
include "reals.ec".
include "laplacian.ec".

cnst j : int.	 
cnst b : int.	 
axiom b_pos: 0<=b.


cnst k : int.
axiom k_def : 0 < k.

cnst eps : real.
axiom eps_def : 0%r < eps.





axiom j_def : 0<j.

op nth : ('a list, int) -> 'a.

pred diff1(k:int,b:int,l1,l2:int list) =
  length(l1)=length(l2) && 
  forall (i:int), (i<>k => nth(l1,i) = nth(l2,i)) &&
  |nth(l1,i) - nth(l2,i)| <= b.


pop lapn : (int list, int, real) -> real list.
(* same as above but over a range *)
pop partial_lapn : (int list, int, real, int, int) -> real list.

axiom lapn_spec(l1,l2:int list, eps:real, j,b:int) : 
   x = lapn(l1,b,eps) ~ y = lapn(l2,b,eps) :
   diff1(j,b,l1,l2) ==[exp(eps);0%r]==> x = y.

axiom partial_lapn_spec(l1,l2:int list, eps:real, j,b:int, lb1,ub1,lb2,ub2:int) :
   x = partial_lapn(l1,b,eps,lb1,ub1) ~ y = partial_lapn(l2,b,eps,lb2,ub2) :
   (diff1(j,b,l1,l2)
   && 0<=lb1 && lb1<=ub1 && ub1<length(l1) && ub2<length(l2)
   && lb1=lb2 && ub1=ub2)
   ==[exp(eps);0%r]==> x = y.

(* Quick Fix.... *)
axiom partial_lapn_spec_EQ(l1,l2:int list, eps:real, j,b:int, lb1,ub1,lb2,ub2:int) :
   x = partial_lapn(l1,b,eps,lb1,ub1) ~ y = partial_lapn(l2,b,eps,lb2,ub2) :
   (diff1(j,b,l1,l2) 
   && 0<=lb1 && lb1<=ub1 && ub1<length(l1) && ub2<length(l2)
   && (j<lb1 || ub1<=j)
   && lb1 = lb2 && ub1 = ub2)
   ==[1%r;0%r]==> x = y.

op OffsetCopy : (real list, real list, real, int, int) -> real list.
axiom offsetcopy_def : forall (l,l1,l2:real list,c:real,lb,ub:int),
   l = OffsetCopy(l1,l2,c,lb,ub) => (
   length(l) = length(l1)
    &&
   (forall (i:int), 
     ((0<=i && i<lb => nth(l,i) = nth(l1,i))
     &&
     (lb<=i && i<ub => nth(l,i) = nth(l2,i)+c)
     &&
     (ub<=i && i<length(l) => nth(l,i) = nth(l1,i))))).

game statistics = {

  fun sum (l:int list) : real = {
    var s : int = 0;
    var r : real;
    var x : int = 0;
    while (x<length(l)) {
      s = s + nth(l,x);
      x = x+1;
    }
    r = lap(s,b,eps);
    return r;
  }

  fun partial_sum (l:int list,lb:int,ub:int ) : real = {
    var s : int = 0;
    var r : real;
    var x : int = lb;
    while (x<ub) {
      s = s + nth(l,x);
      x = x+1;
    }
    r = lap(s,b,eps);
    return r;
  }

  fun sum' (l:int list) : real = {
    var rl : real list;
    var x : int = 0;
    var s : real = 0%r;
    rl  = lapn(l,b,eps);
    while (x<length(rl)) {
      s = s + nth(rl,x);
      x = x+1;
    }
    return s;
  }

  fun partial_sum' (l:int list,lb:int,ub:int) : real = {
    var rl : real list;
    var x : int = lb;
    var s : real = 0%r;
    rl  = partial_lapn(l,b,eps,lb,ub);
    while (x<length(rl)) {
      s = s + nth(rl,x);
      x = x+1;
    }
    return s;
  }

  fun partial_sum'' (l:int list,lb:int,ub:int) : real list = {
    var rl : real list;
    var i : int = lb;
    var s : real list;
    rl = partial_lapn(l,b,eps,lb,ub);
    s = (hd(rl) :: []);
    while (i<length(rl)) {
      s = (hd(s) + nth(rl,i)) :: s;
      i = i+1;
    }
    return s;
  }


  fun smart_sum (l:int list, q:int) : real list = {
    var i : int = 0;
    var c : real = 0%r;
    var s : real list = [];
    var r : real;
    var x : real list;
    while (i<length(l)/q) {
      r = partial_sum(l,i*q,i*(q+1));
      x = partial_sum''(l,i*q,i*(q+1));
      s = OffsetCopy(s,x,c,i*q,i*(q+1));
      c = c+r;
      i = i+1;
    }
    return s;
  }

  fun continuous_sum (l:int list) : real list = {
    var s: int = 0;
    var r : real;
    var out: real list = [];
    var i: int = 0;
    while (i<length(l)) {
      s = s + nth(l,i);
      i = i+1;
      r = lap(s,b,eps);
      out = r :: out;
    }
    return out;
  }

  fun count (l:int list, a:int) : real = {
    var x : int = 0;
    var s : int = 0;
    var r : real;
    while (x<length(l)) {
      if (nth(l,x) = a) {
        s = s+1;
      }
      x = x+1;
    }
    r = lap(s,b,eps);
    return r;
  }

  fun continuous_count (l:int list, a:int) : real list = {
    var i : int = 0;
    var c : int = 0;
    var r : real;
    var out : real list = [];
    while (i<length(l)) {
      if (nth(l,i) = a) {
        c = c+1;
      }
      r = lap(c,b,eps);
      out = r :: out;
      i = i+1;
    }
    return out;
  }


}.

lemma aux0: forall (l:int list), 1%r <= exp (length (l)%r * eps).
lemma aux1: forall (l:int list), (exp(eps)^((length(l)-0)%r)) <=
                               exp ((length(l)%r*eps)).




equiv sumDP : statistics.sum ~ statistics.sum : 
   (diff1(j,b,l{1},l{2}) && 1<length(l{1}))
   ==[exp(eps);0%r]==> 
   ={res}.
apply : lap_spec(s{1},b,eps,s{2}).
while :
             0<=x{1}
          && ={x}
          && (x{1}<=j => ={s})
          && (j<x{1} => ( s{2}-s{1}<=b && s{1}-s{2}<=b ) )
          && diff1(j,b,l{1},l{2})
; trivial.
save.



equiv partial_sumDP : statistics.partial_sum ~ statistics.partial_sum : 
      diff1(j,b,l{1},l{2})
     && 0<=lb{1} && lb{1}<=ub{1} && ub{1}<length(l{1})
     && ={lb,ub}
     && 1<length(l{1})
   ==[exp(eps);0%r]==> 
   ={res}.
apply : lap_spec(s{1},b,eps,s{2}).
while :
             lb{1}<=x{1} && x{1}<=ub{1}
          && ={x,lb,ub}
          && (x{1}<=j => ={s})
          && ( j<x{1} => ( s{2}-s{1}<=b && s{1}-s{2}<=b ) )
          && diff1(j,b,l{1},l{2})
; trivial.
save.


equiv partial_sumEQ : statistics.partial_sum ~ statistics.partial_sum : 
      diff1(j,b,l{1},l{2})
     && 0<=lb{1} && lb{1}<=ub{1} && ub{1}<length(l{1})
     && ={lb,ub}
     && (j<lb{1} || ub{1}<=j)
     && 1<length(l{1})
    ==>  
   ={res}.
rnd.
while : 
   diff1(j,b,l{1},l{2}) 
     && 0<=lb{1} && lb{1}<=ub{1} && ub{1}<length(l{1})
     && ={lb,ub}
     && (j<lb{1} || ub{1}<=j)
     && 1<length(l{1})
     && ={s,x}
     && lb{1}<=x{1} && x{1}<=ub{1}
; auto.
save.


equiv sum'DP : statistics.sum' ~ statistics.sum' : 
    diff1(j,b,l{1},l{2})
    ==[exp(eps);0%r]==> 
   ={res}.
while 1%r, 0%r, x{1}, 0, (length(rl{1})) : 0<=x{1} && ={x,s,rl}.
apply : lapn_spec(l{1},l{2},eps,j,b); trivial.
trivial.
save.

equiv partial_sum'DP : statistics.partial_sum' ~ statistics.partial_sum' : 
        (diff1(j,b,l{1},l{2})
     && ={lb,ub}
     && 0<=lb{1} && lb{1}<=ub{1} && ub{1}<length(l{1}) && ub{2}<length(l{2}) )
    ==[exp(eps);0%r]==>
   ={res}.
(* TODO: I could apply non_app while tactic here *)
while 1%r,0%r,x{1},lb{1},length(rl{1}) :    
   lb{1}<=x{1} && ={x,s,rl}; [| trivial].
(* AUTO could search for specs... *)
apply : partial_lapn_spec(l{1},l{2},eps,j,b,lb{1},ub{1},lb{2},ub{2}); trivial.
save.


equiv partial_sum''DP : statistics.partial_sum'' ~ statistics.partial_sum'' : 
        (diff1(j,b,l{1},l{2})
     && ={lb,ub}
     && 0<=lb{1} && lb{1}<=ub{1} && ub{1}<length(l{1}) && ub{2}<length(l{2}) )
     ==[exp(eps);0%r]==>
     ={res}.
while 1%r,0%r,i{1},lb{1},length(rl{1}) :    
     lb{1}<=i{1} && ={i,s,rl}; [ |trivial].
wp.
apply : partial_lapn_spec(l{1},l{2},eps,j,b,lb{1},ub{1},lb{2},ub{2}); trivial.
save.


equiv partial_sum''EQ : statistics.partial_sum'' ~ statistics.partial_sum'' : 
        diff1(j,b,l{1},l{2})
     && ={lb,ub}
     && 0<=lb{1} && lb{1}<=ub{1} && ub{1}<length(l{1}) && ub{2}<length(l{2})
     && (j<lb{1} || ub{1}<=j)
    ==> ={res}.
while :
   diff1(j,b,l{1},l{2})
   && ={lb,ub}
   && 0<=lb{1} && lb{1}<=ub{1} && ub{1}<length(l{1}) && ub{2}<length(l{2})
   && (j<lb{1} || ub{1}<=j)
   && ={s,i,rl}; [ trivial | ].
wp.
apply : partial_lapn_spec_EQ(l{1},l{2},eps,j,b,lb{1},ub{1},lb{2},ub{2}); trivial.
save.

equiv trivial_partial_sum : statistics.partial_sum ~ statistics.partial_sum : ={ub,lb} ==> true. 
rnd{1};rnd{2}.
while : ={x,ub}; trivial.
save.

equiv trivial_partial_sum'' : statistics.partial_sum'' ~ statistics.partial_sum'' : ={lb} ==> true. 
while{1} : true; trivial.
while{2} : true; trivial.
save.

equiv smart_sumDP : statistics.smart_sum ~ statistics.smart_sum : 
   (diff1(j,b,l{1},l{2})
     && length(l{1}) = 16 && q{1} = 4 && length(l{1}) = length(l{2}) && q{1} = q{2} )
    ==[exp(eps+eps);0%r]==>
   ={res}.
while i->1%r,exp(eps+eps),i{1},0,4 : 
   ={s,i,c,q} 
   && diff1(j,b,l{1},l{2})
   && 0<=i{1} 
   && 0<=q{1}
   && length(l{1}) = 16 && q{1} = 4 && length(l{1}) = length(l{2}) 
   : j<i*q , j<i*q
; [trivial | wp | wp | wp ].
(* goal: pt1 stable *)
call using partial_sum''EQ.
call using partial_sumEQ.
trivial.
(* goal: neg pt1 holds at pre, neg pt1 holds at post *)
(* //contradictory case of third premise *)
(* //pRHL;; //pRHL doesn't handle asserts (\* TODO: fix this *\) *)
(* // non contradictory case of third premise *)
case : j<(i+1)*q.
call using trivial_partial_sum''. 
call using trivial_partial_sum. 
trivial.
call using partial_sum''EQ.
call using partial_sumEQ.
trivial.
(* // forth premise. *)
call using partial_sum''DP.
call using partial_sumDP.
timeout 10.
trivial.
save.



equiv continuous_sumDP : 
  statistics.continuous_sum ~ statistics.continuous_sum : 
   ( diff1(j,b,l{1},l{2}) && 
   1<length(l{1}) && 
   length(l{2}) = length(l{1}) ) 
    ==[exp(length(l{1})%r*eps);0%r]==> 
   ={res}.
while  exp(eps),0%r,i{1},0,length(l{1}) :
           0<=i{1}
        && i{1}<=length(l{1})
        && ={i} && length(l{2}) = length(l{1})
        && 1<length(l{1})
        && ={out}
        && (i{1}<=j => ={s})
        &&  ( j<i{1} => ( s{2}-s{1}<=b && s{1}-s{2}<=b ) )
        && diff1(j,b,l{1},l{2})
; [trivial | ].
wp.
apply : lap_spec(s{1},b,eps,s{2}); trivial.
save.





equiv countDP : statistics.count ~ statistics.count :
   diff1(j,b,l{1},l{2}) &&
   1<length(l{1}) && 
   ={a} 
    ==[exp(eps);0%r]==>
   ={res}.
apply : lap_spec(s{1},b,eps,s{2}).
while : 
        0<=x{1} 
     && x{1}<=length(l{1})
     && ={x} 
     && 1<length(l{1})
     && ={a}
     && (x{1}<=j => ={s})
     &&  ( j<x{1} => ( s{2}-s{1}<=b && s{1}-s{2}<=b ) )
     && diff1(j,b,l{1},l{2})
; trivial.
save.


equiv continuous_countDP : statistics.continuous_count ~ statistics.continuous_count :
   ( diff1(j,b,l{1},l{2}) &&
   1<length(l{1}) && 
   ={a})
    ==[exp(length(l{1})%r*eps);0%r]==>
   ={res}.
while exp(eps),0%r,i{1},0,length(l{1}) : 
        0<=i{1}
     && i{1}<=length(l{1})
     && ={i} && length(l{2}) = length(l{1})
     && 1<length(l{1})
     && ={a}
     && (i{1}<=j => ={c})
     && ( j<i{1} => ( c{2}-c{1}<=b && c{1}-c{2}<=b ) )
     && diff1(j,b,l{1},l{2})
     && ={out}
; [trivial | ].
wp.
apply : lap_spec(c{1},b,eps,c{2}).
timeout 40.
trivial.
save.




claim countDP_cl : statistics.continuous_count ~ statistics.continuous_count :
   ( diff1(j,b,l{1},l{2}) &&
   1<length(l{1}) && 
   ={a})
 ==> 
   statistics.continuous_count[res] <=  exp(length(l{1})%r*eps) * statistics.continuous_count[res]



(*
claim count_count_DP_cl:  
th(l{1}) && ={a} && 
length(l{2}) = length(l{1}) => 
*)