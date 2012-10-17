type message = int.
type cipher = int.

adversary A1() : message * message { message -> message; message -> message }.
adversary A2(c:cipher) : bool { message -> message; message -> message}.

cnst k : int.

game Lazy = {
  var mH : (int, int) map
  var mG : (int, int) map
  var h'  : int
  var hh' : int

  fun H(h:int) : int = {
    if (!in_dom(h, mH)) { mH[h] = [0..k]; }
    return mH[h];
  }

  fun G(g:int) : int = {
    if (! in_dom(g, mG) ) { mG[g] = [0..k]; }
    return mG[g];
  }

  abs A1 = A1 { H, G }
  abs A2 = A2 { H, G }

  fun Main() : bool = { 
    var m0, m1 : message;
    var h : int;
    var b, b' : bool;
    h' = [0..k];
    mH = empty_map;
    mG = empty_map;
    hh' = 0;
    (m0,m1) = A1();
    b = {0,1};
    h = H(h');
    b' = A2(h * (b ? m0 : m1));
    if (!in_dom(h',mH)) { hh' = [0..k]; } else { hh' = mH[h']; }
    return b = b';
  }   
}.

(* We fix set the answer of H(h') to hh', i.e eager sampling *)

game Eager = Lazy where 
   H = {
    if (!in_dom(h, mH)) { 
      if (h = h') { mH[h] = hh'; } else { mH[h] = [0..k]; }
     }
     return mH[h];
   }

   and Main = {
    var m0,m1:message;
    var h:int;
    var b,b':bool;
    h' = [0..k];
    mH = empty_map;
    mG = empty_map;
    hh' = 0;
    if (!in_dom(h',mH)){ hh' =[0..k]; } else { hh' = mH[h']; }
    (m0,m1) = A1();
    b = {0,1};
    h = H(h');
    b' = A2(h * (b ? m0 : m1));
    return b = b';
   }.

equiv Lazy_Eager : Lazy.Main ~ Eager.Main : true ==> ={mH, mG, hh', res} by
eager { if (!in_dom(h',mH)) { hh' =[0..k]; } else { hh' = mH[h']; } }.
(* Eager for H *)
 derandomize.
 case{1} : (!in_dom(h,mH) && !in_dom(h',mH) && h = h').
 trivial.
 swap{1} 1;  trivial.
save.

(* head => eq *)
trivial.

(* tail => eq *)
trivial. 
save.

(* We modify H so that h' is not stored in mH *)
game Eager1 = Eager where 
  H = {
    var res : int;
    if (h = h') { res = hh'; } 
    else {
      if (!in_dom(h,mH)) { mH[h] = [0..k]; }
      res = mH[h];
    }
    return res;
   }

  and Main = {
    var m0, m1 : message;
    var h : int;
    var b, b' : bool;
    h' = [0..k];
    mH = empty_map;
    mG = empty_map;
    hh' = [0..k];
    (m0,m1) = A1();
    b = {0,1};
    h = hh';
    b' = A2(h * (b ? m0 : m1));
    return b = b';
  }.

equiv Eager_Eager1 : Eager.Main ~ Eager1.Main : true ==> ={res} 
by auto 
 (={mG,h',hh'} && (in_dom(h',mH){1} => (mH[h'] = hh'){1}) &&
  forall (h:int),
    h <> h'{1} => (in_dom(h,mH{1}) = in_dom(h,mH{2}) && mH{1}[h] = mH{2}[h]) ).
