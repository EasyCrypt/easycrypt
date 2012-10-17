cnst k : int. (* block length *)
cnst n : int. (* state length *)

type block = bitstring{k}.
type state = bitstring{n}.
type msg   = bool list. (* arbitrary length bitstring *)

cnst IV : state.

op f     : (block, state) -> state.
op fstar : (block list, state) -> state. (* Only used at specification level *)
op pad   : msg -> block list.
op MD (m:msg) = fstar(pad(m), IV).

op coll(xy, xy':block * state) = 
  xy <> xy' && f(fst(xy),snd(xy)) = f(fst(xy'),snd(xy')).

axiom suffix_free:
  forall (m,m':msg, bl:block list), m <> m' => pad(m) <> bl ++ pad(m').

axiom fstar_nil: 
  forall (y:state), fstar([], y) = y.

axiom fstar_cons: 
  forall (x:block, y:state, xs:block list), fstar(x::xs, y) = fstar(xs, f(x,y)).

lemma hd_tl:
  forall (xs:'a list), xs <> [] => hd(xs) :: tl(xs) = xs.

(** Games *)

adversary A() : msg * msg {}.

game CR_MD = {
  abs A = A {}

  fun F(m:msg) : state = {
    var xs : block list = pad(m);
    var y : state = IV;
    while (xs <> []) {
      y  = f(hd(xs), y);
      xs = tl(xs);
    }
    return y;
  }

  fun Main() : bool = {
    var m1, m2 : msg;  
    var h1, h2 : state;  
    (m1, m2) = A();
    h1 = F(m1);
    h2 = F(m2);
    return (m1 <> m2 && h1 = h2);
  }
}.

game CR_f = {
  abs A = A {}

  fun B() : (block * state) * (block * state) = {
    var m1, m2 : msg;    
    var y1, y2 : state;
    var xs', xs1, xs2 : block list;
  
    (m1, m2) = A();
    xs1 = pad(m1);
    xs2 = pad(m2);
    y1 = IV;
    y2 = IV;
    xs' = [];
    while (length(xs2) < length(xs1)) {
      y1  = f(hd(xs1), y1);
      xs' = xs' ++ [hd(xs1)];
      xs1 = tl(xs1);
    }
    while (length(xs1) < length(xs2)) {
      y2  = f(hd(xs2), y2);
      xs' = xs' ++ [hd(xs2)];
      xs2 = tl(xs2);
    }
    while (!(coll((hd(xs1),y1), (hd(xs2), y2))) && xs1 <> []) {
      y1  = f(hd(xs1), y1);
      y2  = f(hd(xs2), y2);
      xs1 = tl(xs1);
      xs2 = tl(xs2);
    }
    return ((hd(xs1), y1), (hd(xs2), y2));
  }

  fun Main() : bool = {
    var xy1, xy2 : block * state;  
    (xy1, xy2) = B();
    return (xy1 <> xy2 && f(fst(xy1), snd(xy1)) = f(fst(xy2), snd(xy2)));
  }
}.

prover "alt-ergo".

equiv MD_f : CR_MD.Main ~ CR_f.Main : true ==> res{1} => res{2}.
inline{2}.
app 1 1 ={m1, m2}; [auto | ].

(* prove functional correctness of F *)
app 1 0 ={m1, m2} && (h1 = MD(m1)){1}; [inline | ].
sp.
while{1} >> :
 (fstar(xs, y) = MD(m1)){1} : length(xs{1}), 0; trivial.
app 1 0 ={m1, m2} && (h1 = MD(m1) && h2 = MD(m2)){1}; [inline; wp; simpl | ].
while{1}  :
   (fstar(xs, y) = MD(m2)){1} : length(xs{1}), 0; trivial.

sp.
case{2}: m1 = m2.
(* m1 = m2, just check termination *)
while{2} >> : true; trivial. 
while{2} >> : true; trivial.
while{2} >> : true : length(xs1{2}), 0; trivial.

(* m1 <> m2 *)
case{2}: length(xs2) < length(xs1).

(* length(xs2) < length(xs1) *)
while{2}>> :  (fstar(xs1, y1) = MD(m1) && 
   xs' ++ xs1 = pad(m1) && 
   length(xs2) <= length(xs1)){2} ; trivial.

condf{2}; trivial.
while{2}>> : 
  (fstar(xs1, y1) = MD(m1) && 
   fstar(xs2, y2) = MD(m2) && 
   length(xs1) = length(xs2)){2} &&
  (xs1{2} = xs2{2} => y1{2} <> y2{2}) :
  length(xs1{2}), 0; trivial.

(* length(xs1) <= length(xs2) *)
condf{2}.
while{2}>> : 
  (fstar(xs2, y2) = MD(m2) &&
   xs' ++ xs2 = pad(m2) && 
  length(xs1) <= length(xs2)){2} :
  - length(xs1{2}) + length(xs2{2}), 0; trivial.
while{2}>> : 
  (fstar(xs1, y1) = MD(m1) && 
   fstar(xs2, y2) = MD(m2) && 
   length(xs1) = length(xs2)){2} &&
  (xs1{2} = xs2{2} => y1{2} <> y2{2}) :
  length(xs1{2}), 0; trivial.
save.

claim conclusion : CR_MD.Main[res] <= CR_f.Main[res] using MD_f.
