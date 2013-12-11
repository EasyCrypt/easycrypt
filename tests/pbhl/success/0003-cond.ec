require import Logic.
require import Distr.
require import Bool.
require import Real.

type t.

op b1 : bool.
op b2 : bool.
op e1 : t.
op e2 : t.

module M = {
  var x, y : t
  proc f () : unit = {
    if (b1) {
      x = e1;
    } else {
      x = e2;
    }
  }
}.

lemma foo : bd_hoare [M.f : (b1 => M.y=e1) && (b2 => M.y=e2) && (b1||b2) ==> 
                         M.x=M.y ] = (1%r).
proof.
 proc.
 if; wp; skip; smt.
qed.


require import Distr.
require import Fset.
clone import Dexcepted.

module M2 = {
  var b,b' : bool
  proc f () : unit = {
    if (b) {
      b' = false;
    } else {
      b' = $ {0,1}\(single b);
    }
  }
}.


lemma test : bd_hoare [M2.f : true ==> M2.b \/ M2.b' ] = (1%r).
proc.
if.
wp; skip; trivial.
rnd;skip. 
simplify. intros &hr H.
cut -> : M2.b{hr} = false;[ smt|simplify]. 
rewrite - (lossless_restr ({0,1}) (single M2.b{hr}) _ _). 
smt.
delta cpMem; simplify.
cut -> : (fun x, mem x (single M2.b{hr})) = ( (=) M2.b{hr}); [apply fun_ext;smt|].
smt.
cut -> : M2.b{hr} = false;[ smt|simplify;smt]. 
qed.

