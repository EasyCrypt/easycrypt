module type Orcl = {
  proc f (x:int) : int 
}.

module F = { 
  var view : int
  proc f () : unit = {
    view = 1;
  } 
}.

lemma toto : forall (Or<:Orcl {F}),
   equiv [F.f ~ F.f : ={glob Or} ==> (={F.view, glob Or})].
intros Or.
proc.
 sim (: ={glob Or}) : (={F.view, glob Or}).
qed.

lemma toto1 : forall (Or<:Orcl),
   equiv [F.f ~ F.f : ={glob Or} ==> (={F.view, glob Or})].
intros Or.
proc.
 sim (: ={glob Or}) : (={F.view, glob Or}).
qed.

module Or = { 
  var x : int
}.

lemma toto2 : 
   equiv [F.f ~ F.f : ={glob Or} ==> (={F.view, glob Or})].
proof.
 sim (: ={glob Or}) / true : (={F.view, glob Or}).
qed.

lemma toto3 : 
   equiv [F.f ~ F.f : ={glob Or} ==> (={F.view, glob Or})].
proof.
 sim (: ={glob Or}) / true.
qed.

