
lemma and_intro  : forall (a b:bool), a => b => a /\ b.
lemma and_elim   : forall (a b c:bool), (a /\ b) => (a => b => c) => c.

lemma anda_intro : forall (a b:bool), a => (a => b) => a && b.
lemma anda_elim  : forall (a b c:bool), (a && b) => (a => b => c) => c.

lemma or_intro_l : forall (a b:bool), a => a \/ b. 
lemma or_intro_r : forall (a b:bool), b => a \/ b. 
lemma or_elim    : forall (a b c : bool), (a \/ b) => (a => c) => (b => c) => c.

lemma ora_intro_l : forall (a b:bool), a => a || b. 
lemma ora_intro_r : forall (a b:bool), (!a => b) => a || b. 
lemma ora_elim    : forall (a b c : bool), (a || b) => 
                         (a => c) => (!a => b => c) => c.


lemma foo : forall (a b:bool), a => b => (a /\ b) \/ b
proof.
 intros a b Ha Hb.
 apply or_introl ( (a /\ b) ,b,_).
 apply and_intro (a,b,_,_);assumption.
save.


require import int.
lemma toto : forall (x:int), x = x
proof.
intros x.
trivial.
save.

(*
module F (A:I) = {
   var x : int           
   module M = A
   module G = {
      fun g (w:int) : int = {
           k := M.f(w);
           u := A.f(w);
           return u + k + x;
        }
      fun g1 (w:int) : int = {
           r := g(w);
           return r;
        }
   }
}.

module K = F(A1)

Print K.x -->  (* K.x = F.x *)   
                var K.x = F.x : int 
Print K.M.x --> (* K.M.x = A1.x *)
                var K.M.x = A1.x : int
Print K.M --> 
Print K.G.g --> (* F(A1).G.g *)
                fun g(w:int) = { 
                  k = K.M.f(w);
                  u = A1.f(w);
                  return u+w+K.x; (* u+w+F.x *)
                }

Print K.G.g1 --> (* F(A1).G.g *)
                fun g1(w:int) = { 
                  r = K.G.g.(w); (* F(A).G.g *)
                  return r;
                }

Print F.M   --> 
            [A:I] 
            module M = A
Print F.G.g --> 
             [A:I]
             fun g(w:int) = { 
                  k = F(A).M.f(w);
                  u = A.f(w);
                  return u+w+F(A).G.x;
                }
Print F(A1).G.g -->
             fun g(w:int) = { 
                  k = F(A1).M.f(w);
                  u = A1.f(w);
                  return u+w+F(A1).G.x;



type mpath = 
   | MPcomp  of mpath * symbol
   | MPapp   of mpath * mpath list
   | MPlocal of EcIdent
   | MPtop   of path 

(* On veut subtituer un path ou un local par ca definition (MPapp) *)
(* On veut calculer la forme normal d'un path : 
   F(A1).M --> A1
   F(A1).G --> F(A1).G
*)

(* Dans EcEnv : On a simplement besoin de savoir acceder un 
   local et au path, les autres acces ce font par indirection 
*)   

type fpath = mpath * symbol

Pas l'impression que l'on a besoin d'acceder directement a M1.M2.f
On accede a M1 on Accede a M2 on accede a f
Si module applique on fait la bonne subtitution.
La ou c'est pas clair pour moi c'est le sens des foncteurs avec les variables:
F(A1).f ~ F(A2).f : F(A1).x{1} = F(A2).x{2} ==> ={res}
F(A1).f ~ F(A2).f : F.x{1} = F.x{2} ==> ={res}



   
             

forall (A:I), F(A).M.f ~ A.f

F(A).M.x = A.x ???
On a besoin d'une fonction de normalisation 
Comment assurer qu'il y a pas de clash de variables:

require int.
axiom tutu : forall (x:int, y:int),
   int.[+] x y = 0.

require import int.
require import real.
(*require import real.*)

axiom foo1 : forall (x:int, y:int), 
   int.[+] x = int.[+] y.

axiom foo2 : forall (x:int, y:int), 
   + x = + y.

axiom foo3 : forall (x:int, y:int), 
   [+] x = [+] y.

axiom foo : forall (x:int, y:int),
   | x - y | = | y - x |.

op toto : (int, int) -> int.

axiom foo4 : forall (x:int, y:int),
  toto x y = x.

op ho : (int->int->bool, int) -> int.

axiom foo5 : forall (x:int),
  ho [=] x = x.

op f1 (x:int, y:int) : int = x + y.

axiom foo6 : forall (x:int, y:int), -! f1 x y = x.

require import map.

axiom foo7 : forall (x:int, y:int, m:(int,int)map),
   m.[x<-y] = m.

axiom foo8 : forall (x:int, y:int, m:(int,int)map),
   m.[x<-y].[x] = y.

op do_m : ('a,'b)map -> ('a,'b) map.

axiom foo9 : forall (x:int, y:int, m:(int,int)map),
   (do_m m).[x<-y].[x] = y.


*)