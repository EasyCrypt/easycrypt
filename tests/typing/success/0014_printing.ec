require Int.

axiom tutu : forall (x:int, y:int), 
   Int.(+) x y = 0.

require import Int.
require import Real.

axiom foo1 : forall (x:int, y:int), 
   Int.(+) x = Int.(+) y.

axiom foo2 : forall (x y:int), 
   (+) x = (+) y.

axiom foo3 : forall (x:int, y:int), 
   (+) x = (+) y.

axiom foo : forall (x:int, y:int),
   `| x - y | = `| y - x |.

op toto : int -> int -> int.

axiom foo4 : forall (x:int, y:int),
  toto x y = x.

op ho : (int->int->bool) -> int -> int.

axiom foo5 : forall (x:int),
  ho (=) x = x.

op f1 (x:int, y:int) : int = x + y.

axiom foo6 : forall (x:int, y:int), -! f1 x y = x.

require import Map.
import OptionGet.

axiom foo7 : forall (x:int, y:int, m:(int,int)map),
   m.[x<-y] = m.

axiom foo8 : forall (x y:int, m:(int,int)map),
   m.[x<-y].[x] = Some y.

op do_m : ('a,'b)map -> ('a,'b) map.

axiom foo9 : forall (x:int, y:int, m:(int,int)map),
   (do_m m).[x<-y].[x] = Some y.


