type t1.
cnst c1 : t1.
   
theory T.

 type t.

 type t' = t * int * t1.

 type t2.

 type t3 = t2 list.

 cnst c : t.

 cnst c' : t' = (c,0,c1). 

 module type IOrcl = {
   fun o1 (x:int):int
   fun o2 (x:int):bool
 }

 module type IA (O:IOrcl) = {
    (* var x *)
    fun A1(x:int) : int { O.o1 }
    fun A2(y:int) : int { O.o1, O.o2 }
 }
 
 op add (x,y:int) = x + y.
 op [+] : (t,t) -> t as add_t.
 pop ir : int -> int. 

 pred p (x1,x2:t,y1,y2:int) = x1 = x2 && y1 = y2. 

 lemma p_refl : forall (x:t,y:int), p(x,x,y,y) by []. 

 axiom add_t_comm : forall (x,y:t), x + y = y + x. 

 module test1 = {
   var y : t'
   fun O1 (x:t) : t' = { return c'; }
   fun O2 (x:t) : t' = {
     var r : t';
     r = O1(x);
     return r;
   }
 }.

 module test (AF:IA) = {
   var w : int
   module O = { 
      fun O1 (x:int) : int = { return x; }
      fun O2 (x:int) : bool = { return true; }
   }

   module A = AF(O)
   open A

   fun Main () : bool = { 
     var x : int;
     x = A1(0);
     x = A2(0);
     return true;
   }
 }.

 declare module AF : IA.

 module test'  = {
   var w : int
   module O = { 
      fun O1 (x:int) : int = { return x; }
      fun O2 (x:int) : bool = { return true; }
   }

   module A = AF(O)
   open A

   fun Main () : bool = { 
     var x : int;
     x = A1(0);
     x = A2(0);
     return true;
   }
 }.

print test.
print test'.
end T.
print T.test.
print T.test'.

clone theory T with type t = int and cnst c = 0 and op [+] = [+] and lemma add_t_comm as T'.
(* T'.t does not exists anymore or is an allias to int ? *)
print T'.test.
print T'.test'.

clone theory T with type t = bool and type t2 = T'.t and cnst c = true as T''.
print T''.test.

print T'.test1.

module type B(O:{ fun o1: int -> int; o2 : fun o2:int -> bool } (* not the good syntaxe ? *) = {
  fun B1(x:int) : int {O.o1}
  fun B2 (y:int) : int {O.o1,O.o2}
}

clone theory T with type t = int and cnst c = 0 and
 module AF(O:T.IO) = { 
   var x : int 
   var y : int
   var z : int
   module B = B (O)
   fun F(x1:int) : int = { return 0; }
   fun A1 (x1:int) : int = {
     var r : int;
     r = o1(x1);
     return 0;
   }
   fun A2 (x1:int) : int = {
     z = F(x1);
     return 0;
   }
  }.

print D_test.

(** Remarque : Il serait bien de pouvoir exprimer dans un module (un game) quelle partie 
    represente l'adversaire est quelle partie le reste du jeu. Pour le moment la syntaxe des
    module ne le permet pas, Ou alors il faut faire des foncteurs de maniere systematique *)

