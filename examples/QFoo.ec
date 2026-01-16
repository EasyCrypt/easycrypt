require import Int.

module type QFooOT = {
   qproc foo(a : int) : int     
}.

module QFooO : QFooOT = {
   qproc foo(a : int) : int = {
       qvar x : int;
       x <- 0;
       return (a + x);
   }
}.

module type QFooT(O : QFooOT) = {
   proc main() : int
}.

section.


declare qmodule A <: QFooT.

end section.
