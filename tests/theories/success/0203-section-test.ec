require import Int.
module type Orcl = { 
  proc o (x:int) : int 
}.

module type Adv (O:Orcl) = {
 proc a (x:int) : int 
}.

theory TO.
module O1 = { 
  var count : int
  proc o (x:int) : int = {
    count = count + x;
    return count;
  }
}.
end TO.

section.

  declare module A : Orcl {TO.O1}.
 
end section.
