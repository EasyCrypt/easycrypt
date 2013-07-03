require import Int.
module type Orcl = { 
  fun o (x:int) : int 
}.

module type Adv (O:Orcl) = {
 fun a (x:int) : int 
}.

theory TO.
module O1 = { 
  var count : int
  fun o (x:int) : int = {
    count = count + x;
    return count;
  }
}.
end TO.

section.

  local module A : Orcl {O1}.
 