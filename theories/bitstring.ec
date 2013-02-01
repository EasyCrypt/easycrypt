require import int.

type bitstring.

op length : bitstring -> int.

axiom length_pos : forall (s:bitstring), 0 <= length s.

op __get : (bitstring, int) -> bool.
op __set : (bitstring, int, bool) -> bitstring.

pred [==] (s1:bitstring, s2:bitstring) = 
  length s1 = length s2 &&
  forall (x:int), 0 <= x && x < length s1 => s1.[x] = s2.[x].

axiom extentionality : forall (s1:bitstring, s2:bitstring),
   s1 == s2 => s1 = s2.
    
axiom set_length : 
  forall (s:bitstring, x:int, b:bool), length s.[x<-b] = length s.

axiom get_out : forall (s:bitstring, x:int),
  x < 0 || length s <= x =>
  s.[x] = false. 

axiom get_set_same : forall (s:bitstring, x:int, b:bool),
   0 <= x => x < length s =>
   s.[x<-b].[x] = b.

axiom get_set_diff : forall (s:bitstring, x:int, y:int, b:bool),
   x <> y =>
   s.[x<-b].[y] = s.[y].

lemma set_outofbound : forall (s:bitstring, x:int, b:bool),
   x < 0 || length s <= x =>
   s.[x<-b] = s
proof.
  intros s x b H.
  apply extentionality (s.[x<-b],s,_). 
  trivial.
save.

