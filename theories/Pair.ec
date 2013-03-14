op fst (p:'a * 'b) : 'a = 
  let (a,b) = p in a.

op snd (p:'a * 'b) : 'b = 
  let (a,b) = p in b.