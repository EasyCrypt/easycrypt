require import Real.

module M = {var x: bool proc p()={}}.

lemma L (&m: {b:bool}): b{m}= true => Pr[M.p()@&m:true] = 1%r. 
proof. move => ->>. abort.

lemma L (&m: {b:bool}): M.x{m}= true => Pr[M.p()@&m:true] = 1%r. 
proof. fail move => ->>. abort.

lemma L: phoare[M.p{&m}: true ==> Pr[M.p()@&m:true] = 1%r] = 1%r.
proof. proc. abort.
