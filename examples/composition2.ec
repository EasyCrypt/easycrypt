cnst p : int.
cnst n : int.
cnst s : int.
cnst r : int.


adversary A1(M:bitstring{p}) : bitstring{n}
 { 
   (bitstring{p}, bitstring{s}) -> bitstring{r}; (* H *)
   bitstring{p} -> bitstring{r}                  (* f *)
 }.

adversary A2(st:bitstring{n}, C:bitstring{s}) : bitstring{r}
 { 
   (bitstring{p}, bitstring{s}) -> bitstring{r}; (* H *)
   bitstring{p} -> bitstring{r}                  (* f *)
 }.


(* The construction H, indifferentiable from a RO *)
adversary H(M:bitstring{p}, C:bitstring{s}) : bitstring{r} 
  { bitstring{p} -> bitstring{r} }.


game CRP_Real = {
 var L_f : (bitstring{p}, bitstring{r}) map

 fun f(x:bitstring{p}) : bitstring{r} = {
   if (!in_dom(x, L_f)) {
     L_f[x] = {0,1}^r;
   }
   return L_f[x];
 }

 abs H = H {f}

 abs A1 = A1 {H, f}
 abs A2 = A2 {H, f}

 fun Main() : bool = {
   var M : bitstring{p};
   var C : bitstring{s};
   var Y, Z : bitstring{r};
   var st : bitstring{n};
   L_f = empty_map;
   M = {0,1}^p;
   st = A1(M);
   C = {0,1}^s;
   Z = A2(st,C);
   Y = H(M,C);
   return (Z = Y);
 }
}.

adversary Sim(x:bitstring{p}) : bitstring{r} 
  { (bitstring{p}, bitstring{s}) -> bitstring{r} }.

game CRP_Ideal = {
 var L_H : (bitstring{p} * bitstring{s}, bitstring{r}) map

 fun H(M:bitstring{p}, C:bitstring{s}) : bitstring{r} = {
   if (!in_dom((M,C), L_H)) {
     L_H[(M,C)] = {0,1}^r;
   }
   return L_H[(M,C)];
 }

 (* BEGIN B1 *)
 abs f1 = Sim {H}

 abs A1 = A1 {H, f1}

 fun B1(M:bitstring{p}) : bitstring{n} = {
   var st : bitstring{n};
   st = A1(M);
   return st;
 }
 (* END B1 *)

 (* BEGIN B2 *)
 abs f2 = Sim {H}

 abs A2 = A2 {H, f2}

 fun B2(st:bitstring{n}, C:bitstring{s}) : bitstring{r} = {
   var Z : bitstring{r};
   Z = A2(st,C);
   return Z;
 }
 (* END B2 *)

 fun Main() : bool = {
   var M : bitstring{p};
   var C : bitstring{s};
   var Y, Z : bitstring{r};
   var st : bitstring{n};
   L_H = empty_map;
   M = {0,1}^p;
   st = B1(M);
   C = {0,1}^s;
   Z = B2(st,C);
   Y = H(M,C);
   return (Z = Y);
 }
}.

game Real = {
 var L_f : (bitstring{p}, bitstring{r}) map

 fun f(x:bitstring{p}) : bitstring{r} = {
   if (!in_dom(x,L_f)) {
     L_f[x] = {0,1}^r;
   }
   return L_f[x];
 }

 abs H = H {f}

 (* BEGIN D(H,f) *)
 abs A1 = A1 {H, f}
 abs A2 = A2 {H, f}

 fun D() : bool = {
   var M : bitstring{p};
   var C : bitstring{s};
   var Y, Z : bitstring{r};
   var st : bitstring{n};
   M = {0,1}^p;
   st = A1(M);
   C = {0,1}^s;
   Z = A2(st,C);
   Y = H(M,C);
   return (Z = Y);
 }
 (** END D(H,f) *)

 fun Main() : bool = {
   var b : bool;
   L_f = empty_map;
   b = D();
   return b;
 }
}.

game Ideal = {
 var L_H : (bitstring{p} * bitstring{s}, bitstring{r}) map

 fun H(M:bitstring{p}, C:bitstring{s}) : bitstring{r} = {
   if (!in_dom((M,C), L_H)) {
     L_H[(M,C)] = {0,1}^r;
   }
   return L_H[(M,C)];
 }

 abs f = Sim {H}

 (* BEGIN D(H,f) *)
 abs A1 = A1 {H, f}
 abs A2 = A2 {H, f}

 fun D() : bool = {
   var M : bitstring{p};
   var C : bitstring{s};
   var Y, Z : bitstring{r};
   var st : bitstring{n};
   M = {0,1}^p;
   st = A1(M);
   C = {0,1}^s;
   Z = A2(st,C);
   Y = H(M,C);
   return (Z = Y);
 }
 (** END D(H,f) *)

 fun Main() : bool = {
   var b : bool;
   L_H = empty_map;
   b = D();
   return b;
 }
}.

prover "alt-ergo".

equiv left  : CRP_Real.Main ~ Real.Main : true ==> ={res} by auto.

equiv right : Ideal.Main ~ CRP_Ideal.Main : true ==> ={res}.
 inline{1} D; inline{2} B1, B2; wp.
 derandomize; auto; *rnd; trivial.
save.

claim Pr_left : CRP_Real.Main[res] = Real.Main[res]
 using left.

claim Pr_right : Ideal.Main[res] = CRP_Ideal.Main[res]
 using right.

claim conclusion : 
  | CRP_Real.Main[res]  - 1%r / 2%r | <= 
  | CRP_Ideal.Main[res] - 1%r / 2%r | + 
  | Real.Main[res] - Ideal.Main[res] |.
