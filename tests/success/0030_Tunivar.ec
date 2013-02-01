op fst : ('a * 'b) -> 'a.  (* FIXME NOTATION 'a * 'b -> 'a *)
op snd : ('a * 'b) -> 'b.

op dprod : ('a distr, 'b distr) -> ('a * 'b) distr.

op in_supp : ('a, 'a distr) -> bool.

axiom supp_def : forall (d1:'a distr, d2:'b distr, p: _), 
      in_supp(p,dprod(d1,d2)) <=> in_supp(fst(p),d1) && in_supp(snd(p), d2).