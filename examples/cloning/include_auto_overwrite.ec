require import AllCore.
(*TODO: Pierre-Yves*)
(* If it can be made to work, would it be possible have an option for the clone include  
   that automatically overwrites when possible?
   Also we should be allowed to overwrite axioms and lemmas.*)

abstract theory Foo.
  type t.
  op op_ : t -> t -> t.
  pred pr : t.
  (*axiom a : true.*)
  type s = t -> t.
  op c = transpose op_.
  pred q (x : t)= predT x.
  (*lemma l : true by trivial.*)
end Foo.

abstract theory Bar.
  clone include Foo.
  type u.
end Bar.

abstract theory FooBar.
  clone include Foo.
  clone include Bar with
    type t <- t,
    op op_ <- op_,
    pred pr <- pr,
    (*axiom a <- a,*)
    type s <- s,
    op c <- c,
    pred q <- q
    (*, lemma l <- l*).
end FooBar.


print FooBar.
