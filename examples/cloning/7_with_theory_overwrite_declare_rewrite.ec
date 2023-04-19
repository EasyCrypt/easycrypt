(*TODO: Pierre-Yves*)

(*
declare rewrite and hint rewrite should be overwritten as well, right?
Note that the hint rewrite in FooBar.Bar talks about a non existing axiom/lemma.
Could it be linked to the rewrite hang bug previously noticed in FFexistence?
*)

abstract theory Foo.
  type t.
  op a : t.
  op b : t.
  axiom eq : a = b.
  hint rewrite hr : eq.
end Foo.

abstract theory Bar.
  clone import Foo.
end Bar.

abstract theory FooBar.
  clone import Foo.
  clone import Bar with theory Foo <- Foo
    rename [theory] "Foo" as "Gone".
end FooBar.

print FooBar.
