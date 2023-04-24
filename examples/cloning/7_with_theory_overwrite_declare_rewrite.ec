(*TODO: Pierre-Yves: declare rewrite and hint rewrite should be overwritten as well, right? *)
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
  clone import Bar with theory Foo <- Foo.
end FooBar.

(*
Note that the hint rewrite in FooBar.Bar talks about a non existing axiom/lemma.
Could it be linked to the rewrite hang bug previously noticed in FFexistence?
*)
print FooBar.

(*TODO: Pierre-Yves: make rewrite hang to rest assured that it was the same bug.
                     Please note that the first time the rewrite hang bug manifested itself,
                     clone with theory _ <= _ was used instead of <- .*)
theory Bug.
  clone include FooBar.

  lemma eq_ : Foo.b = Foo.a.
  proof.
    by rewrite Foo.eq.
  qed.
end Bug.
