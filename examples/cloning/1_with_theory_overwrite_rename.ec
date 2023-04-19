(*TODO: Pierre-Yves*)

(*
When doing a clone include with theory ovewrite, if the overwritten theory should
be gone before trying to add it to the current theory, not after.
The rename line should be removed and the result the same.
*)

abstract theory Foo.
  type t.
end Foo.

abstract theory Bar.
  clone import Foo.
end Bar.

abstract theory FooBar.
  clone import Foo.
  clone include Bar with theory Foo <- Foo
    rename [theory] "Foo" as "Gone".
end FooBar.

print FooBar.
