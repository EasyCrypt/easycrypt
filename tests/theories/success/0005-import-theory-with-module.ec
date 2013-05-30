theory Test.
  module M = {
    fun f() : unit = {}
  }.
end Test.

import Test.

module N = {
  fun g() : unit = {
    M.f();
  }
}.
