theory Test.
  module M = {
    proc f() : unit = {}
  }.
end Test.

import Test.

module N = {
  proc g() : unit = {
    M.f();
  }
}.
