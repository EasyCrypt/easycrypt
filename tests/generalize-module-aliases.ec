module type T = {
  proc f(): bool
}.


module F(O1 : T, O2 : T) = {
  module M = {
    module N = {
      proc g() = {
        var r1, r2;
    
        r1 <@ O1.f();
        r2 <@ O2.f();
        return (r1, r2);
      }
    }
  }
}.

module M : T = {
  proc f() = {
    return true;
  }
}.

section.
declare module M_T1 <: T.
declare module M_T2 <: T.

module A1 = F(M_T1, M_T2).M.
module A2 = F(M_T1).

module C = M.

hoare L1: A1.N.g: true ==> true.
proof. admitted.

hoare L2: A2(C).M.N.g: true ==> true.
proof. admitted.

end section.

hoare LL1 (M1 <: T) (M2 <: T): F(M1, M2).M.N.g : true ==> true.
proof. exact (L1 M1 M2). qed.

hoare LL2 (M1 <: T): F(M1, M).M.N.g : true ==> true.
proof. exact (L1 M1 C). qed. (* The module alias C can escape the section *)

hoare LL3 (M1 <: T): F(M1, M).M.N.g : true ==> true.
proof. exact (L2 M1). qed.
