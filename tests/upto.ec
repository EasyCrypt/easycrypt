game G1 = {
  var bad : bool

  fun Main() : bool = {
    return true;
  }
}.

game G2 = {
  var bad : bool

  fun Main() : bool = {
    return true;
  }
}.

equiv foo : 
  G1.Main ~ G2.Main : true ==> !bad{1} && !bad{2} => ={res}.
admit.
save.

equiv bar : G2.Main ~ G1.Main : true ==> !bad{1} && !bad{2} => ={res}.
admit.
save.


claim a1 : G1.Main[res] = G1.Main[res && bad] + G1.Main[res && !bad]
compute.

claim ___a1 : G1.Main[res] = G1.Main[res && bad] + G1.Main[res && !bad]
split.

claim a2 : G1.Main[res && bad] <= G1.Main[bad] 
compute.

claim a3 : G1.Main[res && !bad] <= G2.Main[res || bad]
using foo.

claim a4 : G2.Main[res || bad] <= G2.Main[res] + G2.Main[bad]
compute.

claim a5 : G1.Main[res] - G2.Main[res] <= G1.Main[bad] + G2.Main[bad].

unset a1, a2, a3, a4.

claim b1 : G2.Main[res] = G2.Main[res && bad] + G2.Main[res && !bad]
compute.

claim b2 : G2.Main[res && bad] <= G2.Main[bad] 
compute.

claim b3 : G2.Main[res && !bad] <= G1.Main[res || bad]
using bar.

claim b4 : G1.Main[res || bad] <= G1.Main[res] + G1.Main[bad]
compute.

claim b5 : G2.Main[res] - G1.Main[res] <= G1.Main[bad] + G2.Main[bad].

unset b1, b2, b3, b4.

claim final : |G1.Main[res] - G2.Main[res]| <= G1.Main[bad] + G2.Main[bad].
