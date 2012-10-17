include "ake_game10.ec".


claim conclusion : 
| AKE.Main[res] - 1%r/2%r | <= 
 AKE8.Main[res] + AKE9.Main[res] + AKE10.Main[res] + AKE3.Main[test_key_reveal_collision_op(tested_session, skey, seed, LH, G)] admit.
 