game Game1 = {
 var bad : bool

  fun Main() : bool = {
    bad=false;
    return true;
  }
}.

game Game2 = {
 var bad : bool

  fun Main() : bool = {
    bad=false;
    return true;
  }
}.

prover "alt-ergo".

equiv Game1_Game2 : Game1.Main ~ Game2.Main : 
  true ==> ={bad} && (!bad{1} => ={res})
by auto.

equiv Game1_Game2' : Game1.Main ~ Game2.Main : 
  true ==> ={bad} && (!bad{2} => ={res})
by auto.

claim test1: | Game1.Main[res] - Game2.Main[res] | <= Game2.Main[bad]
using Game1_Game2.

claim test2: | Game1.Main[res] - Game2.Main[res] | <= Game2.Main[bad]
using Game1_Game2'.

claim test3: | Game1.Main[res] - Game2.Main[res] | <= Game1.Main[bad]
using Game1_Game2.

claim test4: | Game1.Main[res] - Game2.Main[res] | <= Game1.Main[bad]
using Game1_Game2'.

claim test5: Game1.Main[bad] = Game2.Main[bad]
using Game1_Game2.

claim test6: | Game1.Main[res] - Game2.Main[res] | <= Game1.Main[bad].
