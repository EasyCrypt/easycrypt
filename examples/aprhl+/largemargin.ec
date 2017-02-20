(* -------------------------------------------------------------------- *)
require import Int IntExtra Real RealExtra Ring.
require import Distr List Aprhl StdRing StdOrder StdBigop.
(*---*) import IntID IntOrder RField RealOrder.


(* -------------------------------------------------------------------- *)
op eps: { real | 0%r <= eps } as ge0_eps.

hint exact : ge0_eps.

(* -------------------------------------------------------------------- *)
type db.
type query = db -> int.
op evalQ : query -> db -> int.
op nullQ : query.


(* -------------------------------------------------------------------- *)
pred adj: db & db.

axiom one_sens_eval d1 d2 q: adj d1 d2 => `|evalQ q d1 - evalQ q d2| <= 1.


(* -------------------------------------------------------------------- *)
op Ts : int list.
op ts : int -> real.

module AboveTs = {
  proc aboveTs(d : db, qs : query list, Ts : int list) : int = {
    var i, ret, noise, tnoise, ans : int;
    
    noise =$ lap eps 0;
    ret = -1;
    
    i = 0;
    while (i < size qs) {
      ans =$ lap eps (evalQ (nth nullQ qs i) d);
      tnoise = (nth 0 Ts i) + noise;
      ret = (tnoise < ans && ret = -1) ? i : ret;
      i = i + 1;
    }
    
    return ret;
  }
}.


module LargeMargin = {
  proc main(d : db, qs : query list) : query = {
    var m, i, maxInd, maxScore, cutoff, ans : int;
    var update : bool;
    var sorted, tests : query list;
    var filter : bool list;

    sorted = sort (fun (q q' : query) => evalQ q' d <= evalQ q d) qs;
    m =$ lap eps (evalQ (head nullQ sorted)  d);
    tests = map (fun (q : query) => fun (d : db) => m - evalQ q d) qs;
    cutoff = AboveTs.aboveTs(d,drop 1 tests,Ts);

    filter = map (fun (q : query) => (mem (take cutoff sorted) q)) qs;

    maxInd = -1;
    maxScore = 0;
    i = 0;
    while (i < size qs) {
      if (nth true filter i) {
        ans =$ lap eps (evalQ (nth nullQ qs i) d);
        update = (maxScore < ans || maxInd = -1);
        maxInd = update ? i : maxInd;
        maxScore = update ? ans : maxScore;
      }
      i = i + 1;
    }

    return (nth nullQ qs maxInd);
  }
}.
