(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2016 - IMDEA Software Institute
 * Copyright (c) - 2012--2016 - Inria
 * 
 * Distributed under the terms of the CeCILL-C-V1 license
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
open EcParsetree
open EcFol
open EcCoreGoal.FApi

(* -------------------------------------------------------------------- *)
val t_eager_seq     : int -> int -> form -> EcIdent.t -> backward
val t_eager_if      : backward
val t_eager_while   : EcIdent.t -> backward
val t_eager_fun_def : backward
val t_eager_fun_abs : EcFol.form -> EcIdent.t -> backward
val t_eager_call    : form -> form -> backward

(* -------------------------------------------------------------------- *)
val process_seq     : eager_info -> int * int -> pformula -> backward
val process_if      : backward
val process_while   : eager_info -> backward
val process_fun_def : backward
val process_fun_abs : eager_info -> pformula -> backward
val process_call    : call_info gppterm -> backward
val process_eager   : eager_info -> pformula -> backward

(* -------------------------------------------------------------------- *)
(* [eager-seq]
 *   (a)  c1;S ~ S;c1' : P ==> ={R}
 *   (b)  c2;S ~ S;c2' : ={R} ==> Q
 *   (c)  c2' ~ c2'    : ={R.2} ==> ={Q.2}
 *   (d)  ={R} => ={Is}
 *   (e)  compat S S' R Xs
 *   (h)  S ~ S' : ={Is} ==> ={Xs}
 *  --------------------------------------------------
 *        c1;c2;S ~ S;c1';c2' : P ==> Q
 *
 * where compat S S' R Xs =
 *   forall modS modS', ={Xs{modS,modS'}} => ={R{modS,modS'}}
 *
 * [eager-if]
 *   (a) P => e{1} = e'{2}
 *   (b) S;c1 ~ S';c1' : P /\ e{1} ==> Q
 *   (c) S;c2 ~ S';c2' : P /\ !e{1} ==> Q
 *   (d) forall b &2, S  : P /\ e = b ==> e = b
 * --------------------------------------------------
 *       S;if e then c1 else c2
 *     ~ if e' then c1' else c2';S' : P ==> Q
 *
 * [eager-while]
 *
 *   (a) ={I} => e{1} = e{2}
 *   (b) S;c ~ c';S' : ={I} /\ e{1} ==> ={I}
 *   (c)  c' ~ c'    : ={I.2} ==> ={I.2}
 *   (d) forall b &2, S  : e = b ==> e = b
 *   (e) ={I} => ={Is}
 *   (f) compat S S' I Xs
 *   (h) S ~ S' : ={Is} ==> ={Xs}
 * --------------------------------------------------
 *       S;while e do c ~ while e' do c';S'
 *         : ={I} ==> ={I,Xs} /\ !e{1}
 *
 * [eager-fun-def]
 *
 *   (a) S and S' depend only of global
 *       (this should be an invariant of the typing)
 *   (b) S;f.body;result = f.res; ~ S';f'.body;result' = f'.res
 *         : P ==> Q{res{1}<- result, res{2} <- result'}
 * --------------------------------------------------
 *        S, f ~ f', S' : P ==> Q
 *
 * [eager-fun-abs]
 *
 * S and S' depend only of global (hould be an invariant of the typing)
 *
 *  (a) ={I} => e{1} = e{2}
 *  for each oracles o o':
 *      o and o' do not modify (glob A) (this is implied by (f))
 *  (b) S,o ~ o',S' : ={I,params} ==> ={I,res}
 *  (c) o'~ o' : ={I.2, o'.params} ==> ={I.2, res}
 *  (e) ={I} => ={Is}
 *  (f) compat S S' I Xs
 *  (h) S ~ S' : ={Is} ==> ={Xs}
 *  (i) glob A not in I (checked in EcPhlFun.equivF_abs_spec)
 *  (j) S, S' do not modify glob A
 * --------------------------------------------------
 *      S, A.f{o} ~ A.f(o'), S'
 *        : ={I,glob A,A.f.params} ==> ={I,glob A,res}
 *
 * Remark : ={glob A} is not required in pre condition when A.f is an initializer
 *
 * [eager-call]
 *   S,f ~ f',S' : fpre ==> fpost
 *   S do not write a
 * --------------------------------------------------
 *   S;x = f(a) ~ x' = f'(a');S' : wp_call fpre fpost post ==> post
 *)
