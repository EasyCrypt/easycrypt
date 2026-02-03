(* -------------------------------------------------------------------- *)
open EcAst
open EcUtils
open EcParsetree
open EcCoreGoal.FApi
open EcMatching.Position

val process_seq : pcodepos1 pair -> pstmt -> pformula doption -> backward
(** Tactic [eager seq] derives the following proof:
    {v
  (a) S; c₁ ~ c₁'; S : P ==> R₂
  (b) S; c₂ ~ c₂'; S : R₁ ==> Q
  (c) c₁' ~ c₁' : Eq ==> R₁
  (d) c₂ ~ c₂ : R₂ ==> ={Q.1}
 -----------------------------------
  S; c₁; c₂ ~ c₁'; c₂'; S : P ==> Q
    v}
    where [R₁] and [R₂] are provided manually (and equal if a single value was
    provided), as well as [S]. The predicate [={Q.1}] means equality on all free
    variables bound to the first memory in [Q]. *)

val t_eager_seq : codepos1 pair -> stmt -> ts_inv pair -> backward
(** Internal variant of [eager seq] *)

val process_if : backward
(** Tactic [eager if] derives the following proof:
    {v
  (a) forall &1 &2, P => e{1} = e'{2}
  (b) forall &2 b, S : P /\ e = b ==> e = b
  (c) S; c₁ ~ c₁'; S : P /\ e{1} ==> Q
  (d) S; c₂ ~ c₂'; S : P /\ !e{1} ==> Q
 --------------------------------------------
  S; if e then c₁ else c₂
   ~ if e' then c₁' else c₂'; S : P ==> Q
    v} *)

val t_eager_if : backward
(** Internal variant of [eager if] *)

val process_while : pformula -> backward
(** Tactic [eager while] derives the following proof:
    {v
  (a) I => ={e, I.1}
  (b) S; c ~ c'; S : I /\ e{1} ==> I
  (c) forall b &2, S : e = b ==> e = b
  (d) c' ~ c' : Eq ==> I
  (e) c ~ c : I ==> I
  (f) S ~ S : I /\ !e{1} ==> I
 --------------------------------------------------------
  S; while e do c ~ while e do c'; S : I ==> I /\ !e{1}
    v}
    Where the invariant [I] is manually provided.
    Please note that the guard [e] is syntactically identical in both
    programs. *)

val t_eager_while : ts_inv -> backward
(** Internal variant of [eager while] *)

val process_fun_def : backward
(** Tactic [eager proc] derives the following proof:
    {v
  (0) S and S' depend only of global (typing invariant)
  (a) S; f.body; result = f.res; ~ S'; f'.body; result' = f'.res
        : P ==> Q{res{1} <- result, res{2} <- result'}
 ----------------------------------------------------------------
  S, f ~ f', S : P ==> Q
    v} *)

val t_eager_fun_def : backward
(** Internal variant of [eager proc] *)

val process_call : call_info gppterm -> backward
(** Tactic [eager call] derives the following proof:
    {v
  (a) S, f ~ f', S : fpre ==> fpost
  (b) S does not write a
 ------------------------------------------------------------------
   S; x = f(a) ~ x' = f'(a'); S : wp_call fpre fpost post ==> post
    v} *)

val t_eager_call : ts_inv -> ts_inv -> backward
(** Internal variant of [eager call] *)

val process_fun_abs : pformula -> backward
(** Tactic [eager call] (on abstract functions) derives the following proof:
    {v
  (0) S depends only on globals (typing invariant)
  (a) I is a conjunction of same-name variable equalities
  (b) glob A not in I (checked in EcPhlFun.equivF_abs_spec)
  (c) S does not modify glob A
  (d) S ~ S : I ==> I
  for each oracles o o':
      o and o' do not modify (glob A)
  (e) S, o ~ o', S : I /\ ={o'.params} ==> I /\ ={res}
  (f) o' ~ o' : Eq ==> I /\ ={res}
  (g) o ~ o : I /\ ={o.params} ==> I /\ ={res}
 --------------------------------------------------------
  S, A.f{o} ~ A.f(o'), S
    : I /\ ={glob A, A.f.params} ==> I /\ ={glob A, res}
    v} *)

val t_eager_fun_abs : ts_inv -> backward
(** Internal variant of [eager call] (on abstract functions) *)
