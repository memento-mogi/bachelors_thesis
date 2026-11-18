From Stdlib Require Import Nat List FunctionalExtensionality.
From LF Require Export syntax.

Declare Scope lf_scope.
Open Scope lf_scope.
Notation "n =? m" := (Nat.eqb n m) : lf_scope.

Declare Custom Entry lf_tm.

(* Terms (単相: 型も項も Tm の1層) *)
Notation "<{ t }>" := t (t custom lf_tm at level 99) : lf_scope.

Notation "x" := x (in custom lf_tm at level 0, x constr at level 0) : lf_scope.
Notation "( t )" := t (in custom lf_tm at level 0, t custom lf_tm at level 99) : lf_scope.
Notation "{ t }" := t (in custom lf_tm at level 0, t constr at level 99, only parsing) : lf_scope.
Notation "'*'" := (TmSort Star) (in custom lf_tm at level 0) : lf_scope.
Notation "'box'" := (TmSort Box) (in custom lf_tm at level 0) : lf_scope.
Notation "'Pi' A ',' B" := (TmPi A B) (in custom lf_tm at level 90, A custom lf_tm at level 99, B custom lf_tm at level 99) : lf_scope.
Notation "\: A ',' t" := (TmAbs A t) (in custom lf_tm at level 90, A custom lf_tm at level 99, t custom lf_tm at level 90) : lf_scope.
Notation "t1 t2" := (TmApp t1 t2) (in custom lf_tm at level 11, left associativity) : lf_scope.
Notation "'Unit'" := TmUnit (in custom lf_tm at level 0) : lf_scope.
Notation "'tt'" := TmTt (in custom lf_tm at level 0) : lf_scope.

Coercion TmVar : nat >-> Tm.

Definition sigma_tm_empty : nat -> Tm := fun n => TmVar n.
Definition sigma_tm_one (x: nat) (s: Tm) : nat -> Tm :=
  fun n => if n=?x then s else TmVar n.

Notation "'(' x '\->' s ')'" := (sigma_tm_one x s) (in custom lf_tm, x constr, s custom lf_tm, only parsing) : lf_scope.
Notation "'[' x ':=' s ']' t" := (subst_Tm (sigma_tm_one x s) t)
    (in custom lf_tm at level 10, t custom lf_tm at next level, right associativity) : lf_scope.

Definition shift_Tm t := ren_Tm S t.

Reserved Notation "t '-->' t'" (at level 40).

Inductive value : Tm -> Prop :=
  | v_sort : forall s,
      value <{ {TmSort s} }>
  | v_pi : forall A B,
      value <{ Pi A, B }>
  | v_abs : forall A t1,
      value <{ \: A, t1 }>
  | v_unit :
      value <{ Unit }>
  | v_tt :
      value <{ tt }>
.

Definition tm_tm_betared t v :=
  ren_Tm Nat.pred (
    subst_Tm (sigma_tm_one 0 (ren_Tm S v)) t
  ).

Inductive step : Tm -> Tm -> Prop :=
  | ST_AppAbs : forall A t v,
         value v ->
         <{(\:A, t) v}> --> tm_tm_betared t v
  | ST_App1 : forall t1 t1' t2,
         t1 --> t1' ->
         <{t1 t2}> --> <{t1' t2}>
  | ST_App2 : forall v1 t2 t2',
         value v1 ->
         t2 --> t2' ->
         <{v1 t2}> --> <{v1  t2'}>

where "t '-->' t'" := (step t t').

Definition tm_context := list Tm.

Reserved Notation "T1 ==> T2" (at level 97).

Inductive tm_eval_step : Tm -> Tm -> Prop :=
  | TST_Var : forall (X : nat),
      <{ X }> ==> <{ X }>
  | TST_Sort : forall s,
      <{  {TmSort s}  }> ==> <{  {TmSort s}  }>
  | TST_Unit :
      <{ Unit }> ==> <{ Unit }>
  | TST_Tt :
      <{ tt }> ==> <{ tt }>
  | TST_Pi : forall A1 B1 A2 B2,
      A1 ==> A2 ->
      B1 ==> B2 ->
      <{ Pi A1, B1 }> ==> <{ Pi A2, B2 }>
  | TST_Abs : forall A1 t1 A2 t2,
      A1 ==> A2 ->
      t1 ==> t2 ->
      <{ \:A1, t1 }> ==> <{ \:A2, t2 }>
  | TST_App : forall T1 S1 T2 S2,
      T1 ==> S1 ->
      T2 ==> S2 ->
      <{ T1 T2 }> ==> <{ S1 S2 }>
  | TST_Red : forall A T1 S1 T2 S2 S,
      T1 ==> S1 ->
      T2 ==> S2 ->
      S = tm_tm_betared S1 S2 ->
      <{ (\:A, T1) T2 }> ==> S

where " T1 ==> T2 " := (tm_eval_step T1 T2) : lf_scope.

Definition tm_eval_step_lr T1 T2 := (tm_eval_step T1 T2 \/ tm_eval_step T2 T1).

Notation "T1 <=> T2" := (tm_eval_step_lr T1 T2) (at level 98) : lf_scope.

Inductive multi {X: Type} (R: X -> X -> Prop) : X -> X -> Prop :=
  | multi_refl : forall (T : X), multi R T T
  | multi_step : forall (T1 T2 T3 : X),
        R T1 T2 ->
        multi R T2 T3 ->
        multi R T1 T3.

Definition tm_eq T1 T2 := multi tm_eval_step_lr T1 T2.

Notation "T1 === T2" := (tm_eq T1 T2) (at level 99) : lf_scope.

(* 単相の依存文脈では「変数は見つかるたびに1つ分シフトする」ので、
   nth_error ではなく自動シフト付きのルックアップ at_tm を使う。
   (fomega の Ty/Tm 2層では Ty 変数と Gamma の位置が独立なので
    不要だった処理が、単相化したことで必要になった。) *)
Inductive at_tm : tm_context -> nat -> Tm -> Prop :=
  | at_here : forall Gamma A,
      at_tm (A :: Gamma) 0 (ren_Tm S A)
  | at_there : forall Gamma A B n,
      at_tm Gamma n A ->
      at_tm (B :: Gamma) (S n) (ren_Tm S A)
.

(* lf (= λP) の T_Pi/T_Abs は「ドメインは常に Star」という制約を持つ。
   これを fomega_mono/coc と同じ rule 述語の形で明示する。
   lf の rule はコドメインに関わらずドメインを Star に固定する等式
   になる点が fomega_mono (s1=Box\/s2=Star) や coc (True) と違う。
   ラムダキューブで言えば λP の規則集合は Star,Star と Star,Box の2つ。 *)
Definition rule (s1 s2 : Srt) : Prop := s1 = Star.

Reserved Notation "<[ Gamma '|--' t '\in' T ]>" (at level 0, Gamma at level 99, t custom lf_tm, T custom lf_tm).

Inductive has_type : tm_context -> Tm -> Tm -> Prop :=
  | T_Var : forall Gamma x T1,
      at_tm Gamma x T1 ->
      <[ Gamma |-- x \in T1 ]>
  | T_Sort : forall Gamma,
      <[ Gamma |-- * \in box ]>
  | T_Pi : forall Gamma A B s1 s2,
      <[ Gamma |-- A \in {TmSort s1} ]> ->
      rule s1 s2 ->
      <[ A :: Gamma |-- B \in {TmSort s2} ]> ->
      <[ Gamma |-- Pi A, B \in {TmSort s2} ]>
  | T_Abs : forall Gamma A B t1 s1 s2,
      <[ Gamma |-- A \in {TmSort s1} ]> ->
      rule s1 s2 ->
      <[ A :: Gamma |-- t1 \in B ]> ->
      <[ Gamma |-- Pi A, B \in {TmSort s2} ]> ->
      <[ Gamma |-- \:A, t1 \in Pi A, B ]>
  | T_App : forall Gamma t1 t2 A B B',
      <[ Gamma |-- t1 \in Pi A, B ]> ->
      <[ Gamma |-- t2 \in A ]> ->
      B' = tm_tm_betared B t2 ->
      <[ Gamma |-- t1 t2 \in B' ]>
  | T_Conv : forall Gamma t A B s2,
      <[ Gamma |-- t \in A ]> ->
      A === B ->
      <[ Gamma |-- B \in {TmSort s2} ]> ->
      <[ Gamma |-- t \in B ]>
  | T_Unit : forall Gamma,
      <[ Gamma |-- Unit \in * ]>
  | T_Tt : forall Gamma,
      <[ Gamma |-- tt \in Unit ]>

    where "<[ Gamma '|--' t '\in' T ]>" := (has_type Gamma t T) : lf_scope.

Fixpoint wf (Gamma: tm_context) : Prop :=
  match Gamma with
  | nil => True
  | A :: Gamma' => wf Gamma' /\ exists s, <[ Gamma' |-- A \in {TmSort s} ]>
  end.

Ltac aunfold := unfold core.funcomp, unscoped.scons, unscoped.shift, unscoped.id.
Ltac asolve := simpl; asimpl; aunfold; simpl; try auto.
Ltac dauto := try (intros _x; destruct _x; auto).
