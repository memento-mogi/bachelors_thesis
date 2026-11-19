From Stdlib Require Import Nat List FunctionalExtensionality.
From LF Require Export Maps syntax.

Declare Scope lf_scope.
Open Scope lf_scope.
Notation "n =? m" := (Nat.eqb n m) : lf_scope.

Declare Custom Entry lf_ki.
Declare Custom Entry lf_ty.
Declare Custom Entry lf_tm.

(* Kinds *)
Notation "<{| K |}>" := K (K custom lf_ki at level 99) : lf_scope.

Notation "x" := x (in custom lf_ki at level 0, x constr at level 0) : lf_scope.
Notation "( K )" := K (in custom lf_ki at level 0, K custom lf_ki at level 99) : lf_scope.
Notation "{ K }" := K (in custom lf_ki at level 0, K constr at level 99, only parsing) : lf_scope.
Notation "*" := KiStar (in custom lf_ki at level 0) : lf_scope.
Notation "'Pi' T ',' K" := (KiPi T K) (in custom lf_ki at level 90, T custom lf_ty at level 99, K custom lf_ki at level 99) : lf_scope.

(* Types *)
Notation "<{{ T }}>" := T (T custom lf_ty at level 99) : lf_scope.

Notation "x" := x (in custom lf_ty at level 0, x constr at level 0) : lf_scope.
Notation "( T )" := T (in custom lf_ty at level 0, T custom lf_ty at level 99) : lf_scope.
Notation "{ T }" := T (in custom lf_ty at level 0, T constr at level 99, only parsing) : lf_scope.
Notation "\: T ',' S" := (TyPi T S) (in custom lf_ty at level 90, T custom lf_ty at level 99, S custom lf_ty at level 99) : lf_scope.
Notation "T t" := (TyTmApp T t) (in custom lf_ty at level 11, left associativity, t custom lf_tm at level 0) : lf_scope.
Notation "'Unit'" := TyUnit (in custom lf_ty at level 0) : lf_scope.

(* Terms *)
Notation "<{ t }>" := t (t custom lf_tm at level 99) : lf_scope.

Notation "x" := x (in custom lf_tm at level 0, x constr at level 0) : lf_scope.
Notation "( t )" := t (in custom lf_tm at level 0, t custom lf_tm at level 99) : lf_scope.
Notation "{ t }" := t (in custom lf_tm at level 0, t constr at level 99, only parsing) : lf_scope.
Notation "\: T ',' t" := (TmAbs T t) (in custom lf_tm at level 90, T custom lf_ty at level 99, t custom lf_tm at level 90) : lf_scope.
Notation "t1 t2" := (TmApp t1 t2) (in custom lf_tm at level 11, left associativity) : lf_scope.
Notation "'unit'" := TmUnit (in custom lf_tm at level 0) : lf_scope.

Coercion TyVar : nat >-> Ty.
Coercion TmVar : nat >-> Tm.

Definition sigma_tm_empty : nat -> Tm := fun n => TmVar n.
Definition sigma_tm_one (x: nat) (s: Tm) : nat -> Tm :=
  fun n => if n=?x then s else TmVar n.

Notation "'(' x '\->' t0 ')'" := (sigma_tm_one x t0) (in custom lf_tm, x constr, t0 custom lf_tm, only parsing) : lf_scope.
Notation "'[' x ':=' t0 ']' K" := (subst_Ki (sigma_tm_one x t0) K)
    (in custom lf_ki at level 5, K custom lf_ki at next level, right associativity) : lf_scope.
Notation "'[' x ':=' t0 ']' T" := (subst_Ty (sigma_tm_one x t0) T)
    (in custom lf_ty at level 5, T custom lf_ty at next level, right associativity) : lf_scope.
Notation "'[' x ':=' t0 ']' t" := (subst_Tm (sigma_tm_one x t0) t)
    (in custom lf_tm at level 5, t custom lf_tm at next level, right associativity) : lf_scope.

Reserved Notation "t '-->' t'" (at level 40).

Inductive value : Tm -> Prop :=
  | v_abs : forall T t1,
      value <{\:T, t1}>
  | v_unit :
      value <{unit}>
.

Definition tm_tm_betared t v :=
  ren_Tm Nat.pred (
    subst_Tm (sigma_tm_one 0 (ren_Tm S v)) t
  ).

Inductive step : Tm -> Tm -> Prop :=
  | ST_AppAbs : forall T t v,
         value v ->
         <{(\:T, t) v}> --> tm_tm_betared t v
  | ST_App1 : forall t1 t1' t2,
         t1 --> t1' ->
         <{t1 t2}> --> <{t1' t2}>
  | ST_App2 : forall v1 t2 t2',
         value v1 ->
         t2 --> t2' ->
         <{v1 t2}> --> <{v1  t2'}>

where "t '-->' t'" := (step t t').

Reserved Notation "t1 ==>tm t2" (at level 97).

Inductive tm_eval_step : Tm -> Tm -> Prop :=
  | TMST_Var : forall (x : nat),
      <{x}> ==>tm <{x}>
  | TMST_Unit :
      <{unit}> ==>tm <{unit}>
  | TMST_Abs : forall T1 T2 t1 t1',
      t1 ==>tm t1' ->
      <{\:T1, t1}> ==>tm <{\:T2, t1'}>
  | TMST_App : forall t1 t1' t2 t2',
      t1 ==>tm t1' ->
      t2 ==>tm t2' ->
      <{t1 t2}> ==>tm <{t1' t2'}>
  | TMST_Red : forall T t1 t1' t2 t2' t',
      t1 ==>tm t1' ->
      t2 ==>tm t2' ->
      t' = tm_tm_betared t1' t2' ->
      <{(\:T, t1) t2}> ==>tm t'

where "t1 ==>tm t2" := (tm_eval_step t1 t2) : lf_scope.

Inductive multi {X: Type} (R: X -> X -> Prop) : X -> X -> Prop :=
  | multi_refl : forall (T : X), multi R T T
  | multi_step : forall (T1 T2 T3 : X),
        R T1 T2 ->
        multi R T2 T3 ->
        multi R T1 T3.

Definition ty_tm_betared (T : Ty) (t : Tm) : Ty :=
  ren_Ty Nat.pred (
    subst_Ty (sigma_tm_one 0 (ren_Tm S t)) T
  ).

Reserved Notation "T1 ==>ty T2" (at level 97).

Inductive ty_eval_step : Ty -> Ty -> Prop :=
  | TST_Var : forall (X : nat),
      <{{X}}> ==>ty <{{X}}>
  | TST_Unit :
      <{{Unit}}> ==>ty <{{Unit}}>
  | TST_Pi : forall T1 S1 T2 S2,
      T1 ==>ty T2 ->
      S1 ==>ty S2 ->
      <{{\:T1, S1}}> ==>ty <{{\:T2, S2}}>
  | TST_App : forall T1 S1 t t',
      T1 ==>ty S1 ->
      t ==>tm t' ->
      <{{T1 t}}> ==>ty <{{S1 t'}}>
  | TST_Red : forall T S1 S2 t t' S,
      S1 ==>ty S2 ->
      t ==>tm t' ->
      S = ty_tm_betared S2 t' ->
      <{{(\:T, S1) t}}> ==>ty S

where " T1 ==>ty T2 " := (ty_eval_step T1 T2) : lf_scope.

Definition tm_eval_step_lr t1 t2 := (tm_eval_step t1 t2 \/ tm_eval_step t2 t1).
Definition ty_eval_step_lr T1 T2 := (ty_eval_step T1 T2 \/ ty_eval_step T2 T1).

Notation "t1 <=>tm t2" := (tm_eval_step_lr t1 t2) (at level 98) : lf_scope.
Notation "T1 <=>ty T2" := (ty_eval_step_lr T1 T2) (at level 98) : lf_scope.

Definition tm_eq t1 t2 := multi tm_eval_step_lr t1 t2.
Definition ty_eq T1 T2 := multi ty_eval_step_lr T1 T2.

Notation "t1 ===tm t2" := (tm_eq t1 t2) (at level 99) : lf_scope.
Notation "T1 ===ty T2" := (ty_eq T1 T2) (at level 99) : lf_scope.

Definition ki_tm_betared (K : Ki) (t : Tm) : Ki :=
  subst_Ki (fun n => TmVar (Nat.pred n)) (
    subst_Ki (sigma_tm_one 0 (ren_Tm S t)) K
  ).

Definition ty_context := list Ki.
Definition tm_context := list Ty.

Reserved Notation "K1 ===ki K2" (at level 99).

Inductive ki_eq : Ki -> Ki -> Prop :=
  | KiEq_Star : KiStar ===ki KiStar
  | KiEq_Pi : forall T S K J,
      T ===ty S ->
      K ===ki J ->
      (KiPi T K) ===ki (KiPi S J)

where "K1 ===ki K2" := (ki_eq K1 K2) : lf_scope.

Reserved Notation "<[[ Delta '|' Gamma '|--' T '\in' K ]]>" (at level 0, Delta at level 99, Gamma at level 99, T custom lf_ty, K custom lf_ki).
Reserved Notation "<[ Delta '|' Gamma '|--' t '\in' T ]>" (at level 0, Delta at level 99, Gamma at level 99, t custom lf_tm, T custom lf_ty).

Inductive has_kind : ty_context -> tm_context -> Ty -> Ki -> Prop :=
  | K_Var : forall Delta Gamma X K,
      nth_error Delta X = Some K ->
      <[[ Delta | Gamma |-- X \in K ]]>
  | K_Pi : forall Delta Gamma GammaS T S,
      <[[ Delta | Gamma |-- T \in * ]]> ->
      GammaS = (ren_Ty Datatypes.S T) :: map (ren_Ty Datatypes.S) Gamma ->
      <[[ Delta | GammaS |-- S \in * ]]> ->
      <[[ Delta | Gamma |-- \:T, S \in * ]]>
  | K_App : forall Delta Gamma S T t K K',
      <[[ Delta | Gamma |-- S \in {KiPi T K} ]]> ->
      <[ Delta | Gamma |-- t \in T ]> ->
      K' = ki_tm_betared K t ->
      <[[ Delta | Gamma |-- S t \in K' ]]>
  | K_Conv : forall Delta Gamma T K J,
      <[[ Delta | Gamma |-- T \in K ]]> ->
      K ===ki J ->
      <[[ Delta | Gamma |-- T \in J ]]>
  | K_Unit : forall Delta Gamma,
      <[[ Delta | Gamma |-- Unit \in * ]]>

with has_type : ty_context -> tm_context -> Tm -> Ty -> Prop :=
  | T_Var : forall Delta Gamma x T,
      nth_error Gamma x = Some T ->
      <[ Delta | Gamma |-- x \in T ]>
  | T_Abs : forall Delta Gamma GammaS T S t1,
      <[[ Delta | Gamma |-- T \in * ]]> ->
      GammaS = (ren_Ty Datatypes.S T) :: map (ren_Ty Datatypes.S) Gamma ->
      <[ Delta | GammaS |-- t1 \in S ]> ->
      <[ Delta | Gamma |-- \:T, t1 \in \:T, S ]>
  | T_App : forall Delta Gamma t1 t2 T S S',
      <[ Delta | Gamma |-- t1 \in \:T, S ]> ->
      <[ Delta | Gamma |-- t2 \in T ]> ->
      S' = ty_tm_betared S t2 ->
      <[ Delta | Gamma |-- t1 t2 \in S' ]>
  | T_Conv : forall Delta Gamma t T S,
      <[ Delta | Gamma |-- t \in T ]> ->
      T ===ty S ->
      <[[ Delta | Gamma |-- S \in * ]]> ->
      <[ Delta | Gamma |-- t \in S ]>
  | T_Unit : forall Delta Gamma,
      <[ Delta | Gamma |-- unit \in Unit ]>

    where "<[ Delta '|' Gamma '|--' t '\in' T ]>" := (has_type Delta Gamma t T) : lf_scope
    and "<[[ Delta '|' Gamma '|--' T '\in' K ]]>" := (has_kind Delta Gamma T K) : lf_scope.

Scheme has_kind_mut := Induction for has_kind Sort Prop
with has_type_mut := Induction for has_type Sort Prop.

Combined Scheme has_kind_has_type_mutind from has_kind_mut, has_type_mut.

Definition wf (Delta: ty_context) (Gamma: tm_context) :=
  forall x T, nth_error Gamma x = Some T -> <[[ Delta | Gamma |-- T \in * ]]>.

Definition wf_Delta (Delta: ty_context) :=
  forall X K, nth_error Delta X = Some K -> forall sigma, subst_Ki sigma K = K.

Ltac aunfold := unfold core.funcomp, unscoped.scons, unscoped.shift, unscoped.id.
Ltac asolve := simpl; aunfold; simpl; try auto.
Ltac dauto := try (intros _x; destruct _x; auto).
