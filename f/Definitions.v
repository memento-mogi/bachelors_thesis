From Stdlib Require Import List.
From F Require Export Syntax.
Require Import core unscoped.

(* ---------- surface syntax, fomega_sumprod-style custom entries ---------- *)

Declare Scope plc_scope.
Open Scope plc_scope.

Declare Custom Entry plc_ty.
Declare Custom Entry plc_tm.

Notation "<{{ T }}>" := T (T custom plc_ty at level 99) : plc_scope.

Notation "x" := x (in custom plc_ty at level 0, x constr at level 0) : plc_scope.
Notation "x" := x (in custom plc_tm at level 0, x constr at level 0) : plc_scope.

Notation "( T )" := T (in custom plc_ty at level 0, T custom plc_ty at level 99) : plc_scope.
Notation "T1 -> T2" := (TyArrow T1 T2) (in custom plc_ty at level 50, right associativity) : plc_scope.
Notation "'-/,' T" := (TyForall T) (in custom plc_ty at level 90, T custom plc_ty at level 90) : plc_scope.
Notation "'Unit'" := TyUnit (in custom plc_ty at level 0) : plc_scope.

Notation "<{ t }>" := t (t custom plc_tm at level 99) : plc_scope.

Notation "( t )" := t (in custom plc_tm at level 0, t custom plc_tm at level 99) : plc_scope.
Notation "t1 t2" := (TmApp t1 t2) (in custom plc_tm at level 11, left associativity) : plc_scope.
Notation "\: T ',' t" := (TmAbs T t) (in custom plc_tm at level 90, T custom plc_ty at level 99, t custom plc_tm at level 90) : plc_scope.
Notation "t [ T ]" := (TmTApp t T) (in custom plc_tm at level 11, t custom plc_tm, T custom plc_ty at level 0) : plc_scope.
Notation "'\\,' t" := (TmTAbs t) (in custom plc_tm at level 90, t custom plc_tm at level 90) : plc_scope.
Notation "'unit'" := TmUnit (in custom plc_tm at level 0) : plc_scope.

Coercion var_ty : nat >-> ty.
Coercion var_tm : nat >-> tm.

(* beta reduction *)
Definition tm_tm_betared (t v : tm) : tm :=
  subst_tm var_ty (scons v var_tm) t.

Definition tm_ty_betared (t : tm) (T : ty) : tm :=
  subst_tm (scons T var_ty) var_tm t.

Definition ty_beta_red (T1 S0 : ty) : ty :=
  subst_ty (scons S0 var_ty) T1.

(* values *)
Inductive value : tm -> Prop :=
  | V_Abs : forall T t, value (TmAbs T t)
  | V_TAbs : forall t, value (TmTAbs t)
  | V_Unit : value TmUnit.

(* evaluation *)
Reserved Notation "t '-->' t'" (at level 40).

Inductive step : tm -> tm -> Prop :=
  | ST_AppAbs : forall T t v,
      value v ->
      TmApp (TmAbs T t) v --> tm_tm_betared t v
  | ST_App1 : forall t1 t1' t2,
      t1 --> t1' ->
      TmApp t1 t2 --> TmApp t1' t2
  | ST_App2 : forall v1 t2 t2',
      value v1 ->
      t2 --> t2' ->
      TmApp v1 t2 --> TmApp v1 t2'
  | ST_TAppAbs : forall t1 T,
      TmTApp (TmTAbs t1) T --> tm_ty_betared t1 T
  | ST_TApp : forall t1 t1' T,
      t1 --> t1' ->
      TmTApp t1 T --> TmTApp t1' T

where "t '-->' t'" := (step t t').

(* typing *)
Definition context := list ty.

Reserved Notation "<[ Gamma |-- t \in T ]>"
  (at level 0, Gamma at level 99, t custom plc_tm, T custom plc_ty).

Inductive has_type (Gamma : context) : tm -> ty -> Prop :=
  | T_Var : forall x T1,
      nth_error Gamma x = Some T1 ->
      <[ Gamma |-- x \in T1 ]>
  | T_Abs : forall T1 T2 t1,
      <[ T1 :: Gamma |-- t1 \in T2 ]> ->
      <[ Gamma |-- \:T1, t1 \in T1 -> T2 ]>
  | T_App : forall t1 t2 T1 T2,
      <[ Gamma |-- t1 \in T1 -> T2 ]> ->
      <[ Gamma |-- t2 \in T1 ]> ->
      <[ Gamma |-- t1 t2 \in T2 ]>
  | T_TAbs : forall t1 T1,
      <[ map (ren_ty S) Gamma |-- t1 \in T1 ]> ->
      <[ Gamma |-- \\, t1 \in -/, T1 ]>
  | T_TApp : forall t1 T1 S T1',
      <[ Gamma |-- t1 \in -/, T1 ]> ->
      T1' = ty_beta_red T1 S ->
      <[ Gamma |-- t1 [S] \in T1' ]>
  | T_Unit :
      <[ Gamma |-- unit \in Unit ]>

where "<[ Gamma |-- t \in T ]>" := (has_type Gamma t T) : plc_scope.

Ltac aunfold := unfold core.funcomp, unscoped.scons, unscoped.shift, unscoped.id.
Ltac asolve := simpl; asimpl; aunfold; simpl; try auto.
Ltac dauto := try (intros _x; destruct _x; auto).
