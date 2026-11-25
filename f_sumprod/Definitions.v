From Stdlib Require Import List.
From FSumProd Require Export Syntax.
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
Notation "'Prod' Ts" := (TyProd Ts) (in custom plc_ty at level 10, Ts constr at level 0) : plc_scope.
Notation "'Sum' Ts" := (TySum Ts) (in custom plc_ty at level 10, Ts constr at level 0) : plc_scope.
Notation "{ T }" := T (in custom plc_ty at level 0, T constr at level 99, only parsing) : plc_scope.

Notation "<{ t }>" := t (t custom plc_tm at level 99) : plc_scope.

Notation "( t )" := t (in custom plc_tm at level 0, t custom plc_tm at level 99) : plc_scope.
Notation "t1 t2" := (TmApp t1 t2) (in custom plc_tm at level 11, left associativity) : plc_scope.
Notation "\: T ',' t" := (TmAbs T t) (in custom plc_tm at level 90, T custom plc_ty at level 99, t custom plc_tm at level 90) : plc_scope.
Notation "t [ T ]" := (TmTApp t T) (in custom plc_tm at level 11, t custom plc_tm, T custom plc_ty at level 0) : plc_scope.
Notation "'\\,' t" := (TmTAbs t) (in custom plc_tm at level 90, t custom plc_tm at level 90) : plc_scope.
Notation "'unit'" := TmUnit (in custom plc_tm at level 0) : plc_scope.
Notation "'tuple' ts" := (TmTuple ts) (in custom plc_tm at level 10, ts constr at level 0) : plc_scope.
Notation "'proj' i t" := (TmProj i t) (in custom plc_tm at level 10, i constr at level 0, t custom plc_tm at level 0) : plc_scope.
Notation "'inj' i t" := (TmInj i t) (in custom plc_tm at level 10, i constr at level 0, t custom plc_tm at level 0) : plc_scope.
Notation "'case' t 'of' ts" := (TmCase t ts) (in custom plc_tm at level 90, t custom plc_tm at level 99, ts constr at level 0) : plc_scope.
Notation "{ t }" := t (in custom plc_tm at level 0, t constr at level 99, only parsing) : plc_scope.

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
  | V_Tuple : forall ts, Forall value ts -> value (TmTuple ts)
  | V_Inj : forall i v, value v -> value (TmInj i v)
  | V_Unit : value TmUnit.

(* evaluation *)
Reserved Notation "t '-->' t'" (at level 40).

Inductive step : tm -> tm -> Prop :=
  | ST_AppAbs : forall T t v,
      value v ->
      <{ (\:T, t) v }> --> tm_tm_betared t v
  | ST_App1 : forall t1 t1' t2,
      t1 --> t1' ->
      <{ t1 t2 }> --> <{ t1' t2 }>
  | ST_App2 : forall v1 t2 t2',
      value v1 ->
      t2 --> t2' ->
      <{ v1 t2 }> --> <{ v1 t2' }>
  | ST_TAppAbs : forall t1 T,
      <{ (\\, t1) [T] }> --> tm_ty_betared t1 T
  | ST_TApp : forall t1 t1' T,
      t1 --> t1' ->
      <{ t1 [T] }> --> <{ t1' [T] }>
  | ST_Tuple : forall vs t t' ts,
      Forall value vs ->
      t --> t' ->
      <{ tuple (vs ++ t :: ts) }> --> <{ tuple (vs ++ t' :: ts) }>
  | ST_ProjTuple : forall i ts v,
      Forall value ts ->
      nth_error ts i = Some v ->
      <{ proj i (tuple ts) }> --> v
  | ST_Proj : forall i t1 t1',
      t1 --> t1' ->
      <{ proj i t1 }> --> <{ proj i t1' }>
  | ST_Inj : forall i t1 t1',
      t1 --> t1' ->
      <{ inj i t1 }> --> <{ inj i t1' }>
  | ST_CaseInj : forall i v ts t,
      value v ->
      nth_error ts i = Some t ->
      <{ case (inj i v) of ts }> --> <{ t v }>
  | ST_Case : forall t1 t1' ts,
      t1 --> t1' ->
      <{ case t1 of ts }> --> <{ case t1' of ts }>

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
  | T_Tuple : forall ts Ts,
      Forall2 (has_type Gamma) ts Ts ->
      <[ Gamma |-- tuple ts \in Prod Ts ]>
  | T_Proj : forall i t1 Ts Ti,
      <[ Gamma |-- t1 \in Prod Ts ]> ->
      nth_error Ts i = Some Ti ->
      <[ Gamma |-- proj i t1 \in Ti ]>
  | T_Inj : forall i t1 Ts Ti,
      <[ Gamma |-- t1 \in Ti ]> ->
      nth_error Ts i = Some Ti ->
      <[ Gamma |-- inj i t1 \in Sum Ts ]>
  | T_Case : forall t1 ts Ts S,
      <[ Gamma |-- t1 \in Sum Ts ]> ->
      Forall2 (fun t Ti => <[ Gamma |-- t \in Ti -> S ]>) ts Ts ->
      <[ Gamma |-- case t1 of ts \in S ]>
  | T_Unit :
      <[ Gamma |-- unit \in Unit ]>

where "<[ Gamma |-- t \in T ]>" := (has_type Gamma t T) : plc_scope.

(* nested induction principle for has_type (Forall2 premises carry IHs) *)
Fixpoint has_type_ind2 (P : context -> tm -> ty -> Prop)
  (H_Var : forall Gamma x T1,
     nth_error Gamma x = Some T1 ->
     P Gamma (var_tm x) T1)
  (H_Abs : forall Gamma T1 T2 t1,
     has_type (T1 :: Gamma) t1 T2 -> P (T1 :: Gamma) t1 T2 ->
     P Gamma (TmAbs T1 t1) (TyArrow T1 T2))
  (H_App : forall Gamma t1 t2 T1 T2,
     has_type Gamma t1 (TyArrow T1 T2) -> P Gamma t1 (TyArrow T1 T2) ->
     has_type Gamma t2 T1 -> P Gamma t2 T1 ->
     P Gamma (TmApp t1 t2) T2)
  (H_TAbs : forall Gamma t1 T1,
     has_type (map (ren_ty S) Gamma) t1 T1 -> P (map (ren_ty S) Gamma) t1 T1 ->
     P Gamma (TmTAbs t1) (TyForall T1))
  (H_TApp : forall Gamma t1 T1 S T1',
     has_type Gamma t1 (TyForall T1) -> P Gamma t1 (TyForall T1) ->
     T1' = ty_beta_red T1 S ->
     P Gamma (TmTApp t1 S) T1')
  (H_Tuple : forall Gamma ts Ts,
     Forall2 (fun t T => has_type Gamma t T /\ P Gamma t T) ts Ts ->
     P Gamma (TmTuple ts) (TyProd Ts))
  (H_Proj : forall Gamma i t1 Ts Ti,
     has_type Gamma t1 (TyProd Ts) -> P Gamma t1 (TyProd Ts) ->
     nth_error Ts i = Some Ti ->
     P Gamma (TmProj i t1) Ti)
  (H_Inj : forall Gamma i t1 Ts Ti,
     has_type Gamma t1 Ti -> P Gamma t1 Ti ->
     nth_error Ts i = Some Ti ->
     P Gamma (TmInj i t1) (TySum Ts))
  (H_Case : forall Gamma t1 ts Ts S,
     has_type Gamma t1 (TySum Ts) -> P Gamma t1 (TySum Ts) ->
     Forall2 (fun t Ti => has_type Gamma t (TyArrow Ti S) /\
                          P Gamma t (TyArrow Ti S)) ts Ts ->
     P Gamma (TmCase t1 ts) S)
  (H_Unit : forall Gamma,
     P Gamma TmUnit TyUnit)
  Gamma t T (H : has_type Gamma t T) {struct H} : P Gamma t T :=
  match H with
  | T_Var _ x T1 Hx => H_Var Gamma x T1 Hx
  | T_Abs _ T1 T2 t1 H1 =>
      H_Abs Gamma T1 T2 t1 H1
        (has_type_ind2 P H_Var H_Abs H_App H_TAbs H_TApp H_Tuple H_Proj H_Inj H_Case H_Unit _ _ _ H1)
  | T_App _ t1 t2 T1 T2 H1 H2 =>
      H_App Gamma t1 t2 T1 T2
        H1 (has_type_ind2 P H_Var H_Abs H_App H_TAbs H_TApp H_Tuple H_Proj H_Inj H_Case H_Unit _ _ _ H1)
        H2 (has_type_ind2 P H_Var H_Abs H_App H_TAbs H_TApp H_Tuple H_Proj H_Inj H_Case H_Unit _ _ _ H2)
  | T_TAbs _ t1 T1 H1 =>
      H_TAbs Gamma t1 T1 H1
        (has_type_ind2 P H_Var H_Abs H_App H_TAbs H_TApp H_Tuple H_Proj H_Inj H_Case H_Unit _ _ _ H1)
  | T_TApp _ t1 T1 S2 T1' H1 Heq =>
      H_TApp Gamma t1 T1 S2 T1' H1
        (has_type_ind2 P H_Var H_Abs H_App H_TAbs H_TApp H_Tuple H_Proj H_Inj H_Case H_Unit _ _ _ H1) Heq
  | T_Tuple _ ts Ts HF =>
      let fix allP ts Ts (HF : Forall2 (has_type Gamma) ts Ts) :
          Forall2 (fun t T => has_type Gamma t T /\ P Gamma t T) ts Ts :=
          match HF with
          | Forall2_nil _ => Forall2_nil _
          | @Forall2_cons _ _ _ t T ts' Ts' Ht HF' =>
              Forall2_cons _ _
                (conj Ht (has_type_ind2 P H_Var H_Abs H_App H_TAbs H_TApp H_Tuple H_Proj H_Inj H_Case H_Unit _ _ _ Ht))
                (allP ts' Ts' HF')
          end
      in H_Tuple Gamma ts Ts (allP ts Ts HF)
  | T_Proj _ i t1 Ts Ti H1 Hi =>
      H_Proj Gamma i t1 Ts Ti H1
        (has_type_ind2 P H_Var H_Abs H_App H_TAbs H_TApp H_Tuple H_Proj H_Inj H_Case H_Unit _ _ _ H1) Hi
  | T_Inj _ i t1 Ts Ti H1 Hi =>
      H_Inj Gamma i t1 Ts Ti H1
        (has_type_ind2 P H_Var H_Abs H_App H_TAbs H_TApp H_Tuple H_Proj H_Inj H_Case H_Unit _ _ _ H1) Hi
  | T_Case _ t1 ts Ts S2 H1 HF =>
      let fix allP ts Ts
          (HF : Forall2 (fun t Ti => has_type Gamma t (TyArrow Ti S2)) ts Ts) :
          Forall2 (fun t Ti => has_type Gamma t (TyArrow Ti S2) /\
                               P Gamma t (TyArrow Ti S2)) ts Ts :=
          match HF with
          | Forall2_nil _ => Forall2_nil _
          | @Forall2_cons _ _ _ t Ti ts' Ts' Hf HF' =>
              Forall2_cons _ _
                (conj Hf (has_type_ind2 P H_Var H_Abs H_App H_TAbs H_TApp H_Tuple H_Proj H_Inj H_Case H_Unit _ _ _ Hf))
                (allP ts' Ts' HF')
          end
      in H_Case Gamma t1 ts Ts S2 H1
           (has_type_ind2 P H_Var H_Abs H_App H_TAbs H_TApp H_Tuple H_Proj H_Inj H_Case H_Unit _ _ _ H1)
           (allP ts Ts HF)
  | T_Unit _ => H_Unit Gamma
  end.

Ltac aunfold := unfold core.funcomp, unscoped.scons, unscoped.shift, unscoped.id.
Ltac asolve := simpl; asimpl; aunfold; simpl; try auto.
Ltac dauto := try (intros _x; destruct _x; auto).
