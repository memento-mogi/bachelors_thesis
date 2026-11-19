From Stdlib Require Vectors.Fin.
From Stdlib Require Vectors.Vector.
From Stdlib Require Import List.
Module V := Vector.

(* vector notations *)
Declare Scope vec_scope.
Notation "[ ]" := (V.nil _) : vec_scope.
Notation "x ::: v" := (V.cons _ x _ v) (at level 60, right associativity) : vec_scope.
Open Scope vec_scope.

(* substitution plumbing (generic, nat-indexed) *)

Definition scons {X : Type} (x : X) (xi : nat -> X) : nat -> X :=
  fun n => match n with 0 => x | S n' => xi n' end.

Definition up_ren (xi : nat -> nat) : nat -> nat := scons 0 (fun n => S (xi n)).

(* types: Prod/Sum carry a Vector.t ty p; Forall is the universal type *)

Inductive ty : Type :=
  | var_ty : nat -> ty
  | TyArr : ty -> ty -> ty
  | TyForall : ty -> ty
  | TyProd (p : nat) : V.t ty p -> ty
  | TySum (p : nat) : V.t ty p -> ty.

Fixpoint ren_ty (xi : nat -> nat) (T : ty) : ty :=
  match T with
  | var_ty n => var_ty (xi n)
  | TyArr T1 T2 => TyArr (ren_ty xi T1) (ren_ty xi T2)
  | TyForall T1 => TyForall (ren_ty (up_ren xi) T1)
  | TyProd p Ts => TyProd p (V.map (ren_ty xi) Ts)
  | TySum p Ts => TySum p (V.map (ren_ty xi) Ts)
  end.

Definition up_ty (sigma : nat -> ty) : nat -> ty :=
  scons (var_ty 0) (fun n => ren_ty S (sigma n)).

Fixpoint subst_ty (sigma : nat -> ty) (T : ty) : ty :=
  match T with
  | var_ty n => sigma n
  | TyArr T1 T2 => TyArr (subst_ty sigma T1) (subst_ty sigma T2)
  | TyForall T1 => TyForall (subst_ty (up_ty sigma) T1)
  | TyProd p Ts => TyProd p (V.map (subst_ty sigma) Ts)
  | TySum p Ts => TySum p (V.map (subst_ty sigma) Ts)
  end.

(* deep induction principle for ty, mirroring tm_ind2 *)

Fixpoint ty_ind2 (P : ty -> Prop)
  (Hvar : forall n, P (var_ty n))
  (Harr : forall T1 T2, P T1 -> P T2 -> P (TyArr T1 T2))
  (Hforall : forall T1, P T1 -> P (TyForall T1))
  (Hprod : forall p Ts, V.Forall P Ts -> P (TyProd p Ts))
  (Hsum : forall p Ts, V.Forall P Ts -> P (TySum p Ts))
  (T : ty) {struct T} : P T :=
  match T with
  | var_ty n => Hvar n
  | TyArr T1 T2 => Harr T1 T2 (ty_ind2 P Hvar Harr Hforall Hprod Hsum T1)
                             (ty_ind2 P Hvar Harr Hforall Hprod Hsum T2)
  | TyForall T1 => Hforall T1 (ty_ind2 P Hvar Harr Hforall Hprod Hsum T1)
  | TyProd p Ts =>
      let fix allP {p0} (v : V.t ty p0) : V.Forall P v :=
          match v in V.t _ p1 return V.Forall P v with
          | [ ] => V.Forall_nil P
          | T1 ::: v' =>
              V.Forall_cons P T1 v'
                (ty_ind2 P Hvar Harr Hforall Hprod Hsum T1)
                (allP v')
          end
      in Hprod p Ts (allP Ts)
  | TySum p Ts =>
      let fix allP {p0} (v : V.t ty p0) : V.Forall P v :=
          match v in V.t _ p1 return V.Forall P v with
          | [ ] => V.Forall_nil P
          | T1 ::: v' =>
              V.Forall_cons P T1 v'
                (ty_ind2 P Hvar Harr Hforall Hprod Hsum T1)
                (allP v')
          end
      in Hsum p Ts (allP Ts)
  end.

(* terms: tyabs/tyapp add System F-style type abstraction/application *)

Inductive tm : Type :=
  | var_tm : nat -> tm
  | abs : tm -> tm
  | app : tm -> tm -> tm
  | tyabs : tm -> tm
  | tyapp : tm -> ty -> tm
  | tuple : forall p, V.t tm p -> tm
  | proj : forall p, Fin.t p -> tm -> tm
  | inj : forall p, Fin.t p -> tm -> tm
  | case : tm -> forall p, V.t tm p -> tm.

(* ren_tm/subst_tm are two-sorted: a ty-renaming/substitution and a tm-renaming/substitution,
   since tyapp embeds a ty inside a tm and tyabs opens a new ty-scope *)

Fixpoint ren_tm (xi_ty xi_tm : nat -> nat) (t : tm) : tm :=
  match t with
  | var_tm n => var_tm (xi_tm n)
  | abs t1 => abs (ren_tm xi_ty (up_ren xi_tm) t1)
  | app t1 t2 => app (ren_tm xi_ty xi_tm t1) (ren_tm xi_ty xi_tm t2)
  | tyabs t1 => tyabs (ren_tm (up_ren xi_ty) xi_tm t1)
  | tyapp t1 T => tyapp (ren_tm xi_ty xi_tm t1) (ren_ty xi_ty T)
  | tuple p ts => tuple p (V.map (ren_tm xi_ty xi_tm) ts)
  | proj p i t1 => proj p i (ren_tm xi_ty xi_tm t1)
  | inj p i t1 => inj p i (ren_tm xi_ty xi_tm t1)
  | case t1 p fs => case (ren_tm xi_ty xi_tm t1) p (V.map (ren_tm xi_ty xi_tm) fs)
  end.

Definition up_tm (sigma_tm : nat -> tm) : nat -> tm :=
  scons (var_tm 0) (fun n => ren_tm id S (sigma_tm n)).

Definition shift_ty_tm (sigma_tm : nat -> tm) : nat -> tm :=
  fun n => ren_tm S id (sigma_tm n).

Fixpoint subst_tm (sigma_ty : nat -> ty) (sigma_tm : nat -> tm) (t : tm) : tm :=
  match t with
  | var_tm n => sigma_tm n
  | abs t1 => abs (subst_tm sigma_ty (up_tm sigma_tm) t1)
  | app t1 t2 => app (subst_tm sigma_ty sigma_tm t1) (subst_tm sigma_ty sigma_tm t2)
  | tyabs t1 => tyabs (subst_tm (up_ty sigma_ty) (shift_ty_tm sigma_tm) t1)
  | tyapp t1 T => tyapp (subst_tm sigma_ty sigma_tm t1) (subst_ty sigma_ty T)
  | tuple p ts => tuple p (V.map (subst_tm sigma_ty sigma_tm) ts)
  | proj p i t1 => proj p i (subst_tm sigma_ty sigma_tm t1)
  | inj p i t1 => inj p i (subst_tm sigma_ty sigma_tm t1)
  | case t1 p fs => case (subst_tm sigma_ty sigma_tm t1) p (V.map (subst_tm sigma_ty sigma_tm) fs)
  end.

(* deep induction principle *)

Fixpoint tm_ind2 (P : tm -> Prop)
  (Hvar : forall n, P (var_tm n))
  (Habs : forall t1, P t1 -> P (abs t1))
  (Happ : forall t1 t2, P t1 -> P t2 -> P (app t1 t2))
  (Htyabs : forall t1, P t1 -> P (tyabs t1))
  (Htyapp : forall t1 T0, P t1 -> P (tyapp t1 T0))
  (Htuple : forall p ts, V.Forall P ts -> P (tuple p ts))
  (Hproj : forall p i t1, P t1 -> P (proj p i t1))
  (Hinj : forall p i t1, P t1 -> P (inj p i t1))
  (Hcase : forall t1 p fs, P t1 -> V.Forall P fs -> P (case t1 p fs))
  (t : tm) {struct t} : P t :=
  match t with
  | var_tm n => Hvar n
  | abs t1 => Habs t1 (tm_ind2 P Hvar Habs Happ Htyabs Htyapp Htuple Hproj Hinj Hcase t1)
  | app t1 t2 => Happ t1 t2 (tm_ind2 P Hvar Habs Happ Htyabs Htyapp Htuple Hproj Hinj Hcase t1)
                            (tm_ind2 P Hvar Habs Happ Htyabs Htyapp Htuple Hproj Hinj Hcase t2)
  | tyabs t1 => Htyabs t1 (tm_ind2 P Hvar Habs Happ Htyabs Htyapp Htuple Hproj Hinj Hcase t1)
  | tyapp t1 T => Htyapp t1 T (tm_ind2 P Hvar Habs Happ Htyabs Htyapp Htuple Hproj Hinj Hcase t1)
  | tuple p ts =>
      let fix allP {p0} (v : V.t tm p0) : V.Forall P v :=
          match v in V.t _ p1 return V.Forall P v with
          | [ ] => V.Forall_nil P
          | t1 ::: v' =>
              V.Forall_cons P t1 v'
                (tm_ind2 P Hvar Habs Happ Htyabs Htyapp Htuple Hproj Hinj Hcase t1)
                (allP v')
          end
      in Htuple p ts (allP ts)
  | proj p i t1 => Hproj p i t1 (tm_ind2 P Hvar Habs Happ Htyabs Htyapp Htuple Hproj Hinj Hcase t1)
  | inj p i t1 => Hinj p i t1 (tm_ind2 P Hvar Habs Happ Htyabs Htyapp Htuple Hproj Hinj Hcase t1)
  | case t1 p fs =>
      let fix allP {p0} (v : V.t tm p0) : V.Forall P v :=
          match v in V.t _ p1 return V.Forall P v with
          | [ ] => V.Forall_nil P
          | t2 ::: v' =>
              V.Forall_cons P t2 v'
                (tm_ind2 P Hvar Habs Happ Htyabs Htyapp Htuple Hproj Hinj Hcase t2)
                (allP v')
          end
      in Hcase t1 p fs (tm_ind2 P Hvar Habs Happ Htyabs Htyapp Htuple Hproj Hinj Hcase t1) (allP fs)
  end.

Definition context := list ty.

(* surface syntax, fomega_sumprod/PLC-style custom entries *)

Declare Scope sp_scope.
Open Scope sp_scope.

Declare Custom Entry sp_ty.
Declare Custom Entry sp_tm.

Notation "<{{ T }}>" := T (T custom sp_ty at level 99) : sp_scope.

Notation "x" := x (in custom sp_ty at level 0, x constr at level 0) : sp_scope.
Notation "x" := x (in custom sp_tm at level 0, x constr at level 0) : sp_scope.

Notation "( T )" := T (in custom sp_ty at level 0, T custom sp_ty at level 99) : sp_scope.
Notation "T1 -> T2" := (TyArr T1 T2) (in custom sp_ty at level 50, right associativity) : sp_scope.
Notation "'-/,' T" := (TyForall T) (in custom sp_ty at level 90, T custom sp_ty at level 90) : sp_scope.
Notation "{ T }" := T (in custom sp_ty at level 0, T constr at level 99, only parsing) : sp_scope.

Notation "<{ t }>" := t (t custom sp_tm at level 99) : sp_scope.

Notation "( t )" := t (in custom sp_tm at level 0, t custom sp_tm at level 99) : sp_scope.
Notation "t1 t2" := (app t1 t2) (in custom sp_tm at level 11, left associativity) : sp_scope.
Notation "\, t" := (abs t) (in custom sp_tm at level 90, t custom sp_tm at level 90) : sp_scope.
Notation "'\\,' t" := (tyabs t) (in custom sp_tm at level 90, t custom sp_tm at level 90) : sp_scope.
Notation "t [ T ]" := (tyapp t T) (in custom sp_tm at level 11, t custom sp_tm, T custom sp_ty at level 0) : sp_scope.
Notation "{ t }" := t (in custom sp_tm at level 0, t constr at level 99, only parsing) : sp_scope.

Coercion var_tm : nat >-> tm.
Coercion var_ty : nat >-> ty.

(* values *)

Inductive value : tm -> Prop :=
  | V_Abs : forall t, value (abs t)
  | V_TyAbs : forall t, value (tyabs t)
  | V_Tuple : forall p ts, V.Forall value ts -> value (tuple p ts)
  | V_Inj : forall p i t, value t -> value (inj p i t).

(* evaluation *)

Reserved Notation "t '-->' t'" (at level 40).

Inductive step : tm -> tm -> Prop :=
  | ST_AppAbs : forall t v,
      value v -> app (abs t) v --> subst_tm var_ty (scons v var_tm) t
  | ST_App1 : forall t1 t1' t2, t1 --> t1' -> app t1 t2 --> app t1' t2
  | ST_App2 : forall v1 t2 t2', value v1 -> t2 --> t2' -> app v1 t2 --> app v1 t2'
  | ST_TyAppTyAbs : forall t T,
      tyapp (tyabs t) T --> subst_tm (scons T var_ty) var_tm t
  | ST_TyApp1 : forall t t' T, t --> t' -> tyapp t T --> tyapp t' T
  | ST_Tuple : forall p (ts : V.t tm p) (i : Fin.t p) t',
      V.nth ts i --> t' ->
      tuple p ts --> tuple p (V.replace ts i t')
  | ST_ProjRed : forall p (i : Fin.t p) (ts : V.t tm p),
      V.Forall value ts ->
      proj p i (tuple p ts) --> V.nth ts i
  | ST_Proj1 : forall p i t t', t --> t' -> proj p i t --> proj p i t'
  | ST_Inj1 : forall p i t t', t --> t' -> inj p i t --> inj p i t'
  | ST_Case1 : forall t t' p fs, t --> t' -> case t p fs --> case t' p fs
  | ST_Case2 : forall v p (fs : V.t tm p) (j : Fin.t p) t',
      value v -> V.nth fs j --> t' ->
      case v p fs --> case v p (V.replace fs j t')
  | ST_CaseInjRed : forall p (i : Fin.t p) v scrut (fs : V.t tm p) t1,
      scrut = inj p i v -> value v -> V.nth fs i = t1 ->
      case scrut p fs --> app t1 v

where "t '-->' t'" := (step t t').

(* typing *)

Reserved Notation "<[ Gamma |-- t \in T ]>"
  (at level 0, Gamma at level 99, t custom sp_tm, T custom sp_ty).

Inductive has_type (Gamma : context) : tm -> ty -> Prop :=
  | T_Var : forall x T1,
      nth_error Gamma x = Some T1 ->
      <[ Gamma |-- x \in T1 ]>
  | T_Abs : forall T1 T2 t1,
      <[ T1 :: Gamma |-- t1 \in T2 ]> ->
      <[ Gamma |-- \,t1 \in T1 -> T2 ]>
  | T_App : forall T1 T2 t1 t2,
      <[ Gamma |-- t1 \in T1 -> T2 ]> ->
      <[ Gamma |-- t2 \in T1 ]> ->
      <[ Gamma |-- t1 t2 \in T2 ]>
  | T_TyAbs : forall T1 t1,
      has_type (map (ren_ty S) Gamma) t1 T1 ->
      <[ Gamma |-- \\,t1 \in -/, T1 ]>
  | T_TyApp : forall T1 S0 T1' t1,
      <[ Gamma |-- t1 \in -/, T1 ]> ->
      T1' = subst_ty (scons S0 var_ty) T1 ->
      <[ Gamma |-- t1 [S0] \in T1' ]>
  | T_Tuple : forall p (ts : V.t tm p) (Ts : V.t ty p),
      V.Forall2 (has_type Gamma) ts Ts ->
      <[ Gamma |-- {tuple p ts} \in {TyProd p Ts} ]>
  | T_Proj : forall p (i : Fin.t p) (t1 : tm) (Ts : V.t ty p),
      <[ Gamma |-- t1 \in {TyProd p Ts} ]> ->
      <[ Gamma |-- {proj p i t1} \in {V.nth Ts i} ]>
  | T_Inj : forall p (i : Fin.t p) (t1 : tm) (Ts : V.t ty p),
      <[ Gamma |-- t1 \in {V.nth Ts i} ]> ->
      <[ Gamma |-- {inj p i t1} \in {TySum p Ts} ]>
  | T_Case : forall p (t1 : tm) (fs : V.t tm p) (Ts : V.t ty p) (T2 : ty),
      <[ Gamma |-- t1 \in {TySum p Ts} ]> ->
      V.Forall2 (fun t2 Ti => <[ Gamma |-- t2 \in Ti -> T2 ]>) fs Ts ->
      <[ Gamma |-- {case t1 p fs} \in T2 ]>

where "<[ Gamma |-- t \in T ]>" := (has_type Gamma t T) : sp_scope.
