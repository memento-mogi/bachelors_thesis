From Stdlib Require Import Nat List FunctionalExtensionality.
From LF Require Export Definitions.

(* Properties *)

Definition ren_Ki (xi : nat -> nat) (K : Ki) : Ki :=
  subst_Ki (core.funcomp TmVar xi) K.

Lemma up_ren_Tm_TmVar : forall xi n,
  up_Tm_Tm (core.funcomp TmVar xi) n = TmVar (upRen_Tm_Tm xi n).
Proof. intros. destruct n; reflexivity. Qed.

Lemma ren_Ki_Pi : forall xi T K,
  ren_Ki xi (KiPi T K) = KiPi (ren_Ty xi T) (ren_Ki (upRen_Tm_Tm xi) K).
Proof.
  intros. unfold ren_Ki. simpl.
  rewrite <- rinstInst'_Ty.
  f_equal. apply ext_Ki. apply up_ren_Tm_TmVar.
Qed.

Lemma wfDelta_ren_Ki : forall Delta X K xi,
  wf_Delta Delta -> nth_error Delta X = Some K -> ren_Ki xi K = K.
Proof. intros. unfold ren_Ki. apply (H X K H0). Qed.

Lemma subst_ki_tm_betared : forall K v sigma,
  subst_Ki sigma (ki_tm_betared K v) =
  ki_tm_betared (subst_Ki (up_Tm_Tm sigma) K) (subst_Tm sigma v).
Proof.
  intros. unfold ki_tm_betared.
  repeat rewrite substSubst_Ki.
  apply ext_Ki. intros n. destruct n; unfold core.funcomp, sigma_tm_one, up_Tm_Tm, unscoped.scons; simpl.
  - rewrite renSubst_Tm. rewrite renSubst_Tm.
    transitivity (subst_Tm sigma v).
    + apply ext_Tm. intros m. reflexivity.
    + symmetry. transitivity (subst_Tm TmVar (subst_Tm sigma v)).
      * apply ext_Tm. intros m. reflexivity.
      * apply instId'_Tm.
  - unfold core.funcomp. rewrite renSubst_Tm.
    transitivity (subst_Tm TmVar (sigma n)).
    + symmetry. apply instId'_Tm.
    + apply ext_Tm. intros m. destruct m; reflexivity.
Qed.

Lemma ren_ki_tm_betared : forall K v xi,
  ren_Ki xi (ki_tm_betared K v) =
  ki_tm_betared (ren_Ki (upRen_Tm_Tm xi) K) (ren_Tm xi v).
Proof.
  intros. unfold ren_Ki.
  rewrite (subst_ki_tm_betared K v (core.funcomp TmVar xi)).
  f_equal.
  - apply ext_Ki. apply up_ren_Tm_TmVar.
  - symmetry. apply rinstInst'_Tm.
Qed.

(* Basic lemmas on term/type evaluation and equivalence *)
Lemma multi_append :
  forall X R (S T U: X), (multi R S T) /\ (R T U) -> (multi R S U).
Proof.
  intros. destruct H. generalize dependent U.
  induction H; intros.
  - apply multi_step with U.
    + assumption.
    + apply multi_refl.
  - apply multi_step with T2.
    + assumption.
    + apply IHmulti. assumption.
Qed.

Definition tmeval_append := multi_append Tm tm_eval_step.
Definition tmeq_append := multi_append Tm tm_eval_step_lr.
Definition tyeval_append := multi_append Ty ty_eval_step.
Definition tyeq_append := multi_append Ty ty_eval_step_lr.

Lemma tmeval_refl :
  forall t, t ==>tm t.
  induction t; constructor; assumption.
Qed.

Lemma tmeq_sym :
  forall s t, s ===tm t -> t ===tm s.
Proof.
  intros. induction H.
  - apply multi_refl.
  - apply tmeq_append with T2. split.
    + assumption.
    + destruct H; [right | left]; assumption.
Qed.

Lemma tmeq_trans :
  forall s t u, (s ===tm u) /\ (u ===tm t) -> s ===tm t.
Proof.
  intros. destruct H as [HS HT].
  generalize dependent t. induction HS; intros u H1.
  - assumption.
  - apply multi_step with T2.
    + assumption.
    + apply IHHS. assumption.
Qed.

Lemma multi_step_implies_tmeq :
  forall s t, multi tm_eval_step s t -> s ===tm t.
Proof.
  intros. induction H.
  - apply multi_refl.
  - apply multi_step with T2.
    + left. assumption.
    + apply IHmulti.
Qed.

Lemma tyeval_refl :
  forall T, T ==>ty T.
Proof.
  induction T.
  - apply TST_Var.
  - apply TST_Pi; assumption.
  - apply TST_App; [assumption | apply tmeval_refl].
  - apply TST_Unit.
Qed.

Lemma tyeq_sym :
  forall S T, S ===ty T -> T ===ty S.
Proof.
  intros. induction H.
  - apply multi_refl.
  - apply tyeq_append with T2. split.
    + assumption.
    + destruct H; [right | left]; assumption.
Qed.

Lemma tyeq_trans :
  forall S T U, (S ===ty U) /\ (U ===ty T) -> S ===ty T.
Proof.
  intros. destruct H as [HS HT].
  generalize dependent T. induction HS; intros U H1.
  - assumption.
  - apply multi_step with T2.
    + assumption.
    + apply IHHS. assumption.
Qed.

Lemma multi_step_implies_tyeq :
  forall S T, multi ty_eval_step S T -> S ===ty T.
Proof.
  intros. induction H.
  - apply multi_refl.
  - apply multi_step with T2.
    + left. assumption.
    + apply IHmulti.
Qed.

(* Renaming *)
Lemma ren_tm_betared : forall t v xi,
  ren_Tm xi (tm_tm_betared t v) =
  tm_tm_betared (ren_Tm (upRen_Tm_Tm xi) t) (ren_Tm xi v).
Proof.
  intros. unfold tm_tm_betared.
  rewrite renRen_Tm. rewrite substRen_Tm.
  rewrite renSubst_Tm. rewrite substRen_Tm.
  apply ext_Tm. intros n. destruct n; unfold core.funcomp, sigma_tm_one; simpl.
  - rewrite renRen_Tm. rewrite renRen_Tm. rewrite renRen_Tm.
    apply extRen_Tm. intros m. reflexivity.
  - reflexivity.
Qed.

Lemma ren_ty_tm_betared : forall T v xi,
  ren_Ty xi (ty_tm_betared T v) =
  ty_tm_betared (ren_Ty (upRen_Tm_Tm xi) T) (ren_Tm xi v).
Proof.
  intros. unfold ty_tm_betared.
  rewrite renRen_Ty. rewrite substRen_Ty.
  rewrite renSubst_Ty. rewrite substRen_Ty.
  apply ext_Ty. intros n. destruct n; unfold core.funcomp, sigma_tm_one; simpl.
  - rewrite renRen_Tm. rewrite renRen_Tm. rewrite renRen_Tm.
    apply extRen_Tm. intros m. reflexivity.
  - reflexivity.
Qed.

Lemma ren_tmeval : forall t1 t2,
  t1 ==>tm t2 ->
  forall xi,
  (ren_Tm xi t1) ==>tm (ren_Tm xi t2).
Proof.
  intros t1 t2 H. induction H; intros; asolve;
  try (constructor;
       try apply IHtm_eval_step;
       try apply IHtm_eval_step1;
       try apply IHtm_eval_step2
    ).
  - subst t'. eapply TMST_Red.
    + eapply IHtm_eval_step1.
    + eapply IHtm_eval_step2.
    + apply ren_tm_betared.
Qed.

Lemma ren_tmeq : forall t1 t2,
  t1 ===tm t2 ->
  forall xi,
  (ren_Tm xi t1) ===tm (ren_Tm xi t2).
Proof.
  intros t1 t2 H. induction H; intros; asolve.
  - apply multi_refl.
  - apply multi_step with (T2:=ren_Tm xi T2).
    + destruct H; [left | right]; apply ren_tmeval; assumption.
    + apply IHmulti.
Qed.

Lemma ren_tyeval : forall T1 T2,
  T1 ==>ty T2 ->
  forall xi,
  (ren_Ty xi T1) ==>ty (ren_Ty xi T2).
Proof.
  intros T1 T2 H. induction H; intros; asolve.
  - constructor.
  - constructor.
  - constructor; [apply IHty_eval_step1 | apply IHty_eval_step2].
  - constructor; [apply IHty_eval_step | apply ren_tmeval; assumption].
  - subst S. eapply TST_Red.
    + eapply IHty_eval_step.
    + eapply ren_tmeval. eassumption.
    + apply ren_ty_tm_betared.
Qed.

Lemma ren_tyeq : forall T1 T2,
  T1 ===ty T2 ->
  forall xi,
  (ren_Ty xi T1) ===ty (ren_Ty xi T2).
Proof.
  intros T1 T2 H. induction H; intros; asolve.
  - apply multi_refl.
  - apply multi_step with (T2:=ren_Ty xi T2).
    + destruct H; [left | right]; apply ren_tyeval; assumption.
    + apply IHmulti.
Qed.

Lemma ren_kieq : forall K J,
  K ===ki J ->
  forall xi, ren_Ki xi K ===ki ren_Ki xi J.
Proof.
  intros K J H. induction H; intros xi.
  - unfold ren_Ki. simpl. apply KiEq_Star.
  - rewrite ren_Ki_Pi. rewrite ren_Ki_Pi.
    apply KiEq_Pi.
    + apply ren_tyeq. assumption.
    + apply IHki_eq.
Qed.

(* Substitution *)
Lemma subst_tm_betared : forall t v sigma,
  subst_Tm sigma (tm_tm_betared t v) =
  tm_tm_betared (subst_Tm (up_Tm_Tm sigma) t) (subst_Tm sigma v).
Proof.
  intros. unfold tm_tm_betared.
  rewrite renSubst_Tm. rewrite substSubst_Tm.
  rewrite substSubst_Tm. rewrite substRen_Tm.
  apply ext_Tm. intros n. destruct n; unfold core.funcomp, sigma_tm_one; simpl.
  - rewrite renSubst_Tm. rewrite renRen_Tm.
    transitivity (subst_Tm sigma v).
    + apply ext_Tm. intros m. unfold core.funcomp. reflexivity.
    + symmetry. rewrite (extRen_Tm (core.funcomp Nat.pred S) id (fun m => eq_refl)).
      apply rinstId'_Tm.
  - unfold core.funcomp. rewrite renSubst_Tm.
    symmetry.
    transitivity (ren_Tm Nat.pred (ren_Tm unscoped.shift (sigma n))).
    + f_equal. rewrite (rinstInst'_Tm unscoped.shift (sigma n)).
      apply ext_Tm. intros m. unfold core.funcomp. simpl. reflexivity.
    + rewrite renRen_Tm.
      rewrite (extRen_Tm (core.funcomp Nat.pred unscoped.shift) id (fun m => eq_refl)).
      apply rinstId'_Tm.
Qed.

Lemma subst_ty_tm_betared : forall T v sigma,
  subst_Ty sigma (ty_tm_betared T v) =
  ty_tm_betared (subst_Ty (up_Tm_Tm sigma) T) (subst_Tm sigma v).
Proof.
  intros. unfold ty_tm_betared.
  rewrite renSubst_Ty. rewrite substSubst_Ty.
  rewrite substSubst_Ty. rewrite substRen_Ty.
  apply ext_Ty. intros n. destruct n; unfold core.funcomp, sigma_tm_one; simpl.
  - rewrite renSubst_Tm. rewrite renRen_Tm.
    transitivity (subst_Tm sigma v).
    + apply ext_Tm. intros m. unfold core.funcomp. reflexivity.
    + symmetry. rewrite (extRen_Tm (core.funcomp Nat.pred S) id (fun m => eq_refl)).
      apply rinstId'_Tm.
  - unfold core.funcomp. rewrite renSubst_Tm.
    symmetry.
    transitivity (ren_Tm Nat.pred (ren_Tm unscoped.shift (sigma n))).
    + f_equal. rewrite (rinstInst'_Tm unscoped.shift (sigma n)).
      apply ext_Tm. intros m. unfold core.funcomp. simpl. reflexivity.
    + rewrite renRen_Tm.
      rewrite (extRen_Tm (core.funcomp Nat.pred unscoped.shift) id (fun m => eq_refl)).
      apply rinstId'_Tm.
Qed.

Lemma subst_tmeval : forall t1 t2,
  t1 ==>tm t2 ->
  forall sigma,
  (subst_Tm sigma t1) ==>tm (subst_Tm sigma t2).
Proof.
  intros t1 t2 H. induction H; intros; asolve;
  try (constructor;
       try apply IHtm_eval_step;
       try apply IHtm_eval_step1;
       try apply IHtm_eval_step2
    ).
  - apply tmeval_refl.
  - subst t'. eapply TMST_Red.
    + eapply IHtm_eval_step1.
    + eapply IHtm_eval_step2.
    + apply subst_tm_betared.
Qed.

Lemma subst_tmeq : forall t1 t2,
  t1 ===tm t2 ->
  forall sigma,
  (subst_Tm sigma t1) ===tm (subst_Tm sigma t2).
Proof.
  intros t1 t2 H. induction H; intros.
  - apply multi_refl.
  - apply multi_step with (T2:=subst_Tm sigma T2).
    + destruct H; [left|right]; apply subst_tmeval; assumption.
    + apply IHmulti.
Qed.

Lemma subst_tyeval : forall T1 T2,
  T1 ==>ty T2 ->
  forall sigma,
  (subst_Ty sigma T1) ==>ty (subst_Ty sigma T2).
Proof.
  intros T1 T2 H. induction H; intros; asolve.
  - constructor.
  - constructor.
  - constructor; [apply IHty_eval_step1 | apply IHty_eval_step2].
  - constructor; [apply IHty_eval_step | apply subst_tmeval; assumption].
  - subst S. eapply TST_Red.
    + eapply IHty_eval_step.
    + eapply subst_tmeval. eassumption.
    + apply subst_ty_tm_betared.
Qed.

Lemma subst_tyeq : forall T1 T2,
  T1 ===ty T2 ->
  forall sigma,
  (subst_Ty sigma T1) ===ty (subst_Ty sigma T2).
Proof.
  intros T1 T2 H. induction H; intros.
  - apply multi_refl.
  - apply multi_step with (T2:=subst_Ty sigma T2).
    + destruct H; [left|right]; apply subst_tyeval; assumption.
    + apply IHmulti.
Qed.

Lemma subst_kieq : forall K J,
  K ===ki J ->
  forall sigma, subst_Ki sigma K ===ki subst_Ki sigma J.
Proof.
  intros K J H. induction H; intros sigma.
  - simpl. apply KiEq_Star.
  - simpl. apply KiEq_Pi.
    + apply subst_tyeq. assumption.
    + apply IHki_eq.
Qed.

(* weakening / substitution helpers for the self-shifted Gamma *)
Lemma ren_shift_up_ty : forall xi (T : Ty),
  ren_Ty (upRen_Tm_Tm xi) (ren_Ty Datatypes.S T) = ren_Ty Datatypes.S (ren_Ty xi T).
Proof.
  intros. rewrite renRen_Ty. rewrite renRen_Ty.
  apply extRen_Ty. intros n. reflexivity.
Qed.

Lemma subst_shift_up_ty : forall sigma (T : Ty),
  subst_Ty (up_Tm_Tm sigma) (ren_Ty Datatypes.S T) = ren_Ty Datatypes.S (subst_Ty sigma T).
Proof.
  intros. rewrite renSubst_Ty. rewrite substRen_Ty.
  apply ext_Ty. intros n. reflexivity.
Qed.

Lemma nth_error_up_cons : forall Gamma Gamma' xi T,
  (forall x S, nth_error Gamma x = Some S -> nth_error Gamma' (xi x) = Some (ren_Ty xi S)) ->
  forall x S,
    nth_error ((ren_Ty Datatypes.S T) :: map (ren_Ty Datatypes.S) Gamma) x = Some S ->
    nth_error ((ren_Ty Datatypes.S (ren_Ty xi T)) :: map (ren_Ty Datatypes.S) Gamma') (upRen_Tm_Tm xi x) = Some (ren_Ty (upRen_Tm_Tm xi) S).
Proof.
  intros Gamma Gamma' xi T Hxi x S Hx.
  destruct x as [|x']; simpl in Hx.
  - inversion Hx; subst. simpl. rewrite ren_shift_up_ty. reflexivity.
  - rewrite nth_error_map in Hx.
    destruct (nth_error Gamma x') as [S1|] eqn:EqG; try discriminate.
    simpl in Hx. inversion Hx; subst.
    simpl. rewrite nth_error_map. rewrite (Hxi x' S1 EqG). simpl.
    rewrite ren_shift_up_ty. reflexivity.
Qed.

Lemma ren_typing :
  (forall Delta Gamma T K,
   <[[ Delta | Gamma |-- T \in K ]]> ->
   wf_Delta Delta ->
   forall Gamma' xi,
   (forall x S, nth_error Gamma x = Some S -> nth_error Gamma' (xi x) = Some (ren_Ty xi S)) ->
   <[[ Delta | Gamma' |-- {ren_Ty xi T} \in {ren_Ki xi K} ]]>)
  /\
  (forall Delta Gamma t T,
   <[ Delta | Gamma |-- t \in T ]> ->
   wf_Delta Delta ->
   forall Gamma' xi,
   (forall x S, nth_error Gamma x = Some S -> nth_error Gamma' (xi x) = Some (ren_Ty xi S)) ->
   <[ Delta | Gamma' |-- {ren_Tm xi t} \in {ren_Ty xi T} ]>).
Proof.
  apply has_kind_has_type_mutind; intros.
  - rewrite (wfDelta_ren_Ki Delta X K xi H e). apply K_Var. assumption.
  - subst GammaS. eapply K_Pi.
    + apply H; assumption.
    + reflexivity.
    + apply H0; try assumption. apply nth_error_up_cons. assumption.
  - subst K'.
    assert (HS' : <[[ Delta | Gamma' |-- {ren_Ty xi S} \in {KiPi (ren_Ty xi T) (ren_Ki (upRen_Tm_Tm xi) K)} ]]>).
    { rewrite <- ren_Ki_Pi. apply H; assumption. }
    eapply K_App.
    + exact HS'.
    + apply H0; assumption.
    + apply ren_ki_tm_betared.
  - eapply K_Conv.
    + apply H; assumption.
    + apply ren_kieq. assumption.
  - apply K_Unit.
  - apply T_Var. apply H0. assumption.
  - subst GammaS. eapply T_Abs.
    + apply H; assumption.
    + reflexivity.
    + apply H0; try assumption. apply nth_error_up_cons. assumption.
  - subst S'. eapply T_App.
    + apply H; assumption.
    + apply H0; assumption.
    + apply ren_ty_tm_betared.
  - eapply T_Conv.
    + apply H; assumption.
    + apply ren_tyeq. assumption.
    + apply H0; assumption.
  - apply T_Unit.
Qed.

Definition ren_kinding := proj1 ren_typing.
Definition ren_has_type := proj2 ren_typing.

Lemma nth_error_subst_cons : forall Delta Gamma Gamma' sigma T,
  wf_Delta Delta ->
  (forall x S, nth_error Gamma x = Some S -> <[ Delta | Gamma' |-- {sigma x} \in {subst_Ty sigma S} ]>) ->
  forall x S,
    nth_error ((ren_Ty Datatypes.S T) :: map (ren_Ty Datatypes.S) Gamma) x = Some S ->
    <[ Delta | (ren_Ty Datatypes.S (subst_Ty sigma T)) :: map (ren_Ty Datatypes.S) Gamma' |-- {up_Tm_Tm sigma x} \in {subst_Ty (up_Tm_Tm sigma) S} ]>.
Proof.
  intros Delta Gamma Gamma' sigma T HWD Hsig x S Hx.
  destruct x as [|x']; simpl in Hx.
  - inversion Hx; subst. simpl. rewrite subst_shift_up_ty. apply T_Var. reflexivity.
  - rewrite nth_error_map in Hx.
    destruct (nth_error Gamma x') as [S1|] eqn:EqG; try discriminate.
    simpl in Hx. inversion Hx; subst.
    simpl. rewrite subst_shift_up_ty.
    eapply ren_has_type.
    + apply Hsig. eassumption.
    + assumption.
    + intros y T' Hy. simpl. rewrite nth_error_map. rewrite Hy. reflexivity.
Qed.

Lemma subst_typing :
  (forall Delta Gamma T K,
   <[[ Delta | Gamma |-- T \in K ]]> ->
   wf_Delta Delta ->
   forall Gamma' sigma,
   (forall x S, nth_error Gamma x = Some S -> <[ Delta | Gamma' |-- {sigma x} \in {subst_Ty sigma S} ]>) ->
   <[[ Delta | Gamma' |-- {subst_Ty sigma T} \in {subst_Ki sigma K} ]]>)
  /\
  (forall Delta Gamma t T,
   <[ Delta | Gamma |-- t \in T ]> ->
   wf_Delta Delta ->
   forall Gamma' sigma,
   (forall x S, nth_error Gamma x = Some S -> <[ Delta | Gamma' |-- {sigma x} \in {subst_Ty sigma S} ]>) ->
   <[ Delta | Gamma' |-- {subst_Tm sigma t} \in {subst_Ty sigma T} ]>).
Proof.
  apply has_kind_has_type_mutind; intros.
  - rewrite (H X K e sigma). apply K_Var. assumption.
  - subst GammaS. eapply K_Pi with (GammaS := (ren_Ty Datatypes.S (subst_Ty sigma T)) :: map (ren_Ty Datatypes.S) Gamma').
    + apply H; assumption.
    + reflexivity.
    + apply H0; try assumption. eapply nth_error_subst_cons; eassumption.
  - subst K'. eapply K_App.
    + apply H; assumption.
    + apply H0; assumption.
    + apply subst_ki_tm_betared.
  - eapply K_Conv.
    + apply H; assumption.
    + apply subst_kieq. assumption.
  - apply K_Unit.
  - apply H0. assumption.
  - subst GammaS. eapply T_Abs with (GammaS := (ren_Ty Datatypes.S (subst_Ty sigma T)) :: map (ren_Ty Datatypes.S) Gamma').
    + apply H; assumption.
    + reflexivity.
    + apply H0; try assumption. eapply nth_error_subst_cons; eassumption.
  - subst S'. eapply T_App.
    + apply H; assumption.
    + apply H0; assumption.
    + apply subst_ty_tm_betared.
  - eapply T_Conv.
    + apply H; assumption.
    + apply subst_tyeq. assumption.
    + apply H0; assumption.
  - apply T_Unit.
Qed.

Definition subst_kinding := proj1 subst_typing.
Definition subst_has_type := proj2 subst_typing.

(* context extension for wf *)
Lemma wf_cons : forall Delta Gamma T,
  wf_Delta Delta ->
  wf Delta Gamma ->
  <[[ Delta | Gamma |-- T \in * ]]> ->
  wf Delta ((ren_Ty Datatypes.S T) :: map (ren_Ty Datatypes.S) Gamma).
Proof.
  intros Delta Gamma T HWD HW HT x S Hx.
  destruct x as [|x']; simpl in Hx.
  - inversion Hx; subst.
    eapply ren_kinding with (K := KiStar).
    + exact HT.
    + exact HWD.
    + intros y S0 Hy. simpl. rewrite nth_error_map. rewrite Hy. reflexivity.
  - rewrite nth_error_map in Hx.
    destruct (nth_error Gamma x') as [S1|] eqn:EqG; try discriminate.
    simpl in Hx. inversion Hx; subst.
    eapply ren_kinding with (K := KiStar).
    + exact (HW x' S1 EqG).
    + exact HWD.
    + intros y S0 Hy. simpl. rewrite nth_error_map. rewrite Hy. reflexivity.
Qed.

(* inversion for has_kind on a Pi-type, through arbitrarily many K_Conv wraps *)
Lemma kinding_pi_form : forall Delta Gamma T S K,
  <[[ Delta | Gamma |-- \:T, S \in K ]]> ->
  <[[ Delta | Gamma |-- T \in * ]]> /\
  <[[ Delta | (ren_Ty Datatypes.S T) :: map (ren_Ty Datatypes.S) Gamma |-- S \in * ]]>.
Proof.
  intros Delta Gamma T S K H.
  remember <{{\:T,S}}> as Ty0.
  generalize dependent HeqTy0.
  induction H; try discriminate; intros.
  - inversion HeqTy0; subst. split; assumption.
  - apply IHhas_kind. assumption.
Qed.

Lemma pop_subst_ty_tm_betared : forall T v,
  ty_tm_betared T v =
  subst_Ty (fun n => match n with 0 => v | Datatypes.S n' => TmVar n' end) T.
Proof.
  intros. unfold ty_tm_betared.
  rewrite substRen_Ty.
  apply ext_Ty. intros n. destruct n; unfold core.funcomp, sigma_tm_one; simpl.
  - rewrite renRen_Tm.
    rewrite (extRen_Tm (core.funcomp Nat.pred S) id (fun m => eq_refl)).
    apply rinstId'_Tm.
  - reflexivity.
Qed.

Lemma pop_subst_ki_tm_betared : forall K v,
  ki_tm_betared K v =
  subst_Ki (fun n => match n with 0 => v | Datatypes.S n' => TmVar n' end) K.
Proof.
  intros. unfold ki_tm_betared.
  rewrite substSubst_Ki.
  apply ext_Ki. intros n. destruct n; unfold core.funcomp, sigma_tm_one; simpl.
  - rewrite renSubst_Tm.
    transitivity (subst_Tm TmVar v).
    + apply ext_Tm. intros m. reflexivity.
    + apply instId'_Tm.
  - reflexivity.
Qed.

Lemma pop_subst_tm_tm_betared : forall t v,
  tm_tm_betared t v =
  subst_Tm (fun n => match n with 0 => v | Datatypes.S n' => TmVar n' end) t.
Proof.
  intros. unfold tm_tm_betared.
  rewrite substRen_Tm.
  apply ext_Tm. intros n. destruct n; unfold core.funcomp, sigma_tm_one; simpl.
  - rewrite renRen_Tm.
    rewrite (extRen_Tm (core.funcomp Nat.pred S) id (fun m => eq_refl)).
    apply rinstId'_Tm.
  - reflexivity.
Qed.

Lemma pop_subst_kinding : forall Delta T' Gamma T K v,
  wf_Delta Delta ->
  <[[ Delta | (ren_Ty Datatypes.S T') :: map (ren_Ty Datatypes.S) Gamma |-- T \in K ]]> ->
  <[ Delta | Gamma |-- v \in T' ]> ->
  <[[ Delta | Gamma |-- {subst_Ty (fun n => match n with
                           0 => v | Datatypes.S n' => TmVar n' end) T}
      \in {subst_Ki (fun n => match n with 0 => v | Datatypes.S n' => TmVar n' end) K} ]]>.
Proof.
  intros Delta T' Gamma T K v HWD HT Hv.
  eapply subst_kinding.
  - eassumption.
  - assumption.
  - intros x S0 Hx. destruct x as [|x']; simpl in Hx.
    + inversion Hx; subst. simpl.
      assert (Heq : subst_Ty (fun n => match n with
                      0 => v | Datatypes.S n' => TmVar n' end) (ren_Ty Datatypes.S T') = T').
      { rewrite renSubst_Ty. apply idSubst_Ty. intros m. reflexivity. }
      rewrite Heq. assumption.
    + rewrite nth_error_map in Hx.
      destruct (nth_error Gamma x') as [S1|] eqn:EqG; try discriminate.
      simpl in Hx. inversion Hx; subst.
      assert (Heq : subst_Ty (fun n => match n with
                      0 => v | Datatypes.S n' => TmVar n' end) (ren_Ty Datatypes.S S1) = S1).
      { rewrite renSubst_Ty. apply idSubst_Ty. intros m. reflexivity. }
      rewrite Heq. apply T_Var. assumption.
Qed.

Lemma pop_subst_has_type : forall Delta T' Gamma t T v,
  wf_Delta Delta ->
  <[ Delta | (ren_Ty Datatypes.S T') :: map (ren_Ty Datatypes.S) Gamma |-- t \in T ]> ->
  <[ Delta | Gamma |-- v \in T' ]> ->
  <[ Delta | Gamma |-- {subst_Tm (fun n => match n with
                           0 => v | Datatypes.S n' => TmVar n' end) t}
      \in {subst_Ty (fun n => match n with 0 => v | Datatypes.S n' => TmVar n' end) T} ]>.
Proof.
  intros Delta T' Gamma t T v HWD Ht Hv.
  eapply subst_has_type.
  - eassumption.
  - assumption.
  - intros x S0 Hx. destruct x as [|x']; simpl in Hx.
    + inversion Hx; subst. simpl.
      assert (Heq : subst_Ty (fun n => match n with
                      0 => v | Datatypes.S n' => TmVar n' end) (ren_Ty Datatypes.S T') = T').
      { rewrite renSubst_Ty. apply idSubst_Ty. intros m. reflexivity. }
      rewrite Heq. assumption.
    + rewrite nth_error_map in Hx.
      destruct (nth_error Gamma x') as [S1|] eqn:EqG; try discriminate.
      simpl in Hx. inversion Hx; subst.
      assert (Heq : subst_Ty (fun n => match n with
                      0 => v | Datatypes.S n' => TmVar n' end) (ren_Ty Datatypes.S S1) = S1).
      { rewrite renSubst_Ty. apply idSubst_Ty. intros m. reflexivity. }
      rewrite Heq. apply T_Var. assumption.
Qed.

(* Regularity *)
Lemma regularity :
  forall Delta Gamma t T,
  <[ Delta | Gamma |-- t \in T ]> ->
  wf_Delta Delta ->
  wf Delta Gamma ->
  <[[ Delta | Gamma |-- T \in * ]]>.
Proof.
  intros Delta Gamma t T H.
  induction H; intros HWD HW.
  - exact (HW x T H).
  - subst GammaS. eapply K_Pi.
    + assumption.
    + reflexivity.
    + apply IHhas_type; try assumption. apply wf_cons; assumption.
  - pose proof (IHhas_type1 HWD HW) as HK.
    apply kinding_pi_form in HK as [HKT HKS].
    subst S'. rewrite pop_subst_ty_tm_betared.
    change <{|*|}> with (subst_Ki (fun n => match n with
                            0 => t2 | Datatypes.S n' => TmVar n' end) KiStar).
    apply pop_subst_kinding with (T':=T); assumption.
  - assumption.
  - apply K_Unit.
Qed.

(* confluence for terms (unaffected by the type-level redesign) *)
Lemma tmsubst_tmeval_lemma :
  forall t t',
  t ==>tm t' ->
  forall sigma sigma' : nat -> Tm,
  (forall n, (sigma n) ==>tm (sigma' n)) ->
  subst_Tm sigma t ==>tm subst_Tm sigma' t'.
Proof.
  intros t t' H. induction H; intros; asolve.
  - constructor.
  - constructor. apply IHtm_eval_step. intros. destruct n.
    + constructor.
    + apply ren_tmeval. apply H0.
  - constructor; [apply IHtm_eval_step1 | apply IHtm_eval_step2]; assumption.
  - eapply TMST_Red with (t1' := subst_Tm (up_Tm_Tm sigma') t1').
    + apply IHtm_eval_step1. intros n. destruct n.
      * constructor.
      * apply ren_tmeval. apply H2.
    + apply IHtm_eval_step2. apply H2.
    + subst t'. apply subst_tm_betared.
Qed.

Lemma tmtmbetared_tmeval_lemma :
  forall t1 t2 t1' t2',
    (t1 ==>tm t1') ->
    (t2 ==>tm t2') ->
    tm_tm_betared t1 t2 ==>tm tm_tm_betared t1' t2'.
Proof.
  intros. unfold tm_tm_betared.
  apply ren_tmeval. apply tmsubst_tmeval_lemma.
  - assumption.
  - intros. destruct n; unfold sigma_tm_one; asolve.
    + apply ren_tmeval. assumption.
    + constructor.
Qed.

Lemma confluence_single_tm :
  forall t1 t2 t3,
    (t1 ==>tm t2) /\ (t1 ==>tm t3) ->
    exists t4, (t2 ==>tm t4) /\ (t3 ==>tm t4).
Proof.
  intros. destruct H as [HT HU].
  generalize dependent t3. induction HT; intros;
  try (inversion HU; eexists; split; constructor; fail).
  - inversion HU; subst.
    apply IHHT in H2 as [V' [IHT IHU ] ].
    exists (<{\:T2,V'}>). split; constructor; assumption.
  - inversion HU.
    + apply IHHT1 in H1 as [V1 [IH11 IH12] ].
      apply IHHT2 in H3 as [V2 [IH21 IH22] ].
      eexists. split; apply TMST_App; eassumption.
    + subst t1.
      assert (HT1' : <{\:T,t0}> ==>tm <{\:T,t1'0}>).
      { constructor. exact H1. }
      inversion HT1; subst.
      apply IHHT1 in HT1' as [V1 [IH11 IH12] ].
      inversion IH11; subst.
      inversion IH12; subst.
      apply IHHT2 in H2 as [V2 [IH21 IH22] ].
      exists (tm_tm_betared t1' V2). split.
      * eapply TMST_Red; [exact H4 | exact IH21 | reflexivity].
      * apply tmtmbetared_tmeval_lemma; assumption.
  - inversion HU.
    + subst t3. subst t0. subst t4.
      inversion H2; subst.
      apply IHHT1 in H5 as [V1 [IH11 IH12] ].
      apply IHHT2 in H4 as [V2 [IH21 IH22] ].
      exists (tm_tm_betared V1 V2). split.
      * apply tmtmbetared_tmeval_lemma; assumption.
      * eapply TMST_Red; try eassumption. reflexivity.
    + apply IHHT1 in H3 as [V1 [IH11 IH12] ].
      apply IHHT2 in H5 as [V2 [IH21 IH22] ].
      exists (tm_tm_betared V1 V2). split.
      * subst t'. apply tmtmbetared_tmeval_lemma; assumption.
      * subst t3. apply tmtmbetared_tmeval_lemma; assumption.
Qed.

Lemma confluence_multi_single_tm :
  forall t1 t2 t3,
  multi tm_eval_step t1 t2 /\ (t1 ==>tm t3) ->
  exists t4, (t2 ==>tm t4) /\ multi tm_eval_step t3 t4.
Proof.
  intros. destruct H as [HT HU].
  generalize dependent t3. induction HT; intros.
  - exists t3. split.
    + assumption.
    + constructor.
  - assert (HV': exists V', (T2==>tm V') /\ (t3==>tm V')).
    + eapply confluence_single_tm; split; eassumption.
    + destruct HV' as [V' [HV'1 HV'2] ].
      apply IHHT in HV'1 as [V0 [HV'11 HV'12 ] ].
      exists V0. split.
      * assumption.
      * econstructor; eassumption.
Qed.

Lemma confluence_multi_tm :
  forall t1 t2 t3,
    multi tm_eval_step t1 t2 /\ multi tm_eval_step t1 t3 ->
    exists t4, multi tm_eval_step t2 t4 /\ multi tm_eval_step t3 t4.
Proof.
  intros. destruct H as [HT HU].
  generalize dependent t3. induction HT; intros.
  - exists t3. split. + assumption. + constructor.
  - assert (HV': exists V', ((t3 ==>tm V') /\ multi tm_eval_step T2 V')).
    + apply confluence_multi_single_tm with T1. split; assumption.
    + destruct HV' as [V' [HV'1 HV'2] ].
      apply IHHT in HV'2 as [V0 [HV'11 HV'12 ] ].
      exists V0. split.
      * assumption.
      * econstructor; eassumption.
Qed.

Lemma tmeq_implies_confluence :
  forall t1 t2,
    (t1 ===tm t2) ->
    exists t3, multi tm_eval_step t1 t3 /\ multi tm_eval_step t2 t3.
Proof.
  intros. induction H.
  - exists T. split; constructor.
  - destruct IHmulti as [U' [IH2 IH3] ].
    destruct H.
    + exists U'. split.
      * econstructor; eassumption.
      * assumption.
    + assert (exists V, (U' ==>tm V) /\ multi tm_eval_step T1 V).
      * apply confluence_multi_single_tm with T2. split; assumption.
      * destruct H1 as [V [HU HT3] ]. exists V. split; try assumption.
        eapply multi_append. split; eassumption.
Qed.

Lemma tysubst_tmeval_lemma :
  forall T T',
  T ==>ty T' ->
  forall sigma sigma' : nat -> Tm,
  (forall n, (sigma n) ==>tm (sigma' n)) ->
  subst_Ty sigma T ==>ty subst_Ty sigma' T'.
Proof.
  intros T T' H. induction H; intros; asolve.
  - constructor.
  - constructor.
  - constructor.
    + apply IHty_eval_step1. assumption.
    + apply IHty_eval_step2. intros n. destruct n.
      * constructor.
      * apply ren_tmeval. apply H1.
  - constructor.
    + apply IHty_eval_step. assumption.
    + apply tmsubst_tmeval_lemma; assumption.
  - eapply TST_Red with (S2:=subst_Ty (up_Tm_Tm sigma') S2).
    + eapply IHty_eval_step. intros n. destruct n.
      * constructor.
      * apply ren_tmeval. apply H2.
    + apply tmsubst_tmeval_lemma; eassumption.
    + subst S. apply subst_ty_tm_betared.
Qed.

Lemma tytmbetared_tyeval_lemma :
  forall T1 T2 t1 t2,
    (T1 ==>ty T2) ->
    (t1 ==>tm t2) ->
    ty_tm_betared T1 t1 ==>ty ty_tm_betared T2 t2.
Proof.
  intros. unfold ty_tm_betared.
  apply ren_tyeval. apply tysubst_tmeval_lemma.
  - assumption.
  - intros. destruct n; unfold sigma_tm_one; asolve.
    + apply ren_tmeval. assumption.
    + constructor.
Qed.

Lemma confluence_single_ty :
  forall T1 T2 T3,
    (T1 ==>ty T2) /\ (T1 ==>ty T3) ->
    exists T4, (T2 ==>ty T4) /\ (T3 ==>ty T4).
Proof.
  intros. destruct H as [HT HU].
  generalize dependent T3. induction HT; intros;
  try (inversion HU; eexists; split; constructor; fail).
  - inversion HU; subst.
    apply IHHT1 in H1 as [VT [IHT1 IHT2] ].
    apply IHHT2 in H3 as [VS [IHS1 IHS2] ].
    exists (<{{\:VT,VS}}>). split; constructor; assumption.
  - inversion HU.
    + apply IHHT in H2 as [VT [IHT1 IHT2] ].
      destruct (confluence_single_tm t t' t'0 (conj H H4)) as [Vt [IHt1 IHt2] ].
      exists (<{{VT Vt}}>). split; apply TST_App; assumption.
    + subst T1.
      assert (HT1' : <{{\:T,S0}}> ==>ty <{{\:T,S2}}>).
      { constructor.
        - apply tyeval_refl.
        - exact H2. }
      inversion HT; subst.
      apply IHHT in HT1' as [V1 [IH11 IH12] ].
      inversion IH11; subst.
      inversion IH12; subst.
      destruct (confluence_single_tm t t' t'0 (conj H H3)) as [Vt [IHt1 IHt2] ].
      exists (ty_tm_betared S3 Vt). split.
      * eapply TST_Red; [exact H6 | exact IHt1 | reflexivity].
      * apply tytmbetared_tyeval_lemma; [exact H11 | exact IHt2].
  - inversion HU.
    + inversion H3; subst.
      apply IHHT in H10 as [V1 [IH11 IH12] ].
      destruct (confluence_single_tm t t' t'0 (conj H H5)) as [Vt [IHt1 IHt2] ].
      exists (ty_tm_betared V1 Vt). split.
      * apply tytmbetared_tyeval_lemma; assumption.
      * eapply TST_Red; [exact IH12 | exact IHt2 | reflexivity].
    + apply IHHT in H4 as [V1 [IH11 IH12] ].
      destruct (confluence_single_tm t t' t'0 (conj H H6)) as [Vt [IHt1 IHt2] ].
      exists (ty_tm_betared V1 Vt). split.
      * subst S. apply tytmbetared_tyeval_lemma; assumption.
      * subst T3. apply tytmbetared_tyeval_lemma; assumption.
Qed.

Lemma confluence_multi_single_ty :
  forall T1 T2 T3,
  multi ty_eval_step T1 T2 /\ (T1 ==>ty T3) ->
  exists T4, (T2 ==>ty T4) /\ multi ty_eval_step T3 T4.
Proof.
  intros. destruct H as [HT HU].
  generalize dependent T3. induction HT; intros Tf HU.
  - exists Tf. split.
    + assumption.
    + constructor.
  - destruct (confluence_single_ty T1 T2 Tf (conj H HU)) as [V' [HV'1 HV'2] ].
    apply IHHT in HV'1 as [V0 [HV'11 HV'12 ] ].
    exists V0. split.
    + assumption.
    + econstructor; eassumption.
Qed.

Lemma confluence_multi_ty :
  forall T1 T2 T3,
    multi ty_eval_step T1 T2 /\ multi ty_eval_step T1 T3 ->
    exists T4, multi ty_eval_step T2 T4 /\ multi ty_eval_step T3 T4.
Proof.
  intros. destruct H as [HT HU].
  generalize dependent T3. induction HT; intros Tf HU.
  - exists Tf. split. + assumption. + constructor.
  - destruct (confluence_multi_single_ty T1 Tf T2 (conj HU H)) as [V' [HV'1 HV'2] ].
    apply IHHT in HV'2 as [V0 [HV'21 HV'22] ].
    exists V0. split.
    + assumption.
    + econstructor; eassumption.
Qed.

Lemma tyeq_implies_confluence :
  forall T1 T2,
    (T1 ===ty T2) ->
    exists T3, multi ty_eval_step T1 T3 /\ multi ty_eval_step T2 T3.
Proof.
  intros. induction H.
  - exists T. split; constructor.
  - destruct IHmulti as [U' [IH2 IH3] ].
    destruct H.
    + exists U'. split.
      * econstructor; eassumption.
      * assumption.
    + assert (exists V, (U' ==>ty V) /\ multi ty_eval_step T1 V).
      * apply confluence_multi_single_ty with T2. split; assumption.
      * destruct H1 as [V [HU HT3] ]. exists V. split; try assumption.
        eapply tyeval_append. split; eassumption.
Qed.

(* normal form lemma for TyPi inversion *)
Lemma tyeval_preserves_form_pi :
  forall T1 S1 T,
  multi ty_eval_step <{{\:T1,S1}}> T ->
  exists T2 S2,
  T = <{{\:T2,S2}}> /\ multi ty_eval_step T1 T2 /\ multi ty_eval_step S1 S2.
Proof.
  intros. remember <{{\:T1,S1}}> as T0.
  generalize dependent HeqT0. generalize dependent S1. generalize dependent T1.
  induction H; intros.
  - exists T1, S1; repeat split; try assumption; apply multi_refl.
  - rewrite HeqT0 in H. inversion H; subst.
    edestruct IHmulti as [Ta [Sa [HT3 [HTa HSa] ] ] ].
    + reflexivity.
    + exists Ta, Sa. repeat split; try assumption.
      * eapply multi_step; eassumption.
      * eapply multi_step; eassumption.
Qed.

Lemma invert_tyeq_pi :
  forall T1 S1 T2 S2,
  <{{\:T1,S1}}> ===ty <{{\:T2,S2}}> ->
  (T1 ===ty T2) /\ (S1 ===ty S2).
Proof.
  intros. apply tyeq_implies_confluence in H as [U [H1 H2] ].
  apply tyeval_preserves_form_pi in H1 as [UT [US [HU [H11 H12] ] ] ].
  apply tyeval_preserves_form_pi in H2 as [VT [VS [HV [H21 H22] ] ] ].
  subst U. inversion HV. subst VT VS. clear HV. split;
  eapply tyeq_trans; split; [ | apply tyeq_sym | | apply tyeq_sym ];
  apply multi_step_implies_tyeq; eassumption.
Qed.

(* replacing one context entry with a convertible type *)
Lemma context_conv_cons_kinding : forall Delta Gamma T T0 T0' K,
  wf_Delta Delta ->
  <[[ Delta | Gamma |-- T0 \in * ]]> ->
  T0 ===ty T0' ->
  <[[ Delta | (ren_Ty Datatypes.S T0) :: map (ren_Ty Datatypes.S) Gamma |-- T \in K ]]> ->
  <[[ Delta | (ren_Ty Datatypes.S T0') :: map (ren_Ty Datatypes.S) Gamma |-- T \in K ]]>.
Proof.
  intros Delta Gamma T T0 T0' K HWD HT0 Heq HT.
  assert (Hgoal : <[[ Delta | (ren_Ty Datatypes.S T0') :: map (ren_Ty Datatypes.S) Gamma |-- {subst_Ty (fun n => TmVar n) T}
                      \in {subst_Ki (fun n => TmVar n) K} ]]>).
  { eapply subst_kinding.
    - eassumption.
    - assumption.
    - intros x S0 Hx. rewrite instId'_Ty.
      destruct x as [|x']; simpl in Hx.
      + inversion Hx; subst.
        eapply T_Conv.
        * apply T_Var. reflexivity.
        * apply ren_tyeq. apply tyeq_sym. assumption.
        * eapply ren_kinding with (K := KiStar).
          -- eassumption.
          -- assumption.
          -- intros y S1 Hy. simpl. rewrite nth_error_map. rewrite Hy. reflexivity.
      + rewrite nth_error_map in Hx.
        destruct (nth_error Gamma x') as [S1|] eqn:EqG; try discriminate.
        simpl in Hx. inversion Hx; subst.
        apply T_Var. simpl. rewrite nth_error_map. rewrite EqG. reflexivity. }
  rewrite instId'_Ty in Hgoal. rewrite instId'_Ki in Hgoal. assumption.
Qed.

Lemma context_conv_cons_has_type : forall Delta Gamma t T T0 T0',
  wf_Delta Delta ->
  <[[ Delta | Gamma |-- T0 \in * ]]> ->
  T0 ===ty T0' ->
  <[ Delta | (ren_Ty Datatypes.S T0) :: map (ren_Ty Datatypes.S) Gamma |-- t \in T ]> ->
  <[ Delta | (ren_Ty Datatypes.S T0') :: map (ren_Ty Datatypes.S) Gamma |-- t \in T ]>.
Proof.
  intros Delta Gamma t T T0 T0' HWD HT0 Heq Ht.
  assert (Hgoal : <[ Delta | (ren_Ty Datatypes.S T0') :: map (ren_Ty Datatypes.S) Gamma |-- {subst_Tm (fun n => TmVar n) t}
                      \in {subst_Ty (fun n => TmVar n) T} ]>).
  { eapply subst_has_type.
    - eassumption.
    - assumption.
    - intros x S0 Hx. rewrite instId'_Ty.
      destruct x as [|x']; simpl in Hx.
      + inversion Hx; subst.
        eapply T_Conv.
        * apply T_Var. reflexivity.
        * apply ren_tyeq. apply tyeq_sym. assumption.
        * eapply ren_kinding with (K := KiStar).
          -- eassumption.
          -- assumption.
          -- intros y S1 Hy. simpl. rewrite nth_error_map. rewrite Hy. reflexivity.
      + rewrite nth_error_map in Hx.
        destruct (nth_error Gamma x') as [S1|] eqn:EqG; try discriminate.
        simpl in Hx. inversion Hx; subst.
        apply T_Var. simpl. rewrite nth_error_map. rewrite EqG. reflexivity. }
  rewrite instId'_Tm in Hgoal. rewrite instId'_Ty in Hgoal. assumption.
Qed.

Lemma invert_typing_abs :
  forall Delta Gamma S1 t1 T,
  wf_Delta Delta ->
  <[ Delta | Gamma |-- \:S1, t1 \in T ]> ->
  forall T2 S2,
  T ===ty <{{\:T2,S2}}> ->
  <[[ Delta | Gamma |-- \:T2,S2 \in * ]]> ->
  (S1 ===ty T2) /\ <[[ Delta | Gamma |-- S1 \in * ]]> /\
  <[ Delta | (ren_Ty Datatypes.S S1) :: map (ren_Ty Datatypes.S) Gamma |-- t1 \in S2 ]>.
Proof.
  intros Delta Gamma S1 t1 T HWD H.
  remember <{\:S1,t1}> as t.
  generalize dependent Heqt.
  induction H; try discriminate; intros Heqt T2 S2 Heq Hall.
  - inversion Heqt; subst.
    apply invert_tyeq_pi in Heq as [HL HR].
    apply kinding_pi_form in Hall as [HallT HallS].
    repeat split.
    + assumption.
    + assumption.
    + eapply T_Conv.
      * exact H1.
      * assumption.
      * eapply context_conv_cons_kinding.
        -- assumption.
        -- eassumption.
        -- apply tyeq_sym. assumption.
        -- eassumption.
  - apply IHhas_type with (T2:=T2) (S2:=S2).
    + assumption.
    + assumption.
    + eapply tyeq_trans; split; eassumption.
    + assumption.
Qed.

Lemma step_implies_tmeval : forall t t', t --> t' -> t ==>tm t'.
Proof.
  intros t t' H. induction H.
  - eapply TMST_Red; try apply tmeval_refl. reflexivity.
  - constructor; [assumption | apply tmeval_refl].
  - constructor; [apply tmeval_refl | assumption].
Qed.

(* preservation *)
Theorem preservation :
  forall Delta Gamma t T,
  <[ Delta | Gamma |-- t \in T ]> ->
  wf_Delta Delta ->
  wf Delta Gamma ->
  forall t',
  t --> t' ->
  <[ Delta | Gamma |-- t' \in T ]>.
Proof.
  intros Delta Gamma t T H HWD HW. induction H; intros t' Hstep.
  - inversion Hstep.
  - inversion Hstep.
  - inversion Hstep; subst.
    + pose proof (regularity _ _ _ _ H HWD HW) as Hall.
      apply invert_typing_abs with (T2:=T) (S2:=S) in H as [HeqT0T [HT0k Ht] ].
      * rewrite pop_subst_tm_tm_betared. rewrite pop_subst_ty_tm_betared.
        apply pop_subst_has_type with (T':=T0).
        -- assumption.
        -- exact Ht.
        -- eapply T_Conv.
           ++ exact H0.
           ++ apply tyeq_sym. exact HeqT0T.
           ++ exact HT0k.
      * assumption.
      * apply multi_refl.
      * assumption.
    + apply T_App with (T:=T) (S:=S).
      * apply IHhas_type1; assumption.
      * assumption.
      * reflexivity.
    + eapply T_Conv.
      * apply T_App with (T:=T) (S:=S).
        -- assumption.
        -- apply IHhas_type2; assumption.
        -- reflexivity.
      * apply tyeq_sym. eapply multi_step.
        -- left. apply tytmbetared_tyeval_lemma.
           ++ apply tyeval_refl.
           ++ apply step_implies_tmeval. exact H6.
        -- apply multi_refl.
      * rewrite pop_subst_ty_tm_betared.
        change <{|*|}> with (subst_Ki (fun n => match n with
                                0 => t2 | Datatypes.S n' => TmVar n' end) KiStar).
        apply pop_subst_kinding with (T':=T).
        -- assumption.
        -- pose proof (regularity _ _ _ _ H HWD HW) as HallK.
           apply kinding_pi_form in HallK as [HKT HKS]. exact HKS.
        -- assumption.
  - eapply T_Conv.
    + apply IHhas_type; assumption.
    + assumption.
    + assumption.
  - inversion Hstep.
Qed.

(* canonical forms (standard-form lemmas progress needs) *)
Lemma tyeval_preserves_form_unit :
  forall T,
  multi ty_eval_step <{{Unit}}> T ->
  T = <{{Unit}}>.
Proof.
  intros. remember <{{Unit}}> as T0.
  induction H; subst.
  - reflexivity.
  - inversion H; subst. apply IHmulti. reflexivity.
Qed.

Lemma tyeq_pi_unit_absurd :
  forall T S,
  <{{\:T,S}}> ===ty <{{Unit}}> ->
  False.
Proof.
  intros. apply tyeq_implies_confluence in H as [U [H1 H2] ].
  apply tyeval_preserves_form_pi in H1 as [T2 [S2 [HU [_ _] ] ] ].
  apply tyeval_preserves_form_unit in H2.
  rewrite H2 in HU. discriminate HU.
Qed.

Lemma typing_abs_form :
  forall Delta Gamma S1 t1 T,
  <[ Delta | Gamma |-- \:S1, t1 \in T ]> ->
  exists S2, T ===ty <{{\:S1,S2}}>.
Proof.
  intros Delta Gamma S1 t1 T H.
  remember <{\:S1,t1}> as t.
  generalize dependent Heqt.
  induction H; try discriminate; intros.
  - inversion Heqt. subst. exists S. apply multi_refl.
  - apply IHhas_type in Heqt as [S3 HT].
    exists S3. eapply tyeq_trans. split.
    + apply tyeq_sym. eassumption.
    + assumption.
Qed.

Lemma typing_unit_form :
  forall Delta Gamma T,
  <[ Delta | Gamma |-- unit \in T ]> ->
  T ===ty <{{Unit}}>.
Proof.
  intros Delta Gamma T H.
  remember <{unit}> as t.
  generalize dependent Heqt.
  induction H; try discriminate; intros.
  - eapply tyeq_trans. split.
    + apply tyeq_sym. eassumption.
    + apply IHhas_type. assumption.
  - apply multi_refl.
Qed.

(* progress *)
Theorem progress :
  forall Delta t T,
  <[ Delta | nil |-- t \in T ]> ->
  value t \/ exists t', t --> t'.
Proof.
  intros Delta t T H.
  remember (@nil Ty) as Gamma.
  generalize dependent HeqGamma.
  induction H; intros.
  - subst Gamma. destruct x; discriminate H.
  - left. apply v_abs.
  - right. destruct (IHhas_type1 HeqGamma) as [Hv1 | [t1' Hs1] ].
    + destruct (IHhas_type2 HeqGamma) as [Hv2 | [t2' Hs2] ].
      * destruct Hv1.
        -- eexists. apply ST_AppAbs. assumption.
        -- apply typing_unit_form in H.
           apply tyeq_pi_unit_absurd in H. destruct H.
      * eexists. apply ST_App2; eassumption.
    + eexists. apply ST_App1. eassumption.
  - apply IHhas_type. assumption.
  - left. apply v_unit.
Qed.
