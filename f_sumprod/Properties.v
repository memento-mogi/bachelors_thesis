From Stdlib Require Import List.
From FSumProd Require Export Definitions.

(* Forall2 helpers *)
Lemma Forall2_map_l : forall (A B : Type) (R R' : A -> B -> Prop) f xs ys,
  Forall2 R xs ys ->
  (forall x y, R x y -> R' (f x) y) ->
  Forall2 R' (map f xs) ys.
Proof.
  intros A B R R' f xs ys H Hf.
  induction H; simpl.
  - constructor.
  - constructor; auto.
Qed.

Lemma Forall2_map_lr : forall (A B : Type) (R R' : A -> B -> Prop) f g xs ys,
  Forall2 R xs ys ->
  (forall x y, R x y -> R' (f x) (g y)) ->
  Forall2 R' (map f xs) (map g ys).
Proof.
  intros A B R R' f g xs ys H Hfg.
  induction H; simpl.
  - constructor.
  - constructor; auto.
Qed.

Lemma Forall2_nth_error_l : forall (A B : Type) (R : A -> B -> Prop) xs ys i x,
  Forall2 R xs ys ->
  nth_error xs i = Some x ->
  exists y, nth_error ys i = Some y /\ R x y.
Proof.
  intros A B R xs ys i x H.
  revert i.
  induction H; intros i Hi.
  - destruct i; discriminate.
  - destruct i; simpl in *.
    + inversion Hi; subst. exists y. split; auto.
    + apply IHForall2. assumption.
Qed.

Lemma Forall2_nth_error_r : forall (A B : Type) (R : A -> B -> Prop) xs ys i y,
  Forall2 R xs ys ->
  nth_error ys i = Some y ->
  exists x, nth_error xs i = Some x /\ R x y.
Proof.
  intros A B R xs ys i y H.
  revert i.
  induction H; intros i Hi.
  - destruct i; discriminate.
  - destruct i; simpl in *.
    + inversion Hi; subst. exists x. split; auto.
    + apply IHForall2. assumption.
Qed.

Lemma Forall2_replace : forall (A B : Type) (R R' : A -> B -> Prop) vs t t' ts Ts,
  Forall2 R (vs ++ t :: ts) Ts ->
  (forall x y, R x y -> R' x y) ->
  (forall y, R t y -> R' t' y) ->
  Forall2 R' (vs ++ t' :: ts) Ts.
Proof.
  intros A B R R' vs t t' ts Ts H HR Ht.
  apply Forall2_app_inv_l in H.
  destruct H as [Ts1 [Ts2 [H1 [H2 HTs]]]].
  subst Ts. inversion H2; subst.
  apply Forall2_app.
  - eapply Forall2_impl; eassumption.
  - constructor; auto.
    eapply Forall2_impl; eassumption.
Qed.

Lemma Forall2_Forall_l : forall (A B : Type) (R : A -> B -> Prop) (P : A -> Prop) xs ys,
  Forall2 R xs ys ->
  (forall x y, R x y -> P x) ->
  Forall P xs.
Proof.
  intros A B R P xs ys H HP.
  induction H.
  - constructor.
  - constructor.
    + apply HP with (y := y). assumption.
    + assumption.
Qed.

(* renaming/substitution *)
Lemma ren_ty_beta_red : forall T1 S xi,
  ren_ty xi (ty_beta_red T1 S) =
  ty_beta_red (ren_ty (upRen_ty_ty xi) T1) (ren_ty xi S).
Proof.
  intros T1 S xi. unfold ty_beta_red.
  rewrite substRen_ty, renSubst_ty.
  apply ext_ty. intros x. destruct x; simpl; reflexivity.
Qed.

Lemma subst_ty_beta_red : forall T1 S sigma,
  subst_ty sigma (ty_beta_red T1 S) =
  ty_beta_red (subst_ty (up_ty_ty sigma) T1) (subst_ty sigma S).
Proof.
  intros T1 S sigma. unfold ty_beta_red.
  rewrite substSubst_ty, substSubst_ty.
  apply ext_ty. intros x. destruct x; asolve.
Qed.

(* renaming / substitution preserve typing *)
Lemma renTm_typing : forall Gamma t T,
  <[ Gamma |-- t \in T ]> ->
  forall Gamma' xi,
  (forall x S, nth_error Gamma x = Some S ->
                nth_error Gamma' (xi x) = Some S) ->
  <[ Gamma' |-- {ren_tm id xi t} \in T ]>.
Proof.
  intros Gamma t T H.
  induction H using has_type_ind2; intros Gamma' xi Hxi; asolve.
  - apply T_Var. apply Hxi. assumption.
  - apply T_Abs. apply IHhas_type.
    intros x S Hx. destruct x.
    + simpl in Hx. inversion Hx. reflexivity.
    + simpl in Hx. apply Hxi. assumption.
  - eapply T_App.
    + apply IHhas_type1. assumption.
    + apply IHhas_type2. assumption.
  - apply T_TAbs.
    rewrite extRen_tm with (zeta_ty := id) (zeta_tm := xi); dauto.
    apply IHhas_type. intros x S Hx.
    rewrite nth_error_map in *.
    destruct (nth_error Gamma x) as [S'|] eqn:EqGx; try discriminate.
    simpl in Hx. inversion Hx; subst.
    rewrite Hxi with (S := S'); auto.
  - subst T1'. eapply T_TApp.
    + apply IHhas_type. assumption.
    + reflexivity.
  - apply T_Tuple.
    eapply Forall2_map_l; try eassumption.
    intros t T [_ IH]. apply IH. assumption.
  - eapply T_Proj.
    + apply IHhas_type. assumption.
    + assumption.
  - eapply T_Inj.
    + apply IHhas_type. assumption.
    + assumption.
  - eapply T_Case.
    + apply IHhas_type. assumption.
    + eapply Forall2_map_l; try eassumption.
      intros t Ti [_ IH]. apply IH. assumption.
  - apply T_Unit.
Qed.

Lemma renTy_typing : forall Gamma t T,
  <[ Gamma |-- t \in T ]> ->
  forall Gamma' xi,
  (forall x S, nth_error Gamma x = Some S ->
                nth_error Gamma' x = Some (ren_ty xi S)) ->
  <[ Gamma' |-- {ren_tm xi id t} \in {ren_ty xi T} ]>.
Proof.
  intros Gamma t T H.
  induction H using has_type_ind2; intros Gamma' xi HG; asolve.
  - apply T_Var. apply HG. assumption.
  - apply T_Abs.
    rewrite extRen_tm with (zeta_ty := xi) (zeta_tm := id); dauto.
    apply IHhas_type. intros x S Hx.
    destruct x; simpl in *; auto.
    inversion Hx; subst. reflexivity.
  - eapply T_App.
    + apply IHhas_type1. assumption.
    + apply IHhas_type2. assumption.
  - apply T_TAbs.
    apply IHhas_type. intros x S Hx.
    rewrite nth_error_map in *.
    destruct (nth_error Gamma x) as [S'|] eqn:EqGx; try discriminate.
    simpl in Hx. inversion Hx; subst.
    rewrite HG with (S := S'); try assumption.
    asolve.
  - subst T1'. eapply T_TApp.
    + apply IHhas_type; assumption.
    + apply ren_ty_beta_red.
  - apply T_Tuple.
    eapply Forall2_map_lr; try eassumption.
    intros t T [_ IH]. apply IH. assumption.
  - eapply T_Proj.
    + apply IHhas_type; assumption.
    + rewrite nth_error_map. rewrite H0. reflexivity.
  - eapply T_Inj.
    + apply IHhas_type; assumption.
    + rewrite nth_error_map. rewrite H0. reflexivity.
  - eapply T_Case.
    + apply IHhas_type; assumption.
    + eapply Forall2_map_lr; try eassumption.
      intros t Ti [_ IH]. apply IH. assumption.
  - apply T_Unit.
Qed.

(* substitution lemma *)
Lemma tmsubst_preserves_typing :
  forall Gamma t T,
  <[ Gamma |-- t \in T ]> ->
  forall Gamma' sigma,
  (forall x S, nth_error Gamma x = Some S ->
                <[ Gamma' |-- {sigma x} \in S ]>) ->
  <[ Gamma' |-- {subst_tm var_ty sigma t} \in T ]>.
Proof.
  intros Gamma t T H.
  induction H using has_type_ind2; intros Gamma' sigma Hsig.
  - asolve.
  - asolve. apply T_Abs. apply IHhas_type. intros x S Hx.
    destruct x; simpl in *.
    + inversion Hx; subst. apply T_Var. reflexivity.
    + apply renTm_typing with (Gamma := Gamma').
      * apply Hsig. assumption.
      * intros. simpl. assumption.
  - asolve. eapply T_App.
    + apply IHhas_type1. assumption.
    + apply IHhas_type2. assumption.
  - asolve. apply T_TAbs.
    rewrite ext_tm with (tau_ty := id) (tau_tm := (fun x : nat => ren_tm S id (sigma x)));
    dauto.
    eapply IHhas_type. intros x S Hx.
    rewrite nth_error_map in Hx.
    destruct (nth_error Gamma x) as [S'|] eqn:EqGx; try discriminate.
    simpl in Hx. inversion Hx. eapply renTy_typing.
    + apply Hsig. assumption.
    + intros y S1 Hy. rewrite nth_error_map. rewrite Hy. reflexivity.
  - asolve. subst T1'. eapply T_TApp.
    + apply IHhas_type. assumption.
    + reflexivity.
  - asolve. apply T_Tuple.
    eapply Forall2_map_l; try eassumption.
    intros t T [_ IH]. apply IH. assumption.
  - asolve. eapply T_Proj.
    + apply IHhas_type. assumption.
    + assumption.
  - asolve. eapply T_Inj.
    + apply IHhas_type. assumption.
    + assumption.
  - asolve. eapply T_Case.
    + apply IHhas_type. assumption.
    + eapply Forall2_map_l; try eassumption.
      intros t Ti [_ IH]. apply IH. assumption.
  - apply T_Unit.
Qed.

Lemma tysubst_preserves_typing :
  forall Gamma t T,
  <[ Gamma |-- t \in T ]> ->
  forall Gamma' sigma,
  (forall x S, nth_error Gamma x = Some S ->
                nth_error Gamma' x = Some (subst_ty sigma S)) ->
  <[ Gamma' |-- {subst_tm sigma var_tm t} \in {subst_ty sigma T} ]>.
Proof.
  intros Gamma t T H.
  induction H using has_type_ind2; intros Gamma' sigma HG.
  - asolve. apply T_Var. apply HG. assumption.
  - asolve. apply T_Abs.
    rewrite ext_tm with (tau_ty := sigma) (tau_tm := var_tm).
    + apply IHhas_type. intros x S Hx.
      destruct x; simpl in Hx; inversion Hx.
      * reflexivity.
      * simpl. apply HG. assumption.
    + intros x. apply rinstId'_ty.
    + dauto.
  - asolve. eapply T_App.
    + apply IHhas_type1. assumption.
    + apply IHhas_type2. assumption.
  - asolve. apply T_TAbs.
    rewrite ext_tm with (tau_ty := up_ty_ty sigma) (tau_tm := var_tm);
    dauto.
    apply IHhas_type. intros x S Hx.
    rewrite nth_error_map in Hx.
    destruct (nth_error Gamma x) as [S'|] eqn:EqGx; try discriminate.
    simpl in Hx. inversion Hx; subst.
    rewrite nth_error_map. rewrite HG with (S := S'); try assumption.
    simpl. f_equal. asolve.
  - asolve. subst T1'. eapply T_TApp.
    + apply IHhas_type; assumption.
    + apply subst_ty_beta_red.
  - asolve. apply T_Tuple.
    eapply Forall2_map_lr; try eassumption.
    intros t T [_ IH]. apply IH. assumption.
  - asolve. eapply T_Proj.
    + apply IHhas_type. assumption.
    + rewrite nth_error_map. rewrite H0. reflexivity.
  - asolve. eapply T_Inj.
    + apply IHhas_type; assumption.
    + rewrite nth_error_map. rewrite H0. reflexivity.
  - asolve. eapply T_Case.
    + apply IHhas_type; assumption.
    + eapply Forall2_map_lr; try eassumption.
      intros t Ti [_ IH]. apply IH. assumption.
  - apply T_Unit.
Qed.

(* preservation *)
Theorem preservation :
  forall Gamma t T,
  <[ Gamma |-- t \in T ]> ->
  forall t',
  t --> t' ->
  <[ Gamma |-- t' \in T ]>.
Proof.
  intros Gamma t T H.
  induction H using has_type_ind2; intros t' Hstep.
  - inversion Hstep.
  - inversion Hstep.
  - inversion Hstep; subst.
    + unfold tm_tm_betared.
      inversion H; subst.
      apply tmsubst_preserves_typing with (Gamma := T1 :: Gamma).
      * assumption.
      * intros x S Hx. destruct x; simpl in *.
        { inversion Hx; subst. assumption. }
        { apply T_Var. assumption. }
    + eapply T_App.
      * apply IHhas_type1. assumption.
      * assumption.
    + eapply T_App.
      * eassumption.
      * apply IHhas_type2. assumption.
  - inversion Hstep.
  - inversion Hstep; subst.
    + unfold tm_ty_betared.
      inversion H; subst.
      eapply tysubst_preserves_typing.
      * eassumption.
      * intros x S1 Hx. rewrite nth_error_map in Hx.
        destruct (nth_error Gamma x) as [S'|] eqn:EqGx; try discriminate.
        simpl in Hx. inversion Hx; subst.
        asolve.
    + eapply T_TApp.
      * apply IHhas_type. assumption.
      * reflexivity.
  - inversion Hstep; subst.
    apply T_Tuple.
    eapply Forall2_replace.
    + eassumption.
    + simpl. intros t0 T0 [Ht _]. assumption.
    + simpl. intros T0 [_ IH]. apply IH. assumption.
  - inversion Hstep; subst.
    + inversion H. subst.
      destruct (Forall2_nth_error_l _ _ _ _ _ _ _ H4 H5) as [Ti' [HTi' Ht]].
      rewrite H0 in HTi'. inversion HTi'. subst.
      assumption.
    + eapply T_Proj.
      * apply IHhas_type. assumption.
      * assumption.
  - inversion Hstep; subst.
    eapply T_Inj.
    + apply IHhas_type. assumption.
    + assumption.
  - inversion Hstep; subst.
    + inversion H; subst.
      destruct (Forall2_nth_error_l _ _ _ _ _ _ _ H0 H5) as [Ti' [HTi' [Ht _]]].
      rewrite H7 in HTi'. inversion HTi'; subst.
      eapply T_App.
      * eassumption.
      * assumption.
    + eapply T_Case.
      * apply IHhas_type. assumption.
      * eapply Forall2_impl; try eassumption.
        intros t Ti [Ht _]. assumption.
  - inversion Hstep.
Qed.

(* canonical forms *)
Lemma canonical_forms_arr :
  forall t T1 T2,
  <[ nil |-- t \in T1 -> T2 ]> ->
  value t ->
  exists t1, t = <{ \:T1, t1 }>.
Proof.
  intros t T1 T2 Hty Hval.
  destruct Hval; inversion Hty; subst.
  exists t. reflexivity.
Qed.

Lemma canonical_forms_forall :
  forall t T1,
  <[ nil |-- t \in -/, T1 ]> ->
  value t ->
  exists t1, t = <{ \\, t1 }>.
Proof.
  intros t T1 Hty Hval.
  destruct Hval; inversion Hty; subst.
  exists t. reflexivity.
Qed.

Lemma canonical_forms_prod :
  forall t Ts,
  <[ nil |-- t \in Prod Ts ]> ->
  value t ->
  exists ts, t = <{ tuple ts }>.
Proof.
  intros t Ts Hty Hval.
  destruct Hval; inversion Hty; subst.
  exists ts. reflexivity.
Qed.

Lemma canonical_forms_sum :
  forall t Ts,
  <[ nil |-- t \in Sum Ts ]> ->
  value t ->
  exists i v, t = <{ inj i v }>.
Proof.
  intros t Ts Hty Hval.
  destruct Hval; inversion Hty; subst.
  exists i, v. reflexivity.
Qed.

Lemma list_progress :
  forall ts,
  Forall (fun t => value t \/ exists t', t --> t') ts ->
  Forall value ts \/
  exists vs t t' ts', ts = vs ++ t :: ts' /\ Forall value vs /\ t --> t'.
Proof.
  intros ts H.
  induction H.
  - left. constructor.
  - destruct H as [Hv | [x' Hs]].
    + destruct IHForall as [Hvs | [vs [t [t' [ts' [Heq [Hvs Hs]]]]]]].
      * left. constructor; assumption.
      * right. subst l. exists (x :: vs), t, t', ts'.
        repeat split; auto.
    + right. exists nil, x, x', l.
      repeat split; auto.
Qed.

(* progress *)
Theorem progress :
  forall t T,
  <[ nil |-- t \in T ]> ->
  value t \/ exists t', t --> t'.
Proof.
  intros t T H.
  remember (@nil ty) as Gamma eqn:HGamma.
  induction H using has_type_ind2; subst Gamma.
  - destruct x; discriminate H.
  - left. apply V_Abs.
  - right.
    destruct (IHhas_type1 eq_refl) as [Hv1 | [t1' Hs1]].
    + destruct (IHhas_type2 eq_refl) as [Hv2 | [t2' Hs2]].
      * apply canonical_forms_arr in H; try assumption.
        destruct H as [t1' H]. subst t1.
        eexists. apply ST_AppAbs; assumption.
      * eexists. apply ST_App2; eassumption.
    + eexists. apply ST_App1; eapply Hs1.
  - left. apply V_TAbs.
  - right.
    destruct (IHhas_type eq_refl) as [Hv | [t1' Hs]].
    + apply canonical_forms_forall in H; try assumption.
      destruct H as [t1' H]. subst t1.
      eexists. apply ST_TAppAbs.
    + eexists. apply ST_TApp. eassumption.
  - destruct (list_progress ts) as [Hvs | [vs [t [t' [ts' [Heq [Hvs Hs]]]]]]].
    + eapply Forall2_Forall_l; try eassumption.
      intros t T [_ IH]. apply IH. reflexivity.
    + left. apply V_Tuple. assumption.
    + right. subst ts.
      eexists. apply ST_Tuple; eassumption.
  - right.
    destruct (IHhas_type eq_refl) as [Hv | [t1' Hs]].
    + remember H as Hty. clear HeqHty.
      apply canonical_forms_prod in H; try assumption.
      destruct H as [ts H]. subst t1. inversion Hty. inversion Hv.
      subst. destruct (Forall2_nth_error_r _ _ _ _ _ _ _ H2 H0) as [v [Hnth _]].
      eexists. eapply ST_ProjTuple; eassumption.
    + eexists. apply ST_Proj. eassumption.
  - destruct (IHhas_type eq_refl) as [Hv | [t1' Hs]].
    + left. apply V_Inj. assumption.
    + right. eexists. apply ST_Inj. eassumption.
  - right.
    destruct (IHhas_type eq_refl) as [Hv | [t1' Hs]].
    + remember H as Hty. clear HeqHty.
      apply canonical_forms_sum in H; try assumption.
      destruct H as [i [v H]]. subst t1.
      inversion Hty. inversion Hv. subst.
      destruct (Forall2_nth_error_r _ _ _ _ _ _ _ H0 H4) as [t [Hnth _]].
      eexists. eapply ST_CaseInj; eassumption.
    + eexists. apply ST_Case. eassumption.
  - left. apply V_Unit.
Qed.
