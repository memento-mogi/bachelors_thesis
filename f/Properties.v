From Stdlib Require Import List.
From F Require Export Definitions.

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
  has_type Gamma t T ->
  forall Gamma' xi,
  (forall x S, nth_error Gamma x = Some S ->
                nth_error Gamma' (xi x) = Some S) ->
  has_type Gamma' (ren_tm id xi t) T.
Proof.
  intros Gamma t T H.
  induction H; intros Gamma' xi Hxi; asolve.
  - apply T_Var. apply Hxi. assumption.
  - apply T_Abs. apply IHhas_type.
    intros x S Hx. destruct x. 
    + simpl in Hx. inversion Hx. reflexivity.
    + simpl in Hx. apply Hxi. assumption.
  - eapply T_App; eauto.
  - apply T_TAbs.
    rewrite extRen_tm with (zeta_ty := id) (zeta_tm := xi); dauto.
    apply IHhas_type. intros x S Hx.
    rewrite nth_error_map in *.
    destruct (nth_error Gamma x) as [S'|] eqn:EqGx; try discriminate.
    simpl in Hx. inversion Hx; subst.
    rewrite Hxi with (S := S'); auto.
  - subst T1'. eapply T_TApp; eauto.
  - apply T_Unit.
Qed.

Lemma renTy_typing : forall Gamma t T,
  has_type Gamma t T ->
  forall Gamma' xi,
  (forall x S, nth_error Gamma x = Some S ->
                nth_error Gamma' x = Some (ren_ty xi S)) ->
  has_type Gamma' (ren_tm xi id t) (ren_ty xi T).
Proof.
  intros Gamma t T H.
  induction H; intros Gamma' xi HG; asolve.
  - apply T_Var. apply HG. assumption.
  - apply T_Abs.
    rewrite extRen_tm with (zeta_ty := xi) (zeta_tm := id); dauto.
    apply IHhas_type. intros x S Hx.
    destruct x; simpl in *; auto.
    inversion Hx; subst. reflexivity.
  - eapply T_App; eauto.
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
  - apply T_Unit.
Qed.

(* substitution lemma *)
Lemma tmsubst_preserves_typing :
  forall Gamma t T,
  has_type Gamma t T ->
  forall Gamma' sigma,
  (forall x S, nth_error Gamma x = Some S ->
                has_type Gamma' (sigma x) S) ->
  has_type Gamma' (subst_tm var_ty sigma t) T.
Proof.
  intros Gamma t T H.
  induction H; intros Gamma' sigma Hsig; asolve.
  - apply T_Abs. apply IHhas_type. intros x S Hx.
    destruct x; simpl in *.
    + inversion Hx; subst. apply T_Var. reflexivity.
    + apply renTm_typing with (Gamma := Gamma').
      * apply Hsig. assumption.
      * intros y S1 Hy. simpl. assumption.
  - eapply T_App; eauto.
  - apply T_TAbs.
    erewrite ext_tm with (tau_ty := var_ty) (tau_tm := up_ty_tm sigma); dauto.
    apply IHhas_type. intros x S Hx.
    rewrite nth_error_map in Hx.
    destruct (nth_error Gamma x) as [S'|] eqn:EqGx; try discriminate.
    simpl in Hx. inversion Hx; subst S.
    asolve. eapply renTy_typing.
    + apply Hsig. eassumption.
    + intros y S1 Hy. rewrite nth_error_map. rewrite Hy. reflexivity.
  - subst T1'. eapply T_TApp; eauto.
  - apply T_Unit.
Qed.

Lemma tysubst_preserves_typing :
  forall Gamma t T,
  has_type Gamma t T ->
  forall Gamma' sigma,
  (forall x S, nth_error Gamma x = Some S ->
                nth_error Gamma' x = Some (subst_ty sigma S)) ->
  has_type Gamma' (subst_tm sigma var_tm t) (subst_ty sigma T).
Proof.
  intros Gamma t T H.
  induction H; intros Gamma' sigma HG; asolve.
  - apply T_Var. apply HG. assumption.
  - apply T_Abs.
    erewrite ext_tm with (tau_ty := sigma) (tau_tm := var_tm);
      [ | (intros x; apply rinstId'_ty) | dauto ].
    apply IHhas_type. intros x S Hx.
    destruct x; simpl in Hx; inversion Hx.
    + reflexivity.
    + simpl. apply HG. assumption.
  - eapply T_App; eauto.
  - apply T_TAbs.
    erewrite ext_tm with (tau_ty := up_ty_ty sigma) (tau_tm := var_tm);
    dauto.
    apply IHhas_type. intros x S Hx.
    rewrite nth_error_map in Hx.
    destruct (nth_error Gamma x) as [S'|] eqn:EqGx; try discriminate.
    simpl in Hx. inversion Hx; subst.
    rewrite nth_error_map. rewrite HG with (S := S'); try assumption.
    asolve.
  - subst T1'. eapply T_TApp.
    + apply IHhas_type; assumption.
    + apply subst_ty_beta_red.
  - apply T_Unit.
Qed.

(* preservation *)
Theorem preservation :
  forall Gamma t T,
  has_type Gamma t T ->
  forall t',
  t --> t' ->
  has_type Gamma t' T.
Proof.
  intros Gamma t T H.
  induction H; intros t' Hstep; try (inversion Hstep; fail).
  - inversion Hstep; subst.
    + unfold tm_tm_betared.
      inversion H; subst.
      apply tmsubst_preserves_typing with (Gamma := T1 :: Gamma).
      * assumption.
      * intros x S Hx. destruct x; simpl in *.
        { inversion Hx; subst. assumption. }
        { apply T_Var. assumption. }
    + eapply T_App; eauto.
    + eapply T_App; eauto.
  - inversion Hstep; subst.
    + unfold tm_ty_betared.
      inversion H; subst.
      apply tysubst_preserves_typing with (Gamma := map (ren_ty Datatypes.S) Gamma).
      * assumption.
      * intros x S1 Hx. rewrite nth_error_map in Hx.
        destruct (nth_error Gamma x) as [S'|] eqn:EqGx; try discriminate.
        simpl in Hx. inversion Hx; subst.
        asimpl. reflexivity.
    + eapply T_TApp; eauto.
Qed.

(* canonical forms *)
Lemma canonical_forms_arr :
  forall t T1 T2,
  has_type nil t (TyArrow T1 T2) ->
  value t ->
  exists t1, t = TmAbs T1 t1.
Proof.
  intros t T1 T2 Hty Hval.
  destruct Hval as [T t1 | t1 | ]; inversion Hty; subst.
  exists t1. reflexivity.
Qed.

Lemma canonical_forms_forall :
  forall t T1,
  has_type nil t (TyForall T1) ->
  value t ->
  exists t1, t = TmTAbs t1.
Proof.
  intros t T1 Hty Hval.
  destruct Hval as [T t1 | t1 | ]; inversion Hty; subst.
  exists t1. reflexivity.
Qed.

(* progress *)
Theorem progress :
  forall t T,
  has_type nil t T ->
  value t \/ exists t', t --> t'.
Proof.
  intros t T H.
  remember (@nil ty) as Gamma eqn:HGamma.
  induction H; subst Gamma.
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
  - left. apply V_Unit.
Qed.
