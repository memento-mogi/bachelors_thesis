From Stdlib Require Import Eqdep_dec Arith List.
From FSumProd Require Export Definitions.
Open Scope vec_scope.

Ltac clear_existT :=
  repeat match goal with
  | H : existT _ _ _ = existT _ _ _ |- _ =>
      apply Eqdep_dec.inj_pair2_eq_dec in H; [| apply PeanoNat.Nat.eq_dec]; subst
  end.

(* Vector.Forall2 helper lemmas *)

Lemma Forall2_Vmap :
  forall (X : Type) (f : X -> X) (P : X -> Prop) (Y : Type) (Q Q' : X -> Y -> Prop)
    (p: nat) (xs : V.t X p) (ys : V.t Y p),
      V.Forall P xs ->
      V.Forall2 Q xs ys ->
      (forall x y, P x -> Q x y -> Q' (f x) y) ->
      V.Forall2 Q' (V.map f xs) ys.
Proof.
  intros X f P Y Q Q' p xs ys HP HQ H.
  revert HP HQ.
  induction p as [|p' ].
  - replace xs with (@V.nil X); try (symmetry; apply V.nil_spec).
    replace ys with (@V.nil Y); try (symmetry; apply V.nil_spec).
    intros. simpl. constructor.
  - replace xs with (V.cons _ (V.hd xs) _ (V.tl xs)); try (symmetry; apply V.eta).
    replace ys with (V.cons _ (V.hd ys) _ (V.tl ys)); try (symmetry; apply V.eta).
    remember (V.hd xs) as x. remember (V.tl xs) as xs'.
    remember (V.hd ys) as y. remember (V.tl ys) as ys'.
    intros. inversion HP. inversion HQ. clear_existT. simpl. constructor.
    + apply H; assumption.
    + apply IHp'; assumption.
Qed.

Lemma Forall2_Vmap2 :
  forall (X : Type) (f : X -> X) (P : X -> Prop) (Y : Type) (g : Y -> Y) (Q Q' : X -> Y -> Prop)
    (p : nat) (xs : V.t X p) (ys : V.t Y p),
      V.Forall P xs ->
      V.Forall2 Q xs ys ->
      (forall x y, P x -> Q x y -> Q' (f x) (g y)) ->
      V.Forall2 Q' (V.map f xs) (V.map g ys).
Proof.
  intros X f P Y g Q Q' p xs ys HP HQ H.
  revert HP HQ.
  induction p as [|p' ].
  - replace xs with (@V.nil X); try (symmetry; apply V.nil_spec).
    replace ys with (@V.nil Y); try (symmetry; apply V.nil_spec).
    intros. simpl. constructor.
  - replace xs with (V.cons _ (V.hd xs) _ (V.tl xs)); try (symmetry; apply V.eta).
    replace ys with (V.cons _ (V.hd ys) _ (V.tl ys)); try (symmetry; apply V.eta).
    remember (V.hd xs) as x. remember (V.tl xs) as xs'.
    remember (V.hd ys) as y. remember (V.tl ys) as ys'.
    intros. inversion HP. inversion HQ. clear_existT. simpl. constructor.
    + apply H; assumption.
    + apply IHp'; assumption.
Qed.

Lemma Forall2_replace :
  forall X Y (Q : X -> Y -> Prop) p (v1 : V.t X p) (v2 : V.t Y p) (i : Fin.t p) (x' : X),
    V.Forall2 Q v1 v2 ->
    Q x' (V.nth v2 i) ->
    V.Forall2 Q (V.replace v1 i x') v2.
Proof.
  intros X Y Q p v1 v2 i x' H.
  revert i.
  induction H as [| n a b v1' v2' Hab H' IH]; intros i Hq.
  - inversion i.
  - revert Hq. apply (Fin.caseS' i).
    + cbn. intros Hq. constructor; assumption.
    + intros i' Hq. cbn. constructor.
      * eassumption.
      * apply IH. exact Hq.
Qed.

Lemma Forall2_Vnth :
  forall X Y (Q : X -> Y -> Prop) p (v1 : V.t X p) (v2 : V.t Y p) (i : Fin.t p),
    V.Forall2 Q v1 v2 -> Q (V.nth v1 i) (V.nth v2 i).
Proof.
  intros X Y Q p v1 v2 i H.
  revert i.
  induction H as [| n a b v1' v2' Hab H' IH]; intros i.
  - inversion i.
  - apply (Fin.caseS' i).
    + cbn. assumption.
    + intros i'. cbn. apply IH.
Qed.

Lemma map_ext_Forall : forall (A : Type) (f g : A -> A) p (v : V.t A p),
  V.Forall (fun a => f a = g a) v -> V.map f v = V.map g v.
Proof.
  induction v as [| x p' v' IH]; cbn; intros HF.
  - reflexivity.
  - apply Vector.Forall_cons_iff in HF as [Hx Hv'].
    f_equal; [exact Hx | apply IH; exact Hv'].
Qed.

(* Autosubst で自動的に示されていた補題 *)

Lemma ext_ren_ty : forall T xi1 xi2, (forall n, xi1 n = xi2 n) -> ren_ty xi1 T = ren_ty xi2 T.
Proof.
  intros T. induction T using ty_ind2; intros xi1 xi2 Heq; cbn.
  - f_equal. apply Heq.
  - f_equal; [apply IHT1 | apply IHT2]; assumption.
  - f_equal. apply IHT. intros n. destruct n; cbn; [reflexivity | f_equal; apply Heq].
  - f_equal. apply map_ext_Forall. eapply Vector.Forall_impl; [| eassumption].
    intros a Pa. apply Pa; assumption.
  - f_equal. apply map_ext_Forall. eapply Vector.Forall_impl; [| eassumption].
    intros a Pa. apply Pa; assumption.
Qed.

Lemma ren_ren_ty : forall T xi zeta, ren_ty zeta (ren_ty xi T) = ren_ty (fun n => zeta (xi n)) T.
Proof.
  intros T. induction T using ty_ind2; intros xi zeta; cbn.
  - reflexivity.
  - f_equal; [apply IHT1 | apply IHT2].
  - f_equal. rewrite IHT. apply ext_ren_ty. intros n. destruct n; reflexivity.
  - f_equal. rewrite V.map_map. apply map_ext_Forall. eapply Vector.Forall_impl; [| eassumption].
    intros a Pa. apply Pa.
  - f_equal. rewrite V.map_map. apply map_ext_Forall. eapply Vector.Forall_impl; [| eassumption].
    intros a Pa. apply Pa.
Qed.

Lemma ext_subst_ty : forall T sigma1 sigma2, (forall n, sigma1 n = sigma2 n) -> subst_ty sigma1 T = subst_ty sigma2 T.
Proof.
  intros T. induction T using ty_ind2; intros sigma1 sigma2 Heq; cbn.
  - apply Heq.
  - f_equal; [apply IHT1 | apply IHT2]; assumption.
  - f_equal. apply IHT. intros n. destruct n; cbn; [reflexivity | f_equal; apply Heq].
  - f_equal. apply map_ext_Forall. eapply Vector.Forall_impl; [| eassumption].
    intros a Pa. apply Pa; assumption.
  - f_equal. apply map_ext_Forall. eapply Vector.Forall_impl; [| eassumption].
    intros a Pa. apply Pa; assumption.
Qed.

Lemma ren_subst_ty : forall T xi sigma, ren_ty xi (subst_ty sigma T) = subst_ty (fun n => ren_ty xi (sigma n)) T.
Proof.
  intros T. induction T using ty_ind2; intros xi sigma; cbn.
  - reflexivity.
  - f_equal; [apply IHT1 | apply IHT2].
  - f_equal. rewrite IHT. apply ext_subst_ty. intros n. destruct n; cbn.
    + reflexivity.
    + rewrite ren_ren_ty, ren_ren_ty. apply ext_ren_ty. intros k. reflexivity.
  - f_equal. rewrite V.map_map. apply map_ext_Forall. eapply Vector.Forall_impl; [| eassumption].
    intros a Pa. apply Pa.
  - f_equal. rewrite V.map_map. apply map_ext_Forall. eapply Vector.Forall_impl; [| eassumption].
    intros a Pa. apply Pa.
Qed.

Lemma subst_ren_ty : forall T xi sigma, subst_ty sigma (ren_ty xi T) = subst_ty (fun n => sigma (xi n)) T.
Proof.
  intros T. induction T using ty_ind2; intros xi sigma; cbn.
  - reflexivity.
  - f_equal; [apply IHT1 | apply IHT2].
  - f_equal. rewrite IHT. apply ext_subst_ty. intros n. destruct n; reflexivity.
  - f_equal. rewrite V.map_map. apply map_ext_Forall. eapply Vector.Forall_impl; [| eassumption].
    intros a Pa. apply Pa.
  - f_equal. rewrite V.map_map. apply map_ext_Forall. eapply Vector.Forall_impl; [| eassumption].
    intros a Pa. apply Pa.
Qed.

Lemma subst_subst_ty : forall T sigma tau, subst_ty tau (subst_ty sigma T) = subst_ty (fun n => subst_ty tau (sigma n)) T.
Proof.
  intros T. induction T using ty_ind2; intros sigma tau; cbn.
  - reflexivity.
  - f_equal; [apply IHT1 | apply IHT2].
  - f_equal. rewrite IHT. apply ext_subst_ty. intros n. destruct n; cbn.
    + reflexivity.
    + rewrite ren_subst_ty, subst_ren_ty. reflexivity.
  - f_equal. rewrite V.map_map. apply map_ext_Forall. eapply Vector.Forall_impl; [| eassumption].
    intros a Pa. apply Pa.
  - f_equal. rewrite V.map_map. apply map_ext_Forall. eapply Vector.Forall_impl; [| eassumption].
    intros a Pa. apply Pa.
Qed.

Lemma subst_ty_id : forall T, subst_ty var_ty T = T.
Proof.
  induction T using ty_ind2; cbn.
  - reflexivity.
  - f_equal; assumption.
  - f_equal. erewrite ext_subst_ty; [apply IHT |]. intros n. destruct n; reflexivity.
  - f_equal. rewrite <- (V.map_id _ _ Ts) at 2. apply map_ext_Forall. eapply Vector.Forall_impl; [| eassumption].
    intros a Pa. exact Pa.
  - f_equal. rewrite <- (V.map_id _ _ Ts) at 2. apply map_ext_Forall. eapply Vector.Forall_impl; [| eassumption].
    intros a Pa. exact Pa.
Qed.

Lemma ren_ty_id : forall T, ren_ty id T = T.
Proof.
  induction T using ty_ind2; cbn.
  - reflexivity.
  - f_equal; assumption.
  - f_equal. erewrite ext_ren_ty; [apply IHT |]. intros n. destruct n; reflexivity.
  - f_equal. rewrite <- (V.map_id _ _ Ts) at 2. apply map_ext_Forall. eapply Vector.Forall_impl; [| eassumption].
    intros a Pa. exact Pa.
  - f_equal. rewrite <- (V.map_id _ _ Ts) at 2. apply map_ext_Forall. eapply Vector.Forall_impl; [| eassumption].
    intros a Pa. exact Pa.
Qed.

Lemma ext_ren_tm : forall t xi_ty1 xi_ty2 xi_tm1 xi_tm2,
  (forall n, xi_ty1 n = xi_ty2 n) -> (forall n, xi_tm1 n = xi_tm2 n) ->
  ren_tm xi_ty1 xi_tm1 t = ren_tm xi_ty2 xi_tm2 t.
Proof.
  intros t. induction t using tm_ind2; intros xi_ty1 xi_ty2 xi_tm1 xi_tm2 Heqty Heqtm; cbn.
  - f_equal. apply Heqtm.
  - f_equal. apply IHt; [assumption |].
    intros n. destruct n; cbn; [reflexivity | f_equal; apply Heqtm].
  - f_equal; [apply IHt1 | apply IHt2]; assumption.
  - f_equal. apply IHt; [| assumption].
    intros n. destruct n; cbn; [reflexivity | f_equal; apply Heqty].
  - f_equal; [apply IHt; assumption | apply ext_ren_ty; assumption].
  - f_equal. apply map_ext_Forall. eapply Vector.Forall_impl; [| eassumption].
    intros a Pa. apply Pa; assumption.
  - f_equal. apply IHt; assumption.
  - f_equal. apply IHt; assumption.
  - f_equal; [apply IHt; assumption |].
    apply map_ext_Forall. eapply Vector.Forall_impl; [| eassumption].
    intros a Pa. apply Pa; assumption.
Qed.

Lemma ext_subst_tm : forall t sigma_ty1 sigma_ty2 sigma_tm1 sigma_tm2,
  (forall n, sigma_ty1 n = sigma_ty2 n) -> (forall n, sigma_tm1 n = sigma_tm2 n) ->
  subst_tm sigma_ty1 sigma_tm1 t = subst_tm sigma_ty2 sigma_tm2 t.
Proof.
  intros t. induction t using tm_ind2; intros sigma_ty1 sigma_ty2 sigma_tm1 sigma_tm2 Heqty Heqtm; cbn.
  - apply Heqtm.
  - f_equal. apply IHt; [assumption |].
    intros n. destruct n; cbn; [reflexivity | f_equal; apply Heqtm].
  - f_equal; [apply IHt1 | apply IHt2]; assumption.
  - f_equal. apply IHt.
    + intros n. destruct n; cbn; [reflexivity | f_equal; apply Heqty].
    + intros n. unfold shift_ty_tm. f_equal. apply Heqtm.
  - f_equal; [apply IHt; assumption | apply ext_subst_ty; assumption].
  - f_equal. apply map_ext_Forall. eapply Vector.Forall_impl; [| eassumption].
    intros a Pa. apply Pa; assumption.
  - f_equal. apply IHt; assumption.
  - f_equal. apply IHt; assumption.
  - f_equal; [apply IHt; assumption |].
    apply map_ext_Forall. eapply Vector.Forall_impl; [| eassumption].
    intros a Pa. apply Pa; assumption.
Qed.

(* Beta-reduction properties for renaming and substitution *)
Lemma ren_ty_beta_red : forall T1 S0 xi,
  ren_ty xi (subst_ty (scons S0 var_ty) T1) =
  subst_ty (scons (ren_ty xi S0) var_ty) (ren_ty (up_ren xi) T1).
Proof.
  intros T1 S0 xi.
  rewrite ren_subst_ty, subst_ren_ty.
  apply ext_subst_ty. intros n. destruct n; cbn; reflexivity.
Qed.

Lemma subst_ty_beta_red : forall T1 S0 sigma,
  subst_ty sigma (subst_ty (scons S0 var_ty) T1) =
  subst_ty (scons (subst_ty sigma S0) var_ty) (subst_ty (up_ty sigma) T1).
Proof.
  intros T1 S0 sigma.
  rewrite subst_subst_ty, subst_subst_ty.
  apply ext_subst_ty. intros n. destruct n; cbn.
  - reflexivity.
  - rewrite subst_ren_ty.
    transitivity (subst_ty var_ty (sigma n)).
    + symmetry. apply subst_ty_id.
    + apply ext_subst_ty. intros k. reflexivity.
Qed.

(* weakening / substitution preserve typing *)
Lemma renTm_typing :
  forall t Gamma T,
    <[ Gamma |-- t \in T ]> ->
    forall (xi : nat -> nat) (Gamma' : context),
      (forall x T0, nth_error Gamma x = Some T0 -> nth_error Gamma' (xi x) = Some T0) ->
      <[ Gamma' |-- {ren_tm id xi t} \in T ]>.
Proof.
  intros t.
  induction t using tm_ind2; intros Gamma T Hty xi Gamma' Hxi; cbn in *.
  - inversion Hty; subst; clear_existT. apply T_Var. apply Hxi. assumption.
  - inversion Hty; subst; clear_existT.
    apply T_Abs. eapply IHt.
    + eassumption.
    + intros x T0 Hx. destruct x as [|x]; cbn in Hx |- *; unfold up_ren; cbn.
      * exact Hx.
      * apply Hxi. exact Hx.
  - inversion Hty; subst; clear_existT. eapply T_App; eauto.
  - inversion Hty; subst; clear_existT.
    apply T_TyAbs.
    rewrite ext_ren_tm with (xi_ty2 := id) (xi_tm2 := xi);
      [ | intros n; destruct n; reflexivity | reflexivity].
    eapply IHt.
    + eassumption.
    + intros x T0 Hx. rewrite nth_error_map in Hx.
      destruct (nth_error Gamma x) as [S0|] eqn:EqGx; try discriminate.
      simpl in Hx. inversion Hx; subst T0.
      rewrite nth_error_map, (Hxi x S0 EqGx). reflexivity.
  - inversion Hty; subst; clear_existT.
    eapply T_TyApp.
    + eapply IHt; eassumption.
    + rewrite ren_ty_id. reflexivity.
  - inversion Hty; subst; clear_existT.
    apply T_Tuple.
    eapply Forall2_Vmap.
    + eassumption.
    + eassumption.
    + intros x y Px Hxy. eapply Px; eassumption.
  - inversion Hty; subst; clear_existT. eapply T_Proj.
    eapply IHt; eassumption.
  - inversion Hty; subst; clear_existT. eapply T_Inj.
    eapply IHt; eassumption.
  - inversion Hty; subst; clear_existT.
    eapply T_Case.
    + eapply IHt; eassumption.
    + eapply Forall2_Vmap.
      * eassumption.
      * eassumption.
      * simpl. intros t' T' Pt' HtT'. eapply Pt'; eassumption.
Qed.

Lemma renTy_typing :
  forall t Gamma T,
    <[ Gamma |-- t \in T ]> ->
    forall (xi : nat -> nat) (Gamma' : context),
      (forall x T0, nth_error Gamma x = Some T0 -> nth_error Gamma' x = Some (ren_ty xi T0)) ->
      <[ Gamma' |-- {ren_tm xi id t} \in {ren_ty xi T} ]>.
Proof.
  intros t.
  induction t using tm_ind2; intros Gamma T Hty xi Gamma' Hxi; cbn [ren_tm] in *.
  - inversion Hty; subst; clear_existT. apply T_Var. apply Hxi. assumption.
  - inversion Hty; subst; clear_existT.
    apply T_Abs.
    rewrite ext_ren_tm with (xi_ty2 := xi) (xi_tm2 := id);
      [ | reflexivity | intros n; destruct n; reflexivity].
    eapply IHt with (T := T2).
    + eassumption.
    + intros x T0 Hx. destruct x as [|x]; cbn in Hx |- *.
      * inversion Hx; subst. reflexivity.
      * apply Hxi. exact Hx.
  - inversion Hty; subst; clear_existT.
    eapply T_App with (T1 := ren_ty xi T1).
    + eapply IHt1 with (T := TyArr T1 T); eassumption.
    + eapply IHt2 with (T := T1); eassumption.
  - inversion Hty; subst; clear_existT.
    apply T_TyAbs.
    eapply IHt with (T := T1).
    + eassumption.
    + intros x T0 Hx. rewrite nth_error_map in Hx.
      destruct (nth_error Gamma x) as [S0|] eqn:EqGx; try discriminate.
      simpl in Hx. inversion Hx; subst T0.
      rewrite nth_error_map, (Hxi x S0 EqGx). cbn.
      rewrite ren_ren_ty, ren_ren_ty. reflexivity.
  - inversion Hty; subst; clear_existT.
    eapply T_TyApp with (T1 := ren_ty (up_ren xi) T1).
    + eapply IHt with (T := TyForall T1); eassumption.
    + apply ren_ty_beta_red.
  - inversion Hty; subst; clear_existT.
    apply T_Tuple.
    eapply Forall2_Vmap2.
    + eassumption.
    + eassumption.
    + intros x y Px Hxy. eapply Px; eassumption.
  - inversion Hty; subst; clear_existT.
    rewrite <- (Vector.nth_map (ren_ty xi) Ts i i eq_refl).
    eapply T_Proj. eapply IHt with (T := TyProd p Ts); eassumption.
  - inversion Hty; subst; clear_existT.
    eapply T_Inj.
    change (has_type Gamma' (ren_tm xi id t) (V.nth (V.map (ren_ty xi) Ts) i)).
    rewrite (Vector.nth_map (ren_ty xi) Ts i i eq_refl).
    eapply IHt with (T := V.nth Ts i); eassumption.
  - inversion Hty; subst; clear_existT.
    eapply T_Case.
    + eapply IHt with (T := TySum p Ts); eassumption.
    + eapply Forall2_Vmap2.
      * eassumption.
      * eassumption.
      * simpl. intros t' T' Pt' HtT'.
        eapply Pt' with (T := TyArr T' T); eassumption.
Qed.

(* substitution preserves typing *)
Lemma tmsubst_preserves_typing :
  forall t Gamma T,
    <[ Gamma |-- t \in T ]> ->
    forall (sigma : nat -> tm) (Gamma' : context),
      (forall x T0, nth_error Gamma x = Some T0 -> <[ Gamma' |-- {sigma x} \in T0 ]>) ->
      <[ Gamma' |-- {subst_tm var_ty sigma t} \in T ]>.
Proof.
  intros t.
  induction t using tm_ind2; intros Gamma T Hty sigma Gamma' Hsig; cbn [subst_tm] in *.
  - inversion Hty; subst; clear_existT. apply Hsig. assumption.
  - inversion Hty; subst; clear_existT.
    apply T_Abs.
    eapply IHt with (T := T2).
    + eassumption.
    + intros x T0 Hx. destruct x as [|x]; cbn in Hx |- *; unfold up_tm.
      * inversion Hx; subst. apply T_Var. reflexivity.
      * eapply renTm_typing.
        -- apply Hsig. exact Hx.
        -- intros y T1' Hy. exact Hy.
  - inversion Hty; subst; clear_existT.
    eapply T_App.
    + eapply IHt1 with (T := TyArr T1 T); eassumption.
    + eapply IHt2 with (T := T1); eassumption.
  - inversion Hty; subst; clear_existT.
    apply T_TyAbs.
    rewrite ext_subst_tm with (sigma_ty2 := var_ty) (sigma_tm2 := shift_ty_tm sigma);
      [ | intros n; destruct n; reflexivity | reflexivity].
    eapply IHt with (T := T1).
    + eassumption.
    + intros x T0 Hx. rewrite nth_error_map in Hx.
      destruct (nth_error Gamma x) as [S0|] eqn:EqGx; try discriminate.
      simpl in Hx. inversion Hx; subst T0.
      unfold shift_ty_tm.
      eapply renTy_typing with (T := S0).
      * apply Hsig. eassumption.
      * intros y T1' Hy. rewrite nth_error_map, Hy. reflexivity.
  - inversion Hty; subst; clear_existT.
    eapply T_TyApp with (T1 := T1).
    + eapply IHt with (T := TyForall T1); eassumption.
    + rewrite subst_ty_id. reflexivity.
  - inversion Hty; subst; clear_existT.
    apply T_Tuple.
    eapply Forall2_Vmap.
    + eassumption.
    + eassumption.
    + intros x y Px Hxy. eapply Px; eassumption.
  - inversion Hty; subst; clear_existT. eapply T_Proj.
    eapply IHt with (T := TyProd p Ts); eassumption.
  - inversion Hty; subst; clear_existT. eapply T_Inj.
    eapply IHt with (T := V.nth Ts i); eassumption.
  - inversion Hty; subst; clear_existT.
    eapply T_Case.
    + eapply IHt with (T := TySum p Ts); eassumption.
    + eapply Forall2_Vmap.
      * eassumption.
      * eassumption.
      * simpl. intros t' T' Pt' HtT'. eapply Pt'; eassumption.
Qed.

(* type substitution preserves typing *)
Lemma tysubst_preserves_typing :
  forall t Gamma T,
    <[ Gamma |-- t \in T ]> ->
    forall (sigma : nat -> ty) (Gamma' : context),
      (forall x T0, nth_error Gamma x = Some T0 -> nth_error Gamma' x = Some (subst_ty sigma T0)) ->
      <[ Gamma' |-- {subst_tm sigma var_tm t} \in {subst_ty sigma T} ]>.
Proof.
  intros t.
  induction t using tm_ind2; intros Gamma T Hty sigma Gamma' Hxi; cbn [subst_tm] in *.
  - inversion Hty; subst; clear_existT. apply T_Var. apply Hxi. assumption.
  - inversion Hty; subst; clear_existT.
    apply T_Abs.
    rewrite ext_subst_tm with (sigma_ty2 := sigma) (sigma_tm2 := var_tm);
      [ | reflexivity | intros n; destruct n; reflexivity].
    eapply IHt with (T := T2).
    + eassumption.
    + intros x T0 Hx. destruct x as [|x]; cbn in Hx |- *.
      * inversion Hx; subst. reflexivity.
      * apply Hxi. exact Hx.
  - inversion Hty; subst; clear_existT.
    eapply T_App with (T1 := subst_ty sigma T1).
    + eapply IHt1 with (T := TyArr T1 T); eassumption.
    + eapply IHt2 with (T := T1); eassumption.
  - inversion Hty; subst; clear_existT.
    apply T_TyAbs.
    eapply IHt with (T := T1).
    + eassumption.
    + intros x T0 Hx. rewrite nth_error_map in Hx.
      destruct (nth_error Gamma x) as [S0|] eqn:EqGx; try discriminate.
      simpl in Hx. inversion Hx; subst T0.
      rewrite nth_error_map, (Hxi x S0 EqGx). cbn.
      rewrite ren_subst_ty, subst_ren_ty. reflexivity.
  - inversion Hty; subst; clear_existT.
    eapply T_TyApp with (T1 := subst_ty (up_ty sigma) T1).
    + eapply IHt with (T := TyForall T1); eassumption.
    + apply subst_ty_beta_red.
  - inversion Hty; subst; clear_existT.
    apply T_Tuple.
    eapply Forall2_Vmap2.
    + eassumption.
    + eassumption.
    + intros x y Px Hxy. eapply Px; eassumption.
  - inversion Hty; subst; clear_existT.
    rewrite <- (Vector.nth_map (subst_ty sigma) Ts i i eq_refl).
    eapply T_Proj. eapply IHt with (T := TyProd p Ts); eassumption.
  - inversion Hty; subst; clear_existT.
    eapply T_Inj.
    change (has_type Gamma' (subst_tm sigma var_tm t) (V.nth (V.map (subst_ty sigma) Ts) i)).
    rewrite (Vector.nth_map (subst_ty sigma) Ts i i eq_refl).
    eapply IHt with (T := V.nth Ts i); eassumption.
  - inversion Hty; subst; clear_existT.
    eapply T_Case.
    + eapply IHt with (T := TySum p Ts); eassumption.
    + eapply Forall2_Vmap2.
      * eassumption.
      * eassumption.
      * simpl. intros t' T' Pt' HtT'.
        eapply Pt' with (T := TyArr T' T); eassumption.
Qed.

Lemma tmsubst1_preserves_typing :
  forall Gamma T1 T2 t1 t2,
    <[ Gamma |-- t2 \in T1 ]> ->
    <[ T1 :: Gamma |-- t1 \in T2 ]> ->
    <[ Gamma |-- {subst_tm var_ty (scons t2 var_tm) t1} \in T2 ]>.
Proof.
  intros Gamma T1 T2 t1 t2 Ht2 Ht1.
  eapply tmsubst_preserves_typing.
  - eassumption.
  - intros x T0 Hx. destruct x as [|x]; cbn in Hx.
    + injection Hx as Hx. subst. assumption.
    + apply T_Var. assumption.
Qed.

(* preservation *)
Lemma preservation :
  forall t Gamma T,
    <[ Gamma |-- t \in T ]> ->
    forall t', t --> t' -> <[ Gamma |-- t' \in T ]>.
Proof.
  intros t.
  induction t using tm_ind2; intros Gamma T Hty t' Hstep.
  - inversion Hstep.
  - inversion Hstep.
  - inversion Hty; subst; clear_existT.
    inversion Hstep; subst; clear_existT.
    + inversion H1; subst; clear_existT. eapply tmsubst1_preserves_typing; eauto.
    + eapply T_App; eauto.
    + eapply T_App; eauto.
  - inversion Hstep.
  - inversion Hty; subst; clear_existT.
    inversion Hstep; subst; clear_existT.
    + inversion H1; subst; clear_existT.
      eapply tysubst_preserves_typing.
      * eassumption.
      * intros x T2 Hx. rewrite nth_error_map in Hx.
        destruct (nth_error Gamma x) as [S0|] eqn:EqGx; try discriminate.
        simpl in Hx. inversion Hx; subst T2.
        f_equal.
        rewrite subst_ren_ty.
        rewrite (ext_subst_ty S0 (fun n => scons T0 var_ty (S n)) var_ty);
          [symmetry; apply subst_ty_id | intros k; reflexivity].
    + eapply T_TyApp; eauto.
  - inversion Hty; subst; clear_existT.
    inversion Hstep; subst; clear_existT.
    apply T_Tuple.
    eapply Forall2_replace; try eassumption.
    apply Forall2_Vnth with (i := i) in H3.
    eapply (proj1 (Vector.Forall_nth _ _ _ _) H i); eassumption.
  - inversion Hty; subst; clear_existT.
    inversion Hstep; subst; clear_existT.
    + inversion H3; subst; clear_existT.
      apply Forall2_Vnth. assumption.
    + eapply T_Proj; eauto.
  - inversion Hty; subst; clear_existT.
    inversion Hstep; subst; clear_existT.
    eapply T_Inj; eauto.
  - inversion Hty; subst; clear_existT.
    inversion Hstep; subst; clear_existT.
    + eapply T_Case; eauto.
    + eapply T_Case.
      * eassumption.
      * eapply Forall2_replace; [eassumption |].
        apply Forall2_Vnth with (i := j) in H5.
        eapply (proj1 (Vector.Forall_nth _ _ _ _) H j); eassumption.
    + inversion H4; subst; clear_existT.
      eapply T_App.
      * apply (Forall2_Vnth _ _ _ _ _ _ i H5).
      * apply H1.
Qed.

(* canonical forms *)
Lemma canonical_forms_arr :
  forall Gamma (t : tm) T1 T2,
    <[ Gamma |-- t \in T1 -> T2 ]> ->
    value t ->
    exists t1, t = abs t1.
Proof.
  intros Gamma t T1 T2 Hty Hval.
  destruct Hval as [t1 | t1 | p ts Hts | p0 i t0 Hv0].
  - exists t1. reflexivity.
  - inversion Hty.
  - inversion Hty.
  - inversion Hty.
Qed.

Lemma canonical_forms_forall :
  forall Gamma (t : tm) T1,
    <[ Gamma |-- t \in -/, T1 ]> ->
    value t ->
    exists t1, t = tyabs t1.
Proof.
  intros Gamma t T1 Hty Hval.
  destruct Hval as [t1 | t1 | p ts Hts | p0 i t0 Hv0].
  - inversion Hty.
  - exists t1. reflexivity.
  - inversion Hty.
  - inversion Hty.
Qed.

Lemma canonical_forms_prod :
  forall Gamma (t : tm) p (Ts : V.t ty p),
    <[ Gamma |-- t \in {TyProd p Ts} ]> ->
    value t ->
    exists ts, t = tuple p ts.
Proof.
  intros Gamma t p Ts Hty Hval.
  destruct Hval as [t1 | t1 | p' ts Hts | p0 i t0 Hv0].
  - inversion Hty.
  - inversion Hty.
  - inversion Hty; subst; clear_existT. exists ts. reflexivity.
  - inversion Hty.
Qed.

Lemma canonical_forms_sum :
  forall Gamma (t : tm) p (Ts : V.t ty p),
    <[ Gamma |-- t \in {TySum p Ts} ]> ->
    value t ->
    exists (i : Fin.t p) t1, t = inj p i t1.
Proof.
  intros Gamma t p Ts Hty Hval.
  destruct Hval as [t1 | t1 | p' ts Hts | p0 i t0 Hv0].
  - inversion Hty.
  - inversion Hty.
  - inversion Hty.
  - inversion Hty; subst; clear_existT. exists i, t0. reflexivity.
Qed.

Lemma vec_progress :
  forall p (ts : V.t tm p),
    V.Forall (fun t => value t \/ exists t', t --> t') ts ->
    V.Forall value ts \/ (exists (i : Fin.t p) t', V.nth ts i --> t').
Proof.
  induction ts as [| x p' ts' IH]; intros Hall.
  - left. constructor.
  - apply Vector.Forall_cons_iff in Hall as [Hx Hts'].
    destruct Hx as [Hv | [t' Hstep]].
    + destruct (IH Hts') as [Hallt | [i [t'' Hstep]]].
      * left. constructor; assumption.
      * right. exists (Fin.FS i), t''. exact Hstep.
    + right. exists Fin.F1, t'. exact Hstep.
Qed.

Lemma Forall_combine3 :
  forall p (ts : V.t tm p) (Ts : V.t ty p),
    V.Forall (fun t => forall T0, <[ nil |-- t \in T0 ]> -> value t \/ exists t', t --> t') ts ->
    V.Forall2 (has_type nil) ts Ts ->
    V.Forall (fun t => value t \/ exists t', t --> t') ts.
Proof.
  intros p ts Ts.
  refine (@Vector.rect2 tm ty
    (fun n v1 v2 =>
       V.Forall (fun t => forall T0, <[ nil |-- t \in T0 ]> -> value t \/ exists t', t --> t') v1 ->
       V.Forall2 (has_type nil) v1 v2 ->
       V.Forall (fun t => value t \/ exists t', t --> t') v1)
    _ _ p ts Ts).
  - intros _ _. constructor.
  - intros n v1 v2 IH a b HIH HF2.
    apply Vector.Forall_cons_iff in HIH as [Ha HIH'].
    apply Vector.Forall2_cons_iff in HF2 as [Hab HF2'].
    constructor.
    + eapply Ha; eauto.
    + eapply IH; eauto.
Qed.

(* progress *)
Lemma progress :
  forall t T,
    <[ nil |-- t \in T ]> ->
    value t \/ exists t', t --> t'.
Proof.
  intros t.
  induction t using tm_ind2; intros T Hty.
  - inversion Hty; subst; clear_existT.
    rewrite nth_error_nil in H0. discriminate H0.
  - left. constructor.
  - inversion Hty; subst; clear_existT.
    destruct (IHt1 (TyArr T1 T) H1) as [Hv1 | [t1' Hs1]].
    + destruct (IHt2 T1 H3) as [Hv2 | [t2' Hs2]].
      * destruct (canonical_forms_arr _ _ _ _ H1 Hv1) as [t1'' ->].
        right. eexists. constructor. assumption.
      * right. eexists. apply ST_App2; [exact Hv1 | exact Hs2].
    + right. eexists. apply ST_App1; exact Hs1.
  - left. constructor.
  - inversion Hty; subst; clear_existT.
    destruct (IHt (TyForall T1) H1) as [Hv | [t1' Hs]].
    + destruct (canonical_forms_forall _ _ _ H1 Hv) as [t1'' ->].
      right. eexists. apply ST_TyAppTyAbs.
    + right. eexists. apply ST_TyApp1. exact Hs.
  - inversion Hty; subst; clear_existT.
    destruct (vec_progress p ts (Forall_combine3 p ts Ts H H3)) as [Hallv | [i [t' Hstep]]].
    + left. constructor. assumption.
    + right. eexists. eapply ST_Tuple; eassumption.
  - inversion Hty; subst; clear_existT.
    destruct (IHt (TyProd p Ts) H3) as [Hv | [t1' Hs]].
    + destruct (canonical_forms_prod _ _ _ _ H3 Hv) as [ts ->].
      assert (Hallval : V.Forall value ts) by (inversion Hv; subst; clear_existT; assumption).
      right. eexists. eapply (ST_ProjRed p i ts). exact Hallval.
    + right. eexists. apply ST_Proj1; exact Hs.
  - inversion Hty; subst; clear_existT.
    destruct (IHt (V.nth Ts i) H3) as [Hv | [t1' Hs]].
    + left. constructor. assumption.
    + right. eexists. apply ST_Inj1; exact Hs.
  - inversion Hty; subst; clear_existT.
    destruct (IHt (TySum p Ts) H4) as [Hv | [t1' Hs]].
    + destruct (canonical_forms_sum _ _ _ _ H4 Hv) as [i0 [t0 ->]].
      right. eexists. eapply ST_CaseInjRed.
      * reflexivity.
      * inversion Hv; subst; clear_existT; assumption.
      * reflexivity.
    + right. eexists. apply ST_Case1; exact Hs.
Qed.

Print Assumptions preservation.
Print Assumptions progress.
Print Assumptions renTm_typing.
Print Assumptions renTy_typing.
Print Assumptions tmsubst_preserves_typing.
Print Assumptions tysubst_preserves_typing.
