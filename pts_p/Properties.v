From Stdlib Require Import Nat List FunctionalExtensionality.
From FomegaMono Require Export Definitions.

Ltac dauto := try (intros _x; destruct _x; auto).

(* Properties *)
(* Basic lemmas on term evaluation and equivalence *)
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

Lemma tmeval_refl :
  forall T, T ==> T.
  induction T; constructor; assumption.
Qed.

Lemma tmeq_sym :
  forall S T, S === T -> T === S.
Proof.
  intros. induction H.
  - apply multi_refl.
  - apply tmeq_append with T2. split.
    + assumption.
    + destruct H; [right | left]; assumption.
Qed.

Lemma tmeq_trans :
  forall S T U, (S === U) /\ (U === T) -> S === T.
Proof.
  intros. destruct H as [HS HT].
  generalize dependent T. induction HS; intros U H1.
  - assumption.
  - apply multi_step with T2.
    + assumption.
    + apply IHHS. assumption.
Qed.

Lemma multi_step_implies_tmeq :
  forall S T, multi tm_eval_step S T -> S === T.
Proof.
  intros. induction H.
  - apply multi_refl.
  - apply multi_step with T2.
    + left. assumption.
    + apply IHmulti.
Qed.

(* Renaming *)
Lemma ren_tmeval : forall T1 T2,
  T1 ==> T2 ->
  forall xi,
  (ren_Tm xi T1) ==> (ren_Tm xi T2).
Proof.
  intros T1 T2 H. induction H; intros; asolve;
  try (constructor;
       try apply IHtm_eval_step;
       try apply IHtm_eval_step1;
       try apply IHtm_eval_step2
    ).
  - subst S. asolve. eapply TST_Red.
    + eapply IHtm_eval_step1.
    + eapply IHtm_eval_step2.
    + asolve. apply ext_Tm. intros. destruct x; asolve.
Qed.

Lemma ren_tmeq : forall T1 T2,
  T1 === T2 ->
  forall xi,
  (ren_Tm xi T1) === (ren_Tm xi T2).
Proof.
  intros T1 T2 H. induction H; intros; asolve.
  - apply multi_refl.
  - apply multi_step with (T2:=ren_Tm xi T2).
    + destruct H; [left | right]; apply ren_tmeval; assumption.
    + apply IHmulti.
Qed.

Lemma ren_shift_up : forall xi (t : Tm),
  ren_Tm (upRen_Tm_Tm xi) (ren_Tm S t) = ren_Tm S (ren_Tm xi t).
Proof.
  intros. rewrite renRen_Tm. rewrite renRen_Tm.
  apply extRen_Tm. intros n. reflexivity.
Qed.

Lemma upRen_Tm_Tm_zero : forall xi, upRen_Tm_Tm xi 0 = 0.
Proof. reflexivity. Qed.

Lemma upRen_Tm_Tm_succ : forall xi n, upRen_Tm_Tm xi (S n) = S (xi n).
Proof. reflexivity. Qed.

Lemma ren_tm_betared : forall B t2 xi,
  ren_Tm xi (tm_tm_betared B t2) =
  tm_tm_betared (ren_Tm (upRen_Tm_Tm xi) B) (ren_Tm xi t2).
Proof.
  intros. unfold tm_tm_betared.
  rewrite renRen_Tm. rewrite substRen_Tm.
  rewrite renSubst_Tm. rewrite substRen_Tm.
  apply ext_Tm. intros n. destruct n; unfold core.funcomp, sigma_tm_one; simpl.
  - rewrite renRen_Tm. rewrite renRen_Tm. rewrite renRen_Tm.
    apply extRen_Tm. intros m. reflexivity.
  - reflexivity.
Qed.

Lemma at_ren : forall Gamma x T,
  at_tm Gamma x T ->
  forall Gamma' xi,
  (forall y S, at_tm Gamma y S -> at_tm Gamma' (xi y) (ren_Tm xi S)) ->
  at_tm Gamma' (xi x) (ren_Tm xi T).
Proof.
  intros Gamma x T H. induction H; intros Gamma' xi Hxi.
  - apply Hxi. apply at_here.
  - apply Hxi. apply at_there. assumption.
Qed.

Lemma at_up_cons : forall Gamma Gamma' xi A,
  (forall x S, at_tm Gamma x S -> at_tm Gamma' (xi x) (ren_Tm xi S)) ->
  (forall x S, at_tm (A :: Gamma) x S ->
    at_tm (ren_Tm xi A :: Gamma') (upRen_Tm_Tm xi x) (ren_Tm (upRen_Tm_Tm xi) S)).
Proof.
  intros Gamma Gamma' xi A Hxi x S HS.
  inversion HS; subst.
  - rewrite upRen_Tm_Tm_zero. rewrite ren_shift_up. apply at_here.
  - rewrite upRen_Tm_Tm_succ. rewrite ren_shift_up. apply at_there.
    apply Hxi. assumption.
Qed.

Lemma ren_typing : forall Gamma t T,
  <[ Gamma |-- t \in T ]> ->
  forall Gamma' xi,
  (forall x S, at_tm Gamma x S -> at_tm Gamma' (xi x) (ren_Tm xi S)) ->
  <[ Gamma' |-- {ren_Tm xi t} \in {ren_Tm xi T} ]>.
Proof.
  intros Gamma t T H.
  induction H; intros Gamma' xi Hxi; simpl.
  - apply T_Var. apply at_ren with Gamma; assumption.
  - apply T_Sort.
  - eapply T_Pi.
    + apply IHhas_type1. assumption.
    + eassumption.
    + apply IHhas_type2. apply at_up_cons. assumption.
  - eapply T_Abs.
    + apply IHhas_type1. assumption.
    + eassumption.
    + apply IHhas_type2. apply at_up_cons. assumption.
    + apply IHhas_type3. assumption.
  - subst B'. eapply T_App.
    + apply IHhas_type1. assumption.
    + apply IHhas_type2. assumption.
    + apply ren_tm_betared.
  - eapply T_Conv.
    + apply IHhas_type1. assumption.
    + apply ren_tmeq. assumption.
    + apply IHhas_type2. assumption.
  - apply T_Unit.
  - apply T_Tt.
Qed.

(* Substitution *)
Lemma subst_tmeval : forall T1 T2,
  T1 ==> T2 ->
  forall sigma,
  (subst_Tm sigma T1) ==> (subst_Tm sigma T2).
Proof.
  intros T1 T2 H. induction H; intros; asolve;
  try (constructor;
       try apply IHtm_eval_step;
       try apply IHtm_eval_step1;
       try apply IHtm_eval_step2
    ).
  - apply tmeval_refl.
  - subst S. asolve. eapply TST_Red.
    + eapply IHtm_eval_step1.
    + eapply IHtm_eval_step2.
    + asolve. apply ext_Tm. intros. destruct x; asolve.
      * apply ext_Tm. intros x. rewrite renRen_Tm. asolve.
      * asolve.
Qed.

Lemma subst_tmeq : forall T1 T2,
  T1 === T2 ->
  forall sigma,
  (subst_Tm sigma T1) === (subst_Tm sigma T2).
Proof.
  intros T1 T2 H. induction H; intros.
  - apply multi_refl.
  - apply multi_step with (T2:=subst_Tm sigma T2).
    + destruct H; [left|right]; apply subst_tmeval;
      assumption.
    + apply IHmulti.
Qed.

Lemma subst_shift_up : forall sigma (t : Tm),
  subst_Tm (up_Tm_Tm sigma) (ren_Tm S t) = ren_Tm S (subst_Tm sigma t).
Proof.
  intros. rewrite renSubst_Tm. rewrite substRen_Tm.
  apply ext_Tm. intros n. reflexivity.
Qed.

Lemma at_subst_cons : forall Gamma Gamma' sigma A,
  (forall x S, at_tm Gamma x S -> <[ Gamma' |-- {sigma x} \in {subst_Tm sigma S} ]>) ->
  (forall x S, at_tm (A :: Gamma) x S ->
    <[ subst_Tm sigma A :: Gamma' |-- {up_Tm_Tm sigma x} \in {subst_Tm (up_Tm_Tm sigma) S} ]>).
Proof.
  intros Gamma Gamma' sigma A Hsig x S HS.
  inversion HS; subst.
  - rewrite subst_shift_up. apply T_Var. apply at_here.
  - rewrite subst_shift_up. simpl.
    eapply ren_typing.
    + apply Hsig. eassumption.
    + intros y T Hy. apply at_there. assumption.
Qed.

Lemma subst_tm_betared : forall B t2 sigma,
  subst_Tm sigma (tm_tm_betared B t2) =
  tm_tm_betared (subst_Tm (up_Tm_Tm sigma) B) (subst_Tm sigma t2).
Proof.
  intros. unfold tm_tm_betared. asolve.
  apply ext_Tm. intros x. destruct x; asolve.
  symmetry. apply idSubst_Tm. reflexivity.
Qed.

Lemma subst_typing : forall Gamma t T,
  <[ Gamma |-- t \in T ]> ->
  forall Gamma' sigma,
  (forall x S, at_tm Gamma x S -> <[ Gamma' |-- {sigma x} \in {subst_Tm sigma S} ]>) ->
  <[ Gamma' |-- {subst_Tm sigma t} \in {subst_Tm sigma T} ]>.
Proof.
  intros Gamma t T H.
  induction H; intros Gamma' sigma Hsig; simpl.
  - apply Hsig. assumption.
  - apply T_Sort.
  - eapply T_Pi.
    + apply IHhas_type1. assumption.
    + eassumption.
    + apply IHhas_type2. apply at_subst_cons. assumption.
  - eapply T_Abs.
    + apply IHhas_type1. assumption.
    + eassumption.
    + apply IHhas_type2. apply at_subst_cons. assumption.
    + apply IHhas_type3. assumption.
  - subst B'. eapply T_App.
    + apply IHhas_type1. assumption.
    + apply IHhas_type2. assumption.
    + apply subst_tm_betared.
  - eapply T_Conv.
    + apply IHhas_type1. assumption.
    + apply subst_tmeq. assumption.
    + apply IHhas_type2. assumption.
  - apply T_Unit.
  - apply T_Tt.
Qed.

Lemma subst_tmeval_lemma :
  forall T T',
  T ==> T' ->
  forall sigma sigma',
  (forall n, (sigma n) ==> (sigma' n)) ->
  subst_Tm sigma T ==> subst_Tm sigma' T'.
Proof.
  intros T T' H. induction H; intros sigma sigma' Hs; asolve.
  - constructor.
  - constructor.
  - constructor.
  - apply TST_Pi.
    + apply IHtm_eval_step1. assumption.
    + apply IHtm_eval_step2. intros n. destruct n.
      * constructor.
      * apply ren_tmeval. apply Hs.
  - apply TST_Abs.
    + apply IHtm_eval_step1. assumption.
    + apply IHtm_eval_step2. intros n. destruct n.
      * constructor.
      * apply ren_tmeval. apply Hs.
  - constructor; [apply IHtm_eval_step1 | apply IHtm_eval_step2]; assumption.
  - eapply TST_Red with (S1:=(subst_Tm (
                                fun n : nat => match n with
                                  | 0 => 0
                                  | Datatypes.S n' => ren_Tm Datatypes.S (sigma' n')
                                end
                              ) S1)).
    + eapply IHtm_eval_step1. intros n. destruct n.
      * constructor.
      * apply ren_tmeval. apply Hs.
    + apply IHtm_eval_step2. eassumption.
    + subst S. asolve. apply ext_Tm. intros x. destruct x; asolve.
      * apply ext_Tm. intros y. rewrite renRen_Tm. asolve.
      * symmetry. apply idSubst_Tm. reflexivity.
Qed.

(* Confluence *)
Lemma tmtmbetared_tmeval_lemma :
  forall S1 S2 T1 T2,
    (S1 ==> T1) ->
    (S2 ==> T2) ->
    tm_tm_betared S1 S2 ==> tm_tm_betared T1 T2.
Proof.
  intros. unfold tm_tm_betared.
  apply ren_tmeval. apply subst_tmeval_lemma.
  - assumption.
  - intros. destruct n; unfold sigma_tm_one; asolve.
    + apply ren_tmeval. assumption.
    + constructor.
Qed.

Lemma confluence_single :
  forall S T U,
    (S ==> T) /\ (S ==> U) ->
    exists V, (T ==> V) /\ (U ==> V).
Proof.
  intros. destruct H as [HT HU].
  generalize dependent U. induction HT; intros;
  try (inversion HU; eexists; split; constructor; fail).
  - inversion HU; subst.
    edestruct IHHT1 as [V1 [IH11 IH12] ]; [eassumption|].
    edestruct IHHT2 as [V2 [IH21 IH22] ]; [eassumption|].
    eexists. split; apply TST_Pi; eassumption.
  - inversion HU; subst.
    edestruct IHHT1 as [V1 [IH11 IH12] ]; [eassumption|].
    edestruct IHHT2 as [V2 [IH21 IH22] ]; [eassumption|].
    eexists. split; apply TST_Abs; eassumption.
  - inversion HU; subst.
    + edestruct IHHT1 as [V1 [IH11 IH12] ]; [eassumption|].
      edestruct IHHT2 as [V2 [IH21 IH22] ]; [eassumption|].
      eexists. split; apply TST_App; eassumption.
    + edestruct IHHT1 as [V1 [IH11 IH12] ].
      { apply TST_Abs. - apply tmeval_refl. - exact H1. }
      edestruct IHHT2 as [V2 [IH21 IH22] ]; [exact H2|].
      inversion IH12; subst.
      inversion HT1; subst.
      inversion IH11; subst.
      exists (tm_tm_betared t2 V2). split.
      * eapply TST_Red; try eassumption. reflexivity.
      * apply tmtmbetared_tmeval_lemma; eassumption.
  - inversion HU; subst.
    + match goal with
      | [ Hx : <{\:A,T1}> ==> _ |- _ ] =>
          inversion Hx as [ | | | | A2 S1v HA2 HS1v | | | ]; subst
      end.
      edestruct IHHT1 as [V11 [IH11 IH12] ]; [eassumption|].
      edestruct IHHT2 as [V2 [IH21 IH22] ]; [eassumption|].
      exists (tm_tm_betared V11 V2). split.
      * apply tmtmbetared_tmeval_lemma; eassumption.
      * eapply TST_Red; try eassumption. reflexivity.
    + edestruct IHHT1 as [V1 [IH11 IH12] ]; [eassumption|].
      edestruct IHHT2 as [V2 [IH21 IH22] ]; [eassumption|].
      exists (tm_tm_betared V1 V2). split.
      * apply tmtmbetared_tmeval_lemma; eassumption.
      * apply tmtmbetared_tmeval_lemma; eassumption.
Qed.

Lemma confluence_multi_single :
  forall S T U,
  multi tm_eval_step S T /\ (S ==> U) ->
  exists V, (T ==> V) /\ multi tm_eval_step U V.
Proof.
  intros. destruct H as [HT HU].
  generalize dependent U. induction HT; intros.
  - exists U. split.
    + assumption.
    + constructor.
  - assert (HV': exists V', (T2==>V') /\ (U==>V')).
    + eapply confluence_single; split; eassumption.
    + destruct HV' as [V' [HV'1 HV'2] ].
      apply IHHT in HV'1 as [V0 [HV'11 HV'12 ] ].
      exists V0. split.
      * assumption.
      * econstructor; eassumption.
Qed.

Lemma confluence_multi :
  forall S T U,
    multi tm_eval_step S T /\ multi tm_eval_step S U ->
    exists V, multi tm_eval_step T V /\ multi tm_eval_step U V.

Proof.
  intros. destruct H as [HT HU].
  generalize dependent U. induction HT; intros.
  - exists U. split. + assumption. + constructor.
  - assert (HV': exists V', ((U ==> V') /\ multi tm_eval_step T2 V')).
    + apply confluence_multi_single with T1. split; assumption.
    + destruct HV' as [V' [HV'1 HV'2] ].
      apply IHHT in HV'2 as [V0 [HV'11 HV'12 ] ].
      exists V0. split.
      * assumption.
      * econstructor; eassumption.
Qed.

Lemma tmeq_implies_confluence :
  forall S T,
    (S === T) ->
    exists U, multi tm_eval_step S U /\ multi tm_eval_step T U.
Proof.
  intros. induction H.
  - exists T. split; constructor.
  - destruct IHmulti as [U' [IH2 IH3] ].
    destruct H.
    + exists U'. split.
      * econstructor; eassumption.
      * assumption.
    + assert (exists V, (U' ==> V) /\ multi tm_eval_step T1 V).
      * apply confluence_multi_single with T2. split; assumption.
      * destruct H1 as [V [HU HT3] ]. exists V. split; try assumption.
        eapply tmeval_append. split; eassumption.
Qed.

(* Standard forms *)
Lemma tmeval_preserves_form_pi :
  forall S1 S2 T,
  multi tm_eval_step <{Pi S1,S2}> T ->
  exists T1 T2,
  T = <{Pi T1,T2}> /\ (multi tm_eval_step S1 T1) /\ (multi tm_eval_step S2 T2).
Proof.
  intros. remember <{Pi S1,S2}> as S.
  generalize dependent HeqS. generalize dependent S2. generalize dependent S1.
  induction H; intros.
  - exists S1, S2; repeat split; try assumption; apply multi_refl.
  - rename T1 into S, T2 into U, T3 into T.
    subst S. inversion H.
    subst A1 B1. symmetry in H4.
    apply IHmulti in H4 as [T1 [T2 [HT [H6 H7] ] ] ].
    exists T1, T2. repeat split; try assumption.
    + apply multi_step with A2; assumption.
    + apply multi_step with B2; assumption.
Qed.

Lemma invert_tmeq_pi :
  forall S1 S2 T1 T2,
  <{Pi S1,S2}> === <{Pi T1,T2}> ->
  (S1 === T1) /\ (S2 === T2).
Proof.
  intros. apply tmeq_implies_confluence in H as [U [H1 H2] ].
  apply tmeval_preserves_form_pi in H1 as [U1 [U2 [HU [H11 H12] ] ] ].
  apply tmeval_preserves_form_pi in H2 as [V1 [V2 [HV [H21 H22] ] ] ].
  subst U. inversion HV. subst V1 V2. clear HV. split;
  eapply tmeq_trans; split; [ | apply tmeq_sym | | apply tmeq_sym ];
  apply multi_step_implies_tmeq; eassumption.
Qed.

Lemma tmeval_preserves_form_sort :
  forall s T,
  multi tm_eval_step <{ {TmSort s} }> T ->
  T = <{ {TmSort s} }>.
Proof.
  intros. remember <{ {TmSort s} }> as S.
  generalize dependent HeqS.
  induction H; intros.
  - reflexivity.
  - subst T1. inversion H. subst T2. apply IHmulti. reflexivity.
Qed.

Lemma invert_tmeq_sort :
  forall s1 s2,
  <{ {TmSort s1} }> === <{ {TmSort s2} }> ->
  s1 = s2.
Proof.
  intros. apply tmeq_implies_confluence in H as [U [H1 H2] ].
  apply tmeval_preserves_form_sort in H1.
  apply tmeval_preserves_form_sort in H2.
  subst. inversion H2. reflexivity.
Qed.

Lemma tmeval_preserves_form_unit :
  forall T,
  multi tm_eval_step <{Unit}> T ->
  T = <{Unit}>.
Proof.
  intros. remember <{Unit}> as S.
  generalize dependent HeqS.
  induction H; intros.
  - reflexivity.
  - subst T1. inversion H. subst T2. apply IHmulti. reflexivity.
Qed.

Lemma tmeval_preserves_form_tt :
  forall T,
  multi tm_eval_step <{tt}> T ->
  T = <{tt}>.
Proof.
  intros. remember <{tt}> as S.
  generalize dependent HeqS.
  induction H; intros.
  - reflexivity.
  - subst T1. inversion H. subst T2. apply IHmulti. reflexivity.
Qed.

Lemma tmeq_sort_pi_absurd :
  forall s A B,
  <{ {TmSort s} }> === <{Pi A,B}> ->
  False.
Proof.
  intros. apply tmeq_implies_confluence in H as [U [H1 H2] ].
  apply tmeval_preserves_form_sort in H1.
  apply tmeval_preserves_form_pi in H2 as [A' [B' [HU _] ] ].
  subst U. discriminate HU.
Qed.

Lemma tmeq_unit_pi_absurd :
  forall A B,
  <{Unit}> === <{Pi A,B}> ->
  False.
Proof.
  intros. apply tmeq_implies_confluence in H as [U [H1 H2] ].
  apply tmeval_preserves_form_unit in H1.
  apply tmeval_preserves_form_pi in H2 as [A' [B' [HU _] ] ].
  subst U. discriminate HU.
Qed.

(* Inversion of Pi-typing (standard-form chasing through T_Conv) *)
Lemma invert_typing_pi :
  forall Gamma A B T,
  <[ Gamma |-- Pi A,B \in T ]> ->
  forall s,
  T === <{ {TmSort s} }> ->
  (exists s1, <[ Gamma |-- A \in {TmSort s1} ]>) /\ exists s2, <[ A :: Gamma |-- B \in {TmSort s2} ]>.
Proof.
  intros Gamma A B T H.
  remember <{ Pi A,B }> as t.
  generalize dependent Heqt.
  induction H; try discriminate; intros Heqt s0 Heq.
  - inversion Heqt; subst. split.
    + exists s1. assumption.
    + exists s2. assumption.
  - apply IHhas_type1 with (s:=s0).
    + assumption.
    + eapply tmeq_trans. split; eassumption.
Qed.

(* Context conversion: swapping a telescope entry for a convertible one *)
Lemma context_conv_cons :
  forall Gamma A A' sA,
  <[ Gamma |-- A \in {TmSort sA} ]> ->
  A === A' ->
  forall t B,
  <[ A :: Gamma |-- t \in B ]> ->
  <[ A' :: Gamma |-- t \in B ]>.
Proof.
  intros Gamma A A' sA HA Heq t B H.
  assert (Hgoal : <[ A' :: Gamma |-- {subst_Tm (fun n => TmVar n) t} \in
                      {subst_Tm (fun n => TmVar n) B} ]>).
  { eapply subst_typing.
    - eassumption.
    - intros x S Hx. rewrite instId'_Tm.
      inversion Hx; subst.
      + assert (Hwk : <[ A' :: Gamma |-- {ren_Tm S A} \in {ren_Tm S (TmSort sA)} ]>).
        { eapply ren_typing.
          - eassumption.
          - intros y T0 Hy. apply at_there. assumption. }
        simpl in Hwk.
        eapply T_Conv.
        * apply T_Var. apply at_here.
        * apply ren_tmeq. apply tmeq_sym. assumption.
        * exact Hwk.
      + apply T_Var. apply at_there. assumption. }
  rewrite instId'_Tm in Hgoal. rewrite instId'_Tm in Hgoal. assumption.
Qed.

(* TmAbs inversion *)
Lemma invert_typing_abs :
  forall Gamma S1 t1 T,
  <[ Gamma |-- \:S1, t1 \in T ]> ->
  forall T1 T2 s,
  T === <{Pi T1,T2}> ->
  <[ Gamma |-- Pi T1,T2 \in {TmSort s} ]> ->
  (S1 === T1) /\ (exists s1, <[ Gamma |-- S1 \in {TmSort s1} ]>) /\ <[ S1 :: Gamma |-- t1 \in T2 ]>.
Proof.
  intros Gamma S1 t1 T H.
  remember <{ \:S1, t1 }> as t.
  generalize dependent Heqt.
  induction H; try discriminate; intros Heqt T1 T2 s0 Heq Hpi.
  - apply invert_tmeq_pi in Heq as [Hl Hr].
    inversion Heqt; subst. repeat split.
    + assumption.
    + exists s1. assumption.
    + pose proof (invert_typing_pi Gamma T1 T2 (TmSort s0) Hpi s0
                    (multi_refl tm_eval_step_lr (TmSort s0)))
        as [ [s1' HT1k] [s2' HT2k] ].
      eapply T_Conv.
      * eassumption.
      * assumption.
      * eapply context_conv_cons.
        { apply HT1k. }
        { apply tmeq_sym. assumption. }
        { eassumption. }
  - apply IHhas_type1 with (s:=s0).
    + assumption.
    + eapply tmeq_trans. split; eassumption.
    + assumption.
Qed.

(* Regularity *)
Lemma regularity :
  forall Gamma t T,
  <[ Gamma |-- t \in T ]> ->
  wf Gamma ->
  <{T}> = <{box}> \/ exists s, <[ Gamma |-- T \in {TmSort s} ]>.
Proof.
  intros Gamma t T H.
  induction H; intros HW.
  - right. induction H; simpl in HW.
    + destruct HW as [HWG [s HA] ].
      exists s.
      assert (Hwk : <[ A :: Gamma |-- {ren_Tm S A} \in {ren_Tm S (TmSort s)} ]>).
      { eapply ren_typing.
        - eassumption.
        - intros y S0 Hy. apply at_there. assumption. }
      simpl in Hwk. assumption.
    + destruct HW as [HWG HA].
      destruct (IHat_tm HWG) as [s HS].
      exists s.
      assert (Hwk : <[ B :: Gamma |-- {ren_Tm S A} \in {ren_Tm S (TmSort s)} ]>).
      { eapply ren_typing.
        - eassumption.
        - intros y S0 Hy. apply at_there. assumption. }
      simpl in Hwk. assumption.
  - left. reflexivity.
  - destruct s2.
    + right. exists Box. apply T_Sort.
    + left. reflexivity.
  - right. eexists. eassumption.
  - right.
    apply IHhas_type1 in HW as [HWbox | [s' HWs'] ]; try discriminate.
    pose proof (invert_typing_pi Gamma A B (TmSort s') HWs' s'
                  (multi_refl tm_eval_step_lr (TmSort s')))
      as [HAk [s2' HBk] ].
    exists s2'. subst B'. unfold tm_tm_betared.
    assert (Heq : ren_Tm Nat.pred (subst_Tm (sigma_tm_one 0 (ren_Tm S t2)) B) =
                  subst_Tm (fun n => match n with 0 => t2 | S n' => TmVar n' end) B).
    { asolve. apply ext_Tm. intros x. destruct x; asolve. }
    rewrite Heq.
    change (TmSort s2') with
      (subst_Tm (fun n => match n with 0 => t2 | S n' => TmVar n' end) (TmSort s2')).
    eapply subst_typing.
    + eassumption.
    + intros x S0 Hx. inversion Hx; subst.
      * assert (Heq2 : subst_Tm (fun n => match n with
                                  | 0 => t2 | S n' => TmVar n' end) (ren_Tm S A) = A).
        { rewrite renSubst_Tm. apply idSubst_Tm. intros m. reflexivity. }
        rewrite Heq2. exact H0.
      * assert (Heq3 : subst_Tm (fun n => match n with
                                  | 0 => t2 | S n' => TmVar n' end) (ren_Tm S A0) = A0).
        { rewrite renSubst_Tm. apply idSubst_Tm. intros m. reflexivity. }
        rewrite Heq3. apply T_Var. assumption.
  - right. eexists. eassumption.
  - right. exists Box. apply T_Sort.
  - right. exists Star. apply T_Unit.
Qed.

(* General helper: substituting away a single bound variable *)
Lemma pop_subst_betared : forall C v,
  tm_tm_betared C v =
  subst_Tm (fun n => match n with 0 => v | S n' => TmVar n' end) C.
Proof.
  intros. unfold tm_tm_betared. asolve.
  apply ext_Tm. intros x. destruct x; asolve.
Qed.

Lemma pop_subst_typing : forall Gamma A' t T v,
  <[ A' :: Gamma |-- t \in T ]> ->
  <[ Gamma |-- v \in A' ]> ->
  <[ Gamma |-- {subst_Tm (fun n => match n with 0 => v | S n' => TmVar n' end) t}
     \in {subst_Tm (fun n => match n with 0 => v | S n' => TmVar n' end) T} ]>.
Proof.
  intros Gamma A' t T v Ht Hv.
  eapply subst_typing.
  - eassumption.
  - intros x S0 Hx. inversion Hx; subst.
    + assert (Heq : subst_Tm (fun n => match n with
                     0 => v | S n' => TmVar n' end) (ren_Tm S A') = A').
      { rewrite renSubst_Tm. apply idSubst_Tm. intros m. reflexivity. }
      rewrite Heq. assumption.
    + assert (Heq : subst_Tm (fun n => match n with
                     0 => v | S n' => TmVar n' end) (ren_Tm S A) = A).
      { rewrite renSubst_Tm. apply idSubst_Tm. intros m. reflexivity. }
      rewrite Heq. apply T_Var. assumption.
Qed.

(* Preservation *)
Lemma step_implies_tmeval : forall t t',
  t --> t' -> t ==> t'.
Proof.
  intros t t' H. induction H.
  - eapply TST_Red.
    + apply tmeval_refl.
    + apply tmeval_refl.
    + reflexivity.
  - apply TST_App.
    + assumption.
    + apply tmeval_refl.
  - apply TST_App.
    + apply tmeval_refl.
    + assumption.
Qed.

Theorem preservation :
  forall Gamma t T,
  <[ Gamma |-- t \in T ]> ->
  wf Gamma ->
  forall t',
  t --> t' ->
  <[ Gamma |-- t' \in T ]>.
Proof.
  intros Gamma t T H HW. induction H; intros t' Hstep.
  - inversion Hstep.
  - inversion Hstep.
  - inversion Hstep.
  - inversion Hstep.
  - inversion Hstep; subst.
    + destruct (regularity _ _ _ H HW) as [Hbox | [s HPiK] ];
      try discriminate.
      apply invert_typing_abs with (T1:=A) (T2:=B) (s:=s) in H
        as [HeqSA [ [s1'' HSk] Ht] ].
      * rewrite pop_subst_betared. rewrite pop_subst_betared.
        apply pop_subst_typing with (A':=A0).
        { exact Ht. }
        { eapply T_Conv.
          - exact H0.
          - apply tmeq_sym. exact HeqSA.
          - exact HSk. }
      * apply multi_refl.
      * assumption.
    + apply T_App with (A:=A) (B:=B).
      * apply IHhas_type1; assumption.
      * assumption.
      * reflexivity.
    + destruct (regularity _ _ _ H HW) as [Hbox | [s' HPiK] ]; try discriminate.
      pose proof (invert_typing_pi Gamma A B (TmSort s') HPiK s'
                    (multi_refl tm_eval_step_lr (TmSort s')))
        as [HAk [s2' HBk] ].
      eapply T_Conv with (s2:=s2').
      * apply T_App with (A:=A) (B:=B).
        { assumption. }
        { apply IHhas_type2; assumption. }
        { reflexivity. }
      * apply tmeq_sym. eapply multi_step.
        { left. apply tmtmbetared_tmeval_lemma.
          - apply tmeval_refl.
          - apply step_implies_tmeval. exact H6. }
        { apply multi_refl. }
      * rewrite pop_subst_betared.
        apply pop_subst_typing with (A':=A) (T:=TmSort s2'); assumption.
  - eapply T_Conv.
    + apply IHhas_type1; assumption.
    + assumption.
    + exact H1.
  - inversion Hstep.
  - inversion Hstep.
Qed.

(* Standard forms of typing, for progress *)
Lemma typing_pi_form :
  forall Gamma A B T,
  <[ Gamma |-- Pi A,B \in T ]> ->
  exists s, T === <{ {TmSort s} }>.
Proof.
  intros Gamma A B T H.
  remember <{ Pi A,B }> as t.
  generalize dependent Heqt.
  induction H; try discriminate; intros.
  - inversion Heqt; subst. exists s2. apply multi_refl.
  - apply IHhas_type1 in Heqt as [s' Ht]. exists s'.
    eapply tmeq_trans. split.
    + apply tmeq_sym. eassumption.
    + assumption.
Qed.

Lemma typing_abs_form :
  forall Gamma S1 t1 T,
  <[ Gamma |-- \:S1, t1 \in T ]> ->
  exists A B, T === <{ Pi A,B }>.
Proof.
  intros Gamma S1 t1 T H.
  remember <{ \:S1, t1 }> as t.
  generalize dependent Heqt.
  induction H; try discriminate; intros.
  - inversion Heqt; subst. exists S1, B. apply multi_refl.
  - apply IHhas_type1 in Heqt as [A' [B' Ht] ]. exists A', B'.
    eapply tmeq_trans. split.
    + apply tmeq_sym. eassumption.
    + assumption.
Qed.

Lemma typing_sort_form :
  forall Gamma s T,
  <[ Gamma |-- {TmSort s} \in T ]> ->
  T === <{box}>.
Proof.
  intros Gamma s T H.
  remember <{ {TmSort s} }> as t.
  generalize dependent Heqt.
  induction H; try discriminate; intros.
  - inversion Heqt; subst. apply multi_refl.
  - apply IHhas_type1 in Heqt.
    eapply tmeq_trans. split.
    + apply tmeq_sym. eassumption.
    + assumption.
Qed.

Lemma typing_unit_form :
  forall Gamma T,
  <[ Gamma |-- Unit \in T ]> ->
  exists s, T === <{ {TmSort s} }>.
Proof.
  intros Gamma T H.
  remember <{ Unit }> as t.
  generalize dependent Heqt.
  induction H; try discriminate; intros.
  - apply IHhas_type1 in Heqt as [s' Ht]. exists s'.
    eapply tmeq_trans. split.
    + apply tmeq_sym. eassumption.
    + assumption.
  - exists Star. apply multi_refl.
Qed.

Lemma typing_tt_form :
  forall Gamma T,
  <[ Gamma |-- tt \in T ]> ->
  T === <{Unit}>.
Proof.
  intros Gamma T H.
  remember <{ tt }> as t.
  generalize dependent Heqt.
  induction H; try discriminate; intros.
  - apply IHhas_type1 in Heqt.
    eapply tmeq_trans. split.
    + apply tmeq_sym. eassumption.
    + assumption.
  - apply multi_refl.
Qed.

(* Progress *)
Theorem progress :
  forall t T,
  <[ nil |-- t \in T ]> ->
  value t \/ exists t', t --> t'.
Proof.
  intros t T H.
  remember (@nil Tm) as Gamma.
  generalize dependent HeqGamma.
  induction H; intros HeqGamma.
  - subst Gamma. inversion H.
  - left. apply v_sort.
  - left. apply v_pi.
  - left. apply v_abs.
  - right. destruct (IHhas_type1 HeqGamma) as [Hv1 | [t1' Hs1] ].
    + destruct (IHhas_type2 HeqGamma) as [Hv2 | [t2' Hs2] ].
      * destruct Hv1.
        { apply typing_sort_form in H.
          apply tmeq_sym in H. apply tmeq_sort_pi_absurd in H. destruct H. }
        { apply typing_pi_form in H as [s' HT].
          apply tmeq_sym in HT. apply tmeq_sort_pi_absurd in HT. destruct HT. }
        { eexists. apply ST_AppAbs. assumption. }
        { apply typing_unit_form in H as [s' HT].
          apply tmeq_sym in HT. apply tmeq_sort_pi_absurd in HT. destruct HT. }
        { apply typing_tt_form in H.
          apply tmeq_sym in H. apply tmeq_unit_pi_absurd in H. destruct H. }
      * eexists. apply ST_App2; eassumption.
    + eexists. apply ST_App1. eassumption.
  - apply IHhas_type1. assumption.
  - left. apply v_unit.
  - left. apply v_tt.
Qed.
