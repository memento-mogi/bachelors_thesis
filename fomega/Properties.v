From Stdlib Require Import List.
From Fomega Require Export Definitions.

Ltac dauto := try (intros _x; destruct _x; auto).

(* Properties *)
(* Basic lemmas on type evaluation and equivalence *)
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

Definition tyeval_append := multi_append Ty type_eval_step.
Definition tyeq_append := multi_append Ty type_eval_step_lr.

Lemma tyeval_refl :
  forall T, T ==> T.
  induction T; constructor; assumption.
Qed.

Lemma tyeq_sym :
  forall S T, S === T -> T === S.
Proof.
  intros. induction H.
  - apply multi_refl.
  - apply tyeq_append with T2. split.
    + assumption.
    + destruct H; [right | left]; assumption.
Qed.

Lemma tyeq_trans :
  forall S T U, (S === U) /\ (U === T) -> S === T.
Proof.
  intros. destruct H as [HS HT].
  generalize dependent T. induction HS; intros U H1.
  - assumption.
  - apply multi_step with T2.
    + assumption.
    + apply IHHS. assumption.
Qed.

Lemma multi_step_implies_tyeq : 
  forall S T, multi type_eval_step S T -> S === T.
Proof.
  intros. induction H.
  - apply multi_refl.
  - apply multi_step with T2.
    + left. assumption.
    + apply IHmulti.
Qed.

(* Renaming *)
Lemma renTm_typing : forall Delta Gamma t T,
  <[ Delta | Gamma |-- t \in T ]> ->
  forall Gamma' xi,
  (forall x S, nth_error Gamma x = Some S -> 
              nth_error Gamma' (xi x) = Some S) ->
  <[ Delta | Gamma' |-- {ren_Tm id xi t} \in T ]> .
Proof.
  intros Delta Gamma t T H.
  induction H; intros; asolve.
  - apply T_Var. apply H0. assumption.
  - apply T_Abs; try assumption.
    apply IHhas_type. intros. destruct x.
    + simpl in *. assumption.
    + simpl in *. apply H1. assumption.
  - eapply T_App; eauto.
  - eapply T_TAbs; try reflexivity.
    subst GammaS.
    rewrite extRen_Tm with (zeta_Ty:=id) (zeta_Tm:=xi); dauto.
    apply IHhas_type. intros.
    rewrite nth_error_map in *.
    destruct (nth_error Gamma x) as [S'|] eqn: EqGx;
    try discriminate.
    rewrite H1 with (S:=S'); try assumption.
  - eapply T_TApp; try eauto.
  - eapply T_Conv; try eauto.
  - apply T_Unit.
Qed.

Lemma renTy_kinding : forall Delta T K,
  <[[ Delta |-- T \in K ]]> ->
  forall Delta' xi,
  (forall X J, nth_error Delta X = Some J -> 
              nth_error Delta' (xi X) = Some J) ->
  <[[ Delta' |-- {ren_Ty xi T} \in K ]]>. 
Proof.
  intros Delta T K H.
  induction H; intros; asolve;
  try (econstructor; auto).
  - apply IHhas_kind.
    intros. destruct X; simpl; auto.
  - apply IHhas_kind.
    intros. destruct X; simpl; auto.
Qed.

Lemma renTy_tyeval : forall T1 T2, 
  T1 ==> T2 -> 
  forall xi,
  (ren_Ty xi T1) ==> (ren_Ty xi T2).
Proof.
  intros T1 T2 H. induction H; intros; asolve;
  try (constructor;
       try apply IHtype_eval_step;
       try apply IHtype_eval_step1;
       try apply IHtype_eval_step2
    ).
  - subst S. asolve. eapply TST_Red.
    + eapply IHtype_eval_step1.
    + eapply IHtype_eval_step2.
    + asolve. apply ext_Ty. intros. destruct x; asolve.
Qed.

Lemma renTy_tyeq : forall T1 T2,
  T1 === T2 -> 
  forall xi,
  (ren_Ty xi T1) === (ren_Ty xi T2).
Proof.
  intros T1 T2 H. induction H; intros; asolve.
  - apply multi_refl.
  - apply multi_step with (T2:=ren_Ty xi T2).
    + destruct H; [left | right]; apply renTy_tyeval; assumption.
    + apply IHmulti.
Qed.
  
Lemma renTy_typing : forall Delta Gamma t T,
  <[ Delta | Gamma |-- t \in T ]> ->
  forall Gamma' Delta' xi,
  (forall x S, nth_error Gamma x = Some S -> 
              nth_error Gamma' x = Some (ren_Ty xi S)) ->
  (forall X K, nth_error Delta X = Some K -> 
              nth_error Delta' (xi X) = Some K) ->
  <[ Delta' | Gamma' |-- {ren_Tm xi id t} \in {ren_Ty xi T} ]>.
Proof.
  intros Delta Gamma t T H.
  induction H; intros Gamma' Delta' xi HG HD; asolve.
  - apply T_Var. apply HG. assumption.
  - eapply T_Abs.
    + eapply renTy_kinding; eassumption.
    + erewrite extRen_Tm.
      * apply IHhas_type. 
        { intros. destruct x; simpl; simpl in H1.
          - inversion H1. reflexivity.
          - apply HG. assumption. }
        { intros. apply HD. assumption. }
      * reflexivity.
      * intros. destruct x; auto.
  - eapply T_App; eauto.
  - eapply T_TAbs; try reflexivity.
    subst GammaS. apply IHhas_type. 
    + intros. rewrite nth_error_map in *.
      destruct (nth_error Gamma x) as [S'|] eqn: EqGx;
      try discriminate. simpl in H0. inversion H0.
      rewrite HG with (S:=S'); try assumption.
      asolve. 
    + intros. destruct X; auto.
      simpl in *. auto.
  - simpl in IHhas_type.
    eapply T_TApp with (K:=K);
    unfold sigma_ty_one in *; subst T1';
    try apply IHhas_type.
    + asolve.
    + auto.
    + asolve. apply ext_Ty. intros. destruct x; asolve.
    + eapply renTy_kinding; eassumption.
  - eapply T_Conv.
    + apply IHhas_type; assumption.
    + apply renTy_tyeq. assumption.
    + eapply renTy_kinding; eassumption.
  - apply T_Unit.
Qed.

(* substitution *)
Lemma tmsubst_preserves_typing :
  forall Delta Gamma t T,
  <[ Delta | Gamma |-- t \in T ]> ->
  forall Gamma' sigma,
  (forall x S, nth_error Gamma x = Some S -> <[ Delta | Gamma' |-- {sigma x} \in S ]>) ->
  <[ Delta | Gamma' |-- {subst_Tm id sigma t} \in T ]>.
Proof.
  intros Delta Gamma t T.
  intro H. induction H; intros; asolve.
  - apply T_Abs; try assumption.
    apply IHhas_type. intros. destruct x.
    + apply T_Var. assumption.
    + apply renTm_typing with (Gamma').
      * simpl in H2. apply H1. assumption.
      * intros. simpl. assumption. 
  - apply T_App with (T1:=T1).
    + apply IHhas_type1; assumption.
    + apply IHhas_type2; assumption.
  - eapply T_TAbs; try reflexivity.
    erewrite ext_Tm with (tau_Ty:=id); try reflexivity; dauto.
    apply IHhas_type. intros.
    subst GammaS. rewrite nth_error_map in H2.
    destruct (nth_error Gamma x) as [S'|] eqn: EqGx; try discriminate.
    simpl in H2. inversion H2. eapply renTy_typing.
    + apply H1. assumption.
    + intros. rewrite nth_error_map. rewrite H0. reflexivity.
    + intros. simpl. assumption.
  - eapply T_TApp; try eassumption.
    apply IHhas_type. assumption.
  - eapply T_Conv; try eassumption.
    apply IHhas_type. assumption.
  - constructor.
Qed.

Lemma tysubst_preserves_kinding : 
  forall Delta T K,
  <[[ Delta |-- T \in K ]]> ->
  forall sigma Delta',
  ( forall X J, nth_error Delta X = Some J ->
    <[[ Delta' |-- {sigma X} \in J ]]> ) ->
  <[[ Delta' |-- {subst_Ty sigma T} \in K ]]>. 
Proof.
  intros Delta T K H.
  induction H; intros; asolve.
  - apply K_Abs. apply IHhas_kind. intros.
    destruct X.
    + apply K_TVar. assumption.
    + apply renTy_kinding with Delta'.
      * apply H0. assumption.
      * intros. assumption.
  - apply K_App with K2.
    + apply IHhas_kind1. assumption.
    + apply IHhas_kind2. assumption.
  - apply K_Arr.
    + apply IHhas_kind1. assumption.
    + apply IHhas_kind2. assumption.
  - apply K_All. apply IHhas_kind.
    intros. destruct X.
    + apply K_TVar. assumption.
    + apply renTy_kinding with Delta'.
      * apply H0. assumption.
      * intros. assumption.
  - apply K_Unit.
Qed.

Lemma tysubst_preserves_tyeval : 
  forall T1 T2,
  T1 ==> T2 ->
  forall sigma,
  (subst_Ty sigma T1) ==> (subst_Ty sigma T2).
Proof.
  intros T1 T2 H. induction H; intros; asolve;
  try (constructor;
       try apply IHtype_eval_step;
       try apply IHtype_eval_step1;
       try apply IHtype_eval_step2
    ).
  - apply tyeval_refl.
  - subst S. asolve. eapply TST_Red.
    + eapply IHtype_eval_step1.
    + eapply IHtype_eval_step2.
    + asolve. apply ext_Ty. intros. destruct x; asolve.
      * apply ext_Ty. intros x. rewrite renRen_Ty. asolve.
      * asolve.
Qed.

Lemma tysubst_preserves_tyeq : 
  forall T1 T2,
  T1 === T2 ->
  forall sigma,
  (subst_Ty sigma T1) === (subst_Ty sigma T2).
Proof.
  intros T1 T2 H. induction H; intros.
  - apply multi_refl.
  - apply multi_step with (T2:=subst_Ty sigma T2).
    + destruct H; [left|right]; apply tysubst_preserves_tyeval;
      assumption.
    + apply IHmulti.
Qed.

Lemma tysubst_preserves_typing :
  forall Delta Gamma t T, 
  <[ Delta | Gamma |-- t \in T ]> ->
  forall sigma Gamma',
  ( forall x U, nth_error Gamma x = Some U ->
    nth_error Gamma' x = Some (subst_Ty sigma U) ) ->
  forall Delta',
  ( forall X K, nth_error Delta X = Some K ->
    <[[ Delta' |-- {sigma X} \in K ]]> ) ->
  <[ Delta' | Gamma' |-- {subst_Tm sigma id t} \in {subst_Ty sigma T} ]>.
Proof.
  intros Delta Gamma t T H.
  induction H; intros sigma Gamma' HG Delta' HD; asolve.
  - apply T_Var. apply HG. apply H.
  - apply T_Abs.
    + apply tysubst_preserves_kinding with Delta; assumption.
    + asimpl. rewrite ext_Tm with (tau_Ty:=sigma) (tau_Tm:=id).
      * apply IHhas_type.
        { intros. destruct x.
          - simpl. inversion H1. reflexivity.
          - simpl. simpl in H1. apply HG. assumption. }
        { assumption. }
      * reflexivity.
      * intro x. destruct x; auto.
  - apply T_App with (subst_Ty sigma T1).
    + apply IHhas_type1; assumption.
    + apply IHhas_type2; assumption.
  - apply T_TAbs with (map (ren_Ty S) Gamma'); try reflexivity.
    subst GammaS. apply IHhas_type.
    + intros. rewrite nth_error_map in *.
      destruct (nth_error Gamma x) as [U'|] eqn: EqGx; try discriminate.
      simpl in H0. rewrite (HG x U' EqGx). simpl. f_equal.
      inversion H0. asolve.
    + intros. destruct X.
      * apply K_TVar. assumption.
      * apply renTy_kinding with Delta'.
        { apply HD. assumption. }
        { intros. assumption. }
  - apply T_TApp with (K:=K) (T1:=(subst_Ty (up_Ty_Ty sigma) T1)).
    + apply IHhas_type.
      * intros. apply HG. assumption.
      * assumption.
    + subst T1'. asolve. apply ext_Ty. intros.
      destruct x; asolve.
      symmetry. apply idSubst_Ty. reflexivity.
    + apply tysubst_preserves_kinding with Delta; assumption.
  - eapply T_Conv.
    + apply IHhas_type; assumption.
    + apply tysubst_preserves_tyeq. assumption.
    + apply tysubst_preserves_kinding with Delta; assumption.
  - apply T_Unit.
Qed.

Lemma tysubst_tyeval_lemma :
  forall T T',
  T ==> T' ->
  forall sigma sigma',
  (forall n, (sigma n) ==> (sigma' n)) ->
  subst_Ty sigma T ==> subst_Ty sigma' T'.
Proof.
  intros T T' H. induction H; intros; asolve.
  - constructor.
  - constructor. apply IHtype_eval_step. intros. destruct n.
    + constructor.
    + apply renTy_tyeval. apply H0.
  - constructor; [apply IHtype_eval_step1 | apply IHtype_eval_step2]; assumption.
  - eapply TST_Red with (S1:=(subst_Ty (
                                fun n : nat => match n with
                                  | 0 => 0
                                  | Datatypes.S n' => ren_Ty Datatypes.S (sigma' n')
                                end
                              ) S1)).
    + eapply IHtype_eval_step1. intros. destruct n.
      * constructor.
      * apply renTy_tyeval. apply H2.
    + apply IHtype_eval_step2. eassumption.
    + subst S. asolve. apply ext_Ty. intros. destruct x;  asolve.
      * apply ext_Ty. intros. rewrite renRen_Ty. asolve.
      * symmetry. apply idSubst_Ty. reflexivity.
  - constructor; [apply IHtype_eval_step1 | apply IHtype_eval_step2]; assumption.
  - constructor. apply IHtype_eval_step. intros. destruct n.
    + constructor.
    + apply renTy_tyeval. apply H0.
Qed.

(* Regularity *)
Lemma regularity :
  forall Delta Gamma t T,
  <[ Delta | Gamma |-- t \in T ]> ->
  wf Delta Gamma ->
  <[[ Delta |-- T \in * ]]>.
Proof.
  intros Delta Gamma t T H.
  induction H; intros HW.
  - apply HW with x. assumption.
  - apply K_Arr.
    + assumption.
    + apply IHhas_type. intros x U HU. destruct x.
      * simpl in HU. inversion HU. subst. assumption.
      * simpl in HU. apply HW with x. assumption.
  - apply IHhas_type1 in HW. inversion HW. assumption.
  - apply K_All. apply IHhas_type. intros x U HU.
    subst GammaS. rewrite nth_error_map in HU.
    destruct (nth_error Gamma x) as [V|] eqn: EqGx; try discriminate.
    simpl in HU. inversion HU. apply renTy_kinding with Delta.
    + apply HW with x. assumption.
    + intros. simpl. assumption.
  - apply IHhas_type in HW. inversion HW. subst T1'.
    unfold ty_ty_betared. asolve. unfold sigma_ty_one.
    apply tysubst_preserves_kinding with (K::Delta).
    + assumption.
    + intros X J HJ. destruct X; simpl.
      * rewrite renRen_Ty. asolve. simpl in HJ. inversion HJ. subst.
        assumption.
      * apply K_TVar. assumption.
  - assumption.
  - apply K_Unit.
Qed.

(* Confluence *)
Lemma tytybetared_tyeval_lemma :
  forall S1 S2 T1 T2,
    (S1 ==> T1) ->
    (S2 ==> T2) ->
    ty_ty_betared S1 S2 ==> ty_ty_betared T1 T2.
Proof.
  intros. unfold ty_ty_betared.
  apply renTy_tyeval. apply tysubst_tyeval_lemma.
  - assumption.
  - intros. destruct n; unfold sigma_ty_one; asolve.
    + apply renTy_tyeval. assumption.
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
  - inversion HU. apply IHHT in H2 as [V' [IHT IHU ] ].
    eexists. split; constructor; eassumption.
  - inversion HU.
    + apply IHHT1 in H1 as [V1 [IH11 IH12] ].
      apply IHHT2 in H3 as [V2 [IH21 IH22] ].
      eexists. split; apply TST_App; eassumption.
    + subst U.
      rename S into U, S0 into U11, S3 into U2, T0 into T11.
      assert (HT1': T1 ==> <{{ \:: K, U11 }}>); subst T1.
      { constructor. assumption. }
      inversion HT1. rename S0 into S11. subst S1.
      apply IHHT1 in HT1' as [V1 [IH11 IH12] ].
      apply IHHT2 in H2 as [V2 [IH21 IH22] ].
      inversion IH11. rename S1 into V11. subst V1.
      exists (ty_ty_betared V11 V2). split.
      * eapply TST_Red; try eassumption. reflexivity.
      * inversion IH12.
        apply tytybetared_tyeval_lemma; assumption.
  - inversion HU.
    + subst S.
      rename S0 into U1, S3 into U2, T1 into T11, S1 into S11.
      inversion H2. rename S1 into U11. subst U1.
      apply IHHT1 in H7 as [V11 [IH11 IH12] ].
      apply IHHT2 in H4 as [V2 [IH21 IH22] ].
      exists (ty_ty_betared V11 V2). split.
      * apply tytybetared_tyeval_lemma; assumption.
      * eapply TST_Red; try eassumption. reflexivity.
    + rename S0 into U1, S3 into U2.
      apply IHHT1 in H3 as [V1 [IH11 IH12] ].
      apply IHHT2 in H5 as [V2 [IH21 IH22] ].
      exists (ty_ty_betared V1 V2). split.
      * subst S. apply tytybetared_tyeval_lemma; assumption.
      * subst U. apply tytybetared_tyeval_lemma; assumption.
  - inversion HU.
    apply IHHT1 in H1 as [V1 [IH11 IH12] ].
    apply IHHT2 in H3 as [V2 [IH21 IH22] ].
    eexists. split; apply TST_Arr; eassumption.
  - inversion HU.
    apply IHHT in H2 as [V [IH1 IH2] ].
    eexists. split; apply TST_All; eassumption.  
Qed.    

Lemma confluence_multi_single : 
  forall S T U,
  multi type_eval_step S T /\ (S ==> U) ->
  exists V, (T ==> V) /\ multi type_eval_step U V.
Proof.                                
  intros. destruct H as [HT HU].
  generalize dependent U. induction HT; intros.
  - exists U. split.
    + assumption.
    + constructor.
  - assert (HV': exists V', (T2==>V') /\ (U==>V')) .
    + eapply confluence_single; split; eassumption.
    + destruct HV' as [V' [HV'1 HV'2] ].
      apply IHHT in HV'1 as [V0 [HV'11 HV'12 ] ].
      exists V0. split.
      * assumption.
      * econstructor; eassumption.
Qed.

Lemma confluence_multi : 
  forall S T U,
    multi type_eval_step S T /\ multi type_eval_step S U ->
    exists V, multi type_eval_step T V /\ multi type_eval_step U V.
  
Proof.
  intros. destruct H as [HT HU].
  generalize dependent U. induction HT; intros.
  - exists U. split. + assumption. + constructor.
  - assert (HV': exists V', ((U ==> V') /\ multi type_eval_step T2 V')).
    + apply confluence_multi_single with T1. split; assumption.
    + destruct HV' as [V' [HV'1 HV'2] ].
      apply IHHT in HV'2 as [V0 [HV'11 HV'12 ] ].
      exists V0. split.
      * assumption.
      * econstructor; eassumption.
Qed.

Lemma tyeq_implies_confluence :
  forall S T,
    (S === T) ->
    exists U, multi type_eval_step S U /\ multi type_eval_step T U.
Proof.
  intros. induction H.
  - exists T. split; constructor.
  - destruct IHmulti as [U' [IH2 IH3] ].
    destruct H.
    + exists U'. split.
      * econstructor; eassumption.
      * assumption.
    + assert (exists V, (U' ==> V) /\ multi type_eval_step T1 V).
      * apply confluence_multi_single with T2. split; assumption.
      * destruct H1 as [V [HU HT3] ]. exists V. split; try assumption.
        eapply tyeval_append. split; eassumption.
Qed.
  
(* TmAbs invesion *)
Lemma tyeval_preserves_type_form_fun :
  forall S1 S2 T, 
  multi type_eval_step <{{S1 -> S2}}> T ->
  exists T1 T2,
  T = <{{T1 -> T2}}> /\ (multi type_eval_step S1 T1) /\ (multi type_eval_step S2 T2).
Proof.
  intros. remember <{{S1 -> S2}}> as S.
  generalize dependent HeqS. generalize dependent S2. generalize dependent S1.
  induction H; intros.
  - exists S1, S2; repeat split; try assumption; apply multi_refl.
  - rename T1 into S, T2 into U, T3 into T.
    subst S. inversion H.
    + rename S0 into U1. symmetry in H4. subst T1 T2.
      apply IHmulti in H4 as [T1 [T2 [HT [H1 H2] ] ] ].
      exists T1, T2. repeat split; try assumption.
      * apply multi_step with U1; assumption. 
      * apply multi_step with S3; assumption.
Qed.

Lemma invert_tyeq_fun : 
  forall S1 S2 T1 T2, 
  <{{S1 -> S2}}> === <{{T1 -> T2}}> ->
  (S1 === T1) /\ (S2 === T2).
Proof.
  intros. apply tyeq_implies_confluence in H as [U [H1 H2] ]. 
  apply tyeval_preserves_type_form_fun in H1 as [U1 [U2 [HU [H11 H12] ] ] ].
  apply tyeval_preserves_type_form_fun in H2 as [V1 [V2 [HV [H21 H22] ] ] ].
  subst U. inversion HV. subst V1 V2. clear HV. split;
  eapply tyeq_trans; split; [ | apply tyeq_sym | | apply tyeq_sym ];
  apply multi_step_implies_tyeq; eassumption.
Qed.


Lemma invert_typing_abs :
  forall Delta Gamma S1 t1 T,
  <[ Delta | Gamma |-- \:S1, t1 \in T ]> ->
  forall T1 T2,
  T === <{{ T1 -> T2 }}> ->
  <[[ Delta |-- T1 -> T2 \in * ]]> ->
  (S1 === T1) /\ <[[ Delta |-- S1 \in * ]]> /\ <[ Delta | S1 :: Gamma |-- t1 \in T2 ]>.
Proof.
  intros Delta Gamma S1 t1 T H.
  remember <{ \:S1, t1 }> as t.
  generalize dependent Heqt.
  induction H; try discriminate; intros.
  - apply invert_tyeq_fun in H1 as [Hl Hr].
    inversion Heqt. subst. repeat split.
    + assumption.
    + assumption.
    + inversion H2. subst. eapply T_Conv; eassumption.
  - apply IHhas_type.
    + assumption.
    + eapply tyeq_trans. split; eassumption.
    + assumption.
Qed.

(* TmTAbs inversion *)
Lemma tyeval_preserves_type_form_all :
  forall K S1 T,
  multi type_eval_step <{{ -/::K, S1 }}> T ->
  exists T1,
  T = <{{ -/::K, T1 }}> /\ (multi type_eval_step S1 T1).
Proof.
  intros. remember <{{ -/::K, S1 }}> as S.
  generalize dependent HeqS. generalize dependent S1.
  induction H; intros.
  - exists S1. repeat split; try assumption; apply multi_refl.
  - rename T1 into S, T2 into U, T3 into T.
    subst S. inversion H; subst.
    destruct (IHmulti S0 eq_refl) as [T1 [HT Hm] ].
    exists T1. split; try assumption.
    apply multi_step with S0; assumption.
Qed.

Lemma invert_tyeq_all :
  forall K J S T,
  <{{ -/::K , S }}> === <{{ -/::J, T }}> ->
  K = J /\ (S === T).
Proof.
  intros. apply tyeq_implies_confluence in H as [U [H1 H2] ].
  apply tyeval_preserves_type_form_all in H1 as [U1 [HU H1'] ].
  apply tyeval_preserves_type_form_all in H2 as [V1 [HV H2'] ].
  subst U. inversion HV. subst V1 J. clear HV. split.
  - reflexivity.
  - eapply tyeq_trans. split; [ | apply tyeq_sym ];
    apply multi_step_implies_tyeq; eassumption.
Qed.

Lemma invert_typing_tyabs :   
  forall Delta Gamma J t1 T,
  <[ Delta | Gamma |-- \::J, t1 \in T ]> ->
  forall K T1,
  T === <{{ -/::K, T1 }}> ->
  <[[ Delta |-- -/::K, T1 \in * ]]> ->
  K = J /\ <[ J :: Delta | map (ren_Ty S) Gamma |-- t1 \in T1 ]>.
Proof.
  intros Delta Gamma J t1 T H.
  remember <{ \::J, t1 }> as t.
  generalize dependent Heqt.
  induction H; try discriminate; intros.
  - inversion Heqt. apply invert_tyeq_all in H1 as [HK HT].
    subst. split.
    + reflexivity.
    + inversion H2. subst. eapply T_Conv; eassumption.
  - apply IHhas_type.
    + assumption.
    + eapply tyeq_trans. split; eassumption.
    + assumption.
Qed.

(* Preservation *)
Theorem preservation :
  forall Delta Gamma t T,
  <[ Delta | Gamma |-- t \in T ]> ->
  wf Delta Gamma ->
  forall t',
  t --> t' ->
  <[ Delta | Gamma |-- t' \in T ]>.
Proof.
  intros Delta Gamma t T H HW. induction H; intros.
  - inversion H0.
  - inversion H1.
  - inversion H1.
    + asolve. unfold sigma_tm_one. subst t1.
      apply invert_typing_abs with (T1:=T1) (T2:=T2) in H as [HT1 [HK Ht] ].
      * apply tmsubst_preserves_typing with (Gamma:=(T::Gamma)).
        { apply Ht. }
        { intros. destruct x; simpl.
          - rewrite renRen_Tm. asolve.
            simpl in H. inversion H. subst S. 
            eapply T_Conv.
            + eassumption.
            + apply tyeq_sym; assumption.
            + assumption.
          - apply T_Var. assumption. }
      * apply multi_refl.
      * eapply regularity; eassumption.
    + apply T_App with T1.
      * apply IHhas_type1; assumption.
      * assumption.
    + apply T_App with T1.
      * assumption.
      * apply IHhas_type2; assumption.
  - inversion H1.
  - inversion H2.
    + subst. asolve. unfold sigma_ty_one.
      apply invert_typing_tyabs with (K:=K) (T1:=T1) in H as [HK Ht].
      * eapply tysubst_preserves_typing.
        { apply Ht. }
        { intros. rewrite nth_error_map in H.
          destruct (nth_error Gamma x) as [V|]; try discriminate.
          simpl in H. inversion H.
          f_equal. asolve. rewrite idSubst_Ty; try reflexivity. }
        { intros. destruct X; simpl. 
          - rewrite renRen_Ty. asolve. simpl in H. inversion H. subst.
            assumption. 
          - apply K_TVar. assumption. }
      * apply multi_refl.
      * eapply regularity; eassumption.
    + eapply T_TApp; try eassumption.
      * apply IHhas_type; assumption.
  - eapply T_Conv.
    + apply IHhas_type; assumption.
    + assumption.
    + assumption.
  - inversion H.
Qed. 

(* Progress *)
Lemma tyeval_preserves_type_form_unit :
  forall T,
  multi type_eval_step <{{Unit}}> T ->
  T = <{{Unit}}>.
Proof.
  intros. remember <{{Unit}}> as S.
  generalize dependent HeqS.
  induction H; intros.
  - reflexivity.
  - subst T1. inversion H. subst T2. apply IHmulti. reflexivity.
Qed.

Lemma tyeq_fun_unit_absurd :
  forall S1 S2,
  <{{S1 -> S2}}> === <{{Unit}}> ->
  False.
Proof.
  intros. apply tyeq_implies_confluence in H as [U [H1 H2] ].
  apply tyeval_preserves_type_form_fun in H1 as [U1 [U2 [HU [H11 H12] ] ] ].
  apply tyeval_preserves_type_form_unit in H2.
  subst U. discriminate H2.
Qed.

Lemma tyeq_all_unit_absurd :
  forall K S1,
  <{{-/::K, S1}}> === <{{Unit}}> ->
  False.
Proof.
  intros. apply tyeq_implies_confluence in H as [U [H1 H2] ].
  apply tyeval_preserves_type_form_all in H1 as [U1 [HU H1'] ].
  apply tyeval_preserves_type_form_unit in H2.
  subst U. discriminate H2.
Qed.

Lemma tyeq_fun_all_absurd :
  forall S1 S2 K T1,
  <{{S1 -> S2}}> === <{{-/::K, T1}}> ->
  False.
Proof.
  intros. apply tyeq_implies_confluence in H as [U [H1 H2] ].
  apply tyeval_preserves_type_form_fun in H1 as [U1 [U2 [HU [H11 H12] ] ] ].
  apply tyeval_preserves_type_form_all in H2 as [V1 [HV H2'] ].
  subst U. discriminate HV.
Qed.

Lemma typing_abs_form :
  forall Delta Gamma S1 t1 T,
  <[ Delta | Gamma |-- \:S1, t1 \in T ]> ->
  exists T2, T === <{{S1 -> T2}}>.
Proof.
  intros Delta Gamma S1 t1 T H.
  remember <{ \:S1, t1 }> as t.
  generalize dependent Heqt.
  induction H; try discriminate; intros.
  - inversion Heqt. subst. exists T2. apply multi_refl.
  - apply IHhas_type in Heqt as [T3 HT].
    exists T3. eapply tyeq_trans. split.
    + apply tyeq_sym. eassumption.
    + assumption.
Qed.

Lemma typing_tyabs_form :
  forall Delta Gamma J t1 T,
  <[ Delta | Gamma |-- \::J, t1 \in T ]> ->
  exists T1, T === <{{-/::J, T1}}>.
Proof.
  intros Delta Gamma J t1 T H.
  remember <{ \::J, t1 }> as t.
  generalize dependent Heqt.
  induction H; try discriminate; intros.
  - inversion Heqt. subst. exists T1. apply multi_refl.
  - apply IHhas_type in Heqt as [T3 HT].
    exists T3. eapply tyeq_trans. split.
    + apply tyeq_sym. eassumption.
    + assumption.
Qed.

Lemma typing_unit_form :
  forall Delta Gamma T,
  <[ Delta | Gamma |-- unit \in T ]> ->
  T === <{{Unit}}>.
Proof.
  intros Delta Gamma T H.
  remember <{ unit }> as t.
  generalize dependent Heqt.
  induction H; try discriminate; intros.
  - eapply tyeq_trans. split.
    + apply tyeq_sym. eassumption.
    + apply IHhas_type. assumption.
  - apply multi_refl.
Qed.

Theorem progress :
  forall Delta t T,
  <[ Delta | nil |-- t \in T ]> ->
  value t \/ exists t', t --> t'.
Proof.
  intros Delta t T H.
  remember (@nil Ty) as Gamma.
  generalize dependent HeqGamma.
  induction H; intros.
  - subst Gamma. destruct x; discriminate.
  - left. apply v_abs.
  - right. destruct (IHhas_type1 HeqGamma) as [Hv1 | [t1' Hs1] ].
    + destruct (IHhas_type2 HeqGamma) as [Hv2 | [t2' Hs2] ].
      * destruct Hv1.
        { eexists. apply ST_AppAbs. assumption. }
        { apply typing_tyabs_form in H as [T3 HT].
          apply tyeq_fun_all_absurd in HT. destruct HT. }
        { apply typing_unit_form in H.
          apply tyeq_fun_unit_absurd in H. destruct H. }
      * eexists. apply ST_App2; eassumption.
    + eexists. apply ST_App1. eassumption.
  - left. apply v_tyabs.
  - right. destruct (IHhas_type HeqGamma) as [Hv1 | [t1' Hs1] ].
    + destruct Hv1.
      * apply typing_abs_form in H as [T3 HT].
        apply tyeq_sym in HT. apply tyeq_fun_all_absurd in HT. destruct HT.
      * eexists. apply ST_TAppAbs.
      * apply typing_unit_form in H.
        apply tyeq_all_unit_absurd in H. destruct H.
    + eexists. apply ST_TApp. eassumption.
  - apply IHhas_type. assumption.
  - left. apply v_unit.
Qed.
