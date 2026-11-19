Require Import core unscoped.

Require Import Setoid Morphisms Relation_Definitions.


Module Core.

Inductive Ty : Type :=
  | TyVar : nat -> Ty
  | TyPi : Ty -> Ty -> Ty
  | TyTmApp : Ty -> Tm -> Ty
  | TyUnit : Ty
with Tm : Type :=
  | TmVar : nat -> Tm
  | TmAbs : Ty -> Tm -> Tm
  | TmApp : Tm -> Tm -> Tm
  | TmUnit : Tm.

Lemma congr_TyVar {s0 : nat} {t0 : nat} (H0 : s0 = t0) : TyVar s0 = TyVar t0.
Proof.
exact (eq_trans eq_refl (ap (fun x => TyVar x) H0)).
Qed.

Lemma congr_TyPi {s0 : Ty} {s1 : Ty} {t0 : Ty} {t1 : Ty} (H0 : s0 = t0)
  (H1 : s1 = t1) : TyPi s0 s1 = TyPi t0 t1.
Proof.
exact (eq_trans (eq_trans eq_refl (ap (fun x => TyPi x s1) H0))
         (ap (fun x => TyPi t0 x) H1)).
Qed.

Lemma congr_TyTmApp {s0 : Ty} {s1 : Tm} {t0 : Ty} {t1 : Tm} (H0 : s0 = t0)
  (H1 : s1 = t1) : TyTmApp s0 s1 = TyTmApp t0 t1.
Proof.
exact (eq_trans (eq_trans eq_refl (ap (fun x => TyTmApp x s1) H0))
         (ap (fun x => TyTmApp t0 x) H1)).
Qed.

Lemma congr_TyUnit : TyUnit = TyUnit.
Proof.
exact (eq_refl).
Qed.

Lemma congr_TmAbs {s0 : Ty} {s1 : Tm} {t0 : Ty} {t1 : Tm} (H0 : s0 = t0)
  (H1 : s1 = t1) : TmAbs s0 s1 = TmAbs t0 t1.
Proof.
exact (eq_trans (eq_trans eq_refl (ap (fun x => TmAbs x s1) H0))
         (ap (fun x => TmAbs t0 x) H1)).
Qed.

Lemma congr_TmApp {s0 : Tm} {s1 : Tm} {t0 : Tm} {t1 : Tm} (H0 : s0 = t0)
  (H1 : s1 = t1) : TmApp s0 s1 = TmApp t0 t1.
Proof.
exact (eq_trans (eq_trans eq_refl (ap (fun x => TmApp x s1) H0))
         (ap (fun x => TmApp t0 x) H1)).
Qed.

Lemma congr_TmUnit : TmUnit = TmUnit.
Proof.
exact (eq_refl).
Qed.

Lemma upRen_Tm_Tm (xi : nat -> nat) : nat -> nat.
Proof.
exact (up_ren xi).
Defined.

Fixpoint ren_Ty (xi_Tm : nat -> nat) (s : Ty) {struct s} : Ty :=
  match s with
  | TyVar s0 => TyVar s0
  | TyPi s0 s1 => TyPi (ren_Ty xi_Tm s0) (ren_Ty (upRen_Tm_Tm xi_Tm) s1)
  | TyTmApp s0 s1 => TyTmApp (ren_Ty xi_Tm s0) (ren_Tm xi_Tm s1)
  | TyUnit => TyUnit
  end
with ren_Tm (xi_Tm : nat -> nat) (s : Tm) {struct s} : Tm :=
  match s with
  | TmVar s0 => TmVar (xi_Tm s0)
  | TmAbs s0 s1 => TmAbs (ren_Ty xi_Tm s0) (ren_Tm (upRen_Tm_Tm xi_Tm) s1)
  | TmApp s0 s1 => TmApp (ren_Tm xi_Tm s0) (ren_Tm xi_Tm s1)
  | TmUnit => TmUnit
  end.

Lemma up_Tm_Tm (sigma : nat -> Tm) : nat -> Tm.
Proof.
exact (scons (TmVar var_zero) (funcomp (ren_Tm shift) sigma)).
Defined.

Fixpoint subst_Ty (sigma_Tm : nat -> Tm) (s : Ty) {struct s} : Ty :=
  match s with
  | TyVar s0 => TyVar s0
  | TyPi s0 s1 =>
      TyPi (subst_Ty sigma_Tm s0) (subst_Ty (up_Tm_Tm sigma_Tm) s1)
  | TyTmApp s0 s1 => TyTmApp (subst_Ty sigma_Tm s0) (subst_Tm sigma_Tm s1)
  | TyUnit => TyUnit
  end
with subst_Tm (sigma_Tm : nat -> Tm) (s : Tm) {struct s} : Tm :=
  match s with
  | TmVar s0 => sigma_Tm s0
  | TmAbs s0 s1 =>
      TmAbs (subst_Ty sigma_Tm s0) (subst_Tm (up_Tm_Tm sigma_Tm) s1)
  | TmApp s0 s1 => TmApp (subst_Tm sigma_Tm s0) (subst_Tm sigma_Tm s1)
  | TmUnit => TmUnit
  end.

Lemma upId_Tm_Tm (sigma : nat -> Tm) (Eq : forall x, sigma x = TmVar x) :
  forall x, up_Tm_Tm sigma x = TmVar x.
Proof.
exact (fun n =>
       match n with
       | S n' => ap (ren_Tm shift) (Eq n')
       | O => eq_refl
       end).
Qed.

Fixpoint idSubst_Ty (sigma_Tm : nat -> Tm)
(Eq_Tm : forall x, sigma_Tm x = TmVar x) (s : Ty) {struct s} :
subst_Ty sigma_Tm s = s :=
  match s with
  | TyVar s0 => congr_TyVar (eq_refl s0)
  | TyPi s0 s1 =>
      congr_TyPi (idSubst_Ty sigma_Tm Eq_Tm s0)
        (idSubst_Ty (up_Tm_Tm sigma_Tm) (upId_Tm_Tm _ Eq_Tm) s1)
  | TyTmApp s0 s1 =>
      congr_TyTmApp (idSubst_Ty sigma_Tm Eq_Tm s0)
        (idSubst_Tm sigma_Tm Eq_Tm s1)
  | TyUnit => congr_TyUnit
  end
with idSubst_Tm (sigma_Tm : nat -> Tm)
(Eq_Tm : forall x, sigma_Tm x = TmVar x) (s : Tm) {struct s} :
subst_Tm sigma_Tm s = s :=
  match s with
  | TmVar s0 => Eq_Tm s0
  | TmAbs s0 s1 =>
      congr_TmAbs (idSubst_Ty sigma_Tm Eq_Tm s0)
        (idSubst_Tm (up_Tm_Tm sigma_Tm) (upId_Tm_Tm _ Eq_Tm) s1)
  | TmApp s0 s1 =>
      congr_TmApp (idSubst_Tm sigma_Tm Eq_Tm s0)
        (idSubst_Tm sigma_Tm Eq_Tm s1)
  | TmUnit => congr_TmUnit
  end.

Lemma upExtRen_Tm_Tm (xi : nat -> nat) (zeta : nat -> nat)
  (Eq : forall x, xi x = zeta x) :
  forall x, upRen_Tm_Tm xi x = upRen_Tm_Tm zeta x.
Proof.
exact (fun n => match n with
                | S n' => ap shift (Eq n')
                | O => eq_refl
                end).
Qed.

Fixpoint extRen_Ty (xi_Tm : nat -> nat) (zeta_Tm : nat -> nat)
(Eq_Tm : forall x, xi_Tm x = zeta_Tm x) (s : Ty) {struct s} :
ren_Ty xi_Tm s = ren_Ty zeta_Tm s :=
  match s with
  | TyVar s0 => congr_TyVar (eq_refl s0)
  | TyPi s0 s1 =>
      congr_TyPi (extRen_Ty xi_Tm zeta_Tm Eq_Tm s0)
        (extRen_Ty (upRen_Tm_Tm xi_Tm) (upRen_Tm_Tm zeta_Tm)
           (upExtRen_Tm_Tm _ _ Eq_Tm) s1)
  | TyTmApp s0 s1 =>
      congr_TyTmApp (extRen_Ty xi_Tm zeta_Tm Eq_Tm s0)
        (extRen_Tm xi_Tm zeta_Tm Eq_Tm s1)
  | TyUnit => congr_TyUnit
  end
with extRen_Tm (xi_Tm : nat -> nat) (zeta_Tm : nat -> nat)
(Eq_Tm : forall x, xi_Tm x = zeta_Tm x) (s : Tm) {struct s} :
ren_Tm xi_Tm s = ren_Tm zeta_Tm s :=
  match s with
  | TmVar s0 => ap (TmVar) (Eq_Tm s0)
  | TmAbs s0 s1 =>
      congr_TmAbs (extRen_Ty xi_Tm zeta_Tm Eq_Tm s0)
        (extRen_Tm (upRen_Tm_Tm xi_Tm) (upRen_Tm_Tm zeta_Tm)
           (upExtRen_Tm_Tm _ _ Eq_Tm) s1)
  | TmApp s0 s1 =>
      congr_TmApp (extRen_Tm xi_Tm zeta_Tm Eq_Tm s0)
        (extRen_Tm xi_Tm zeta_Tm Eq_Tm s1)
  | TmUnit => congr_TmUnit
  end.

Lemma upExt_Tm_Tm (sigma : nat -> Tm) (tau : nat -> Tm)
  (Eq : forall x, sigma x = tau x) :
  forall x, up_Tm_Tm sigma x = up_Tm_Tm tau x.
Proof.
exact (fun n =>
       match n with
       | S n' => ap (ren_Tm shift) (Eq n')
       | O => eq_refl
       end).
Qed.

Fixpoint ext_Ty (sigma_Tm : nat -> Tm) (tau_Tm : nat -> Tm)
(Eq_Tm : forall x, sigma_Tm x = tau_Tm x) (s : Ty) {struct s} :
subst_Ty sigma_Tm s = subst_Ty tau_Tm s :=
  match s with
  | TyVar s0 => congr_TyVar (eq_refl s0)
  | TyPi s0 s1 =>
      congr_TyPi (ext_Ty sigma_Tm tau_Tm Eq_Tm s0)
        (ext_Ty (up_Tm_Tm sigma_Tm) (up_Tm_Tm tau_Tm) (upExt_Tm_Tm _ _ Eq_Tm)
           s1)
  | TyTmApp s0 s1 =>
      congr_TyTmApp (ext_Ty sigma_Tm tau_Tm Eq_Tm s0)
        (ext_Tm sigma_Tm tau_Tm Eq_Tm s1)
  | TyUnit => congr_TyUnit
  end
with ext_Tm (sigma_Tm : nat -> Tm) (tau_Tm : nat -> Tm)
(Eq_Tm : forall x, sigma_Tm x = tau_Tm x) (s : Tm) {struct s} :
subst_Tm sigma_Tm s = subst_Tm tau_Tm s :=
  match s with
  | TmVar s0 => Eq_Tm s0
  | TmAbs s0 s1 =>
      congr_TmAbs (ext_Ty sigma_Tm tau_Tm Eq_Tm s0)
        (ext_Tm (up_Tm_Tm sigma_Tm) (up_Tm_Tm tau_Tm) (upExt_Tm_Tm _ _ Eq_Tm)
           s1)
  | TmApp s0 s1 =>
      congr_TmApp (ext_Tm sigma_Tm tau_Tm Eq_Tm s0)
        (ext_Tm sigma_Tm tau_Tm Eq_Tm s1)
  | TmUnit => congr_TmUnit
  end.

Lemma up_ren_ren_Tm_Tm (xi : nat -> nat) (zeta : nat -> nat)
  (rho : nat -> nat) (Eq : forall x, funcomp zeta xi x = rho x) :
  forall x, funcomp (upRen_Tm_Tm zeta) (upRen_Tm_Tm xi) x = upRen_Tm_Tm rho x.
Proof.
exact (up_ren_ren xi zeta rho Eq).
Qed.

Fixpoint compRenRen_Ty (xi_Tm : nat -> nat) (zeta_Tm : nat -> nat)
(rho_Tm : nat -> nat) (Eq_Tm : forall x, funcomp zeta_Tm xi_Tm x = rho_Tm x)
(s : Ty) {struct s} : ren_Ty zeta_Tm (ren_Ty xi_Tm s) = ren_Ty rho_Tm s :=
  match s with
  | TyVar s0 => congr_TyVar (eq_refl s0)
  | TyPi s0 s1 =>
      congr_TyPi (compRenRen_Ty xi_Tm zeta_Tm rho_Tm Eq_Tm s0)
        (compRenRen_Ty (upRen_Tm_Tm xi_Tm) (upRen_Tm_Tm zeta_Tm)
           (upRen_Tm_Tm rho_Tm) (up_ren_ren _ _ _ Eq_Tm) s1)
  | TyTmApp s0 s1 =>
      congr_TyTmApp (compRenRen_Ty xi_Tm zeta_Tm rho_Tm Eq_Tm s0)
        (compRenRen_Tm xi_Tm zeta_Tm rho_Tm Eq_Tm s1)
  | TyUnit => congr_TyUnit
  end
with compRenRen_Tm (xi_Tm : nat -> nat) (zeta_Tm : nat -> nat)
(rho_Tm : nat -> nat) (Eq_Tm : forall x, funcomp zeta_Tm xi_Tm x = rho_Tm x)
(s : Tm) {struct s} : ren_Tm zeta_Tm (ren_Tm xi_Tm s) = ren_Tm rho_Tm s :=
  match s with
  | TmVar s0 => ap (TmVar) (Eq_Tm s0)
  | TmAbs s0 s1 =>
      congr_TmAbs (compRenRen_Ty xi_Tm zeta_Tm rho_Tm Eq_Tm s0)
        (compRenRen_Tm (upRen_Tm_Tm xi_Tm) (upRen_Tm_Tm zeta_Tm)
           (upRen_Tm_Tm rho_Tm) (up_ren_ren _ _ _ Eq_Tm) s1)
  | TmApp s0 s1 =>
      congr_TmApp (compRenRen_Tm xi_Tm zeta_Tm rho_Tm Eq_Tm s0)
        (compRenRen_Tm xi_Tm zeta_Tm rho_Tm Eq_Tm s1)
  | TmUnit => congr_TmUnit
  end.

Lemma up_ren_subst_Tm_Tm (xi : nat -> nat) (tau : nat -> Tm)
  (theta : nat -> Tm) (Eq : forall x, funcomp tau xi x = theta x) :
  forall x, funcomp (up_Tm_Tm tau) (upRen_Tm_Tm xi) x = up_Tm_Tm theta x.
Proof.
exact (fun n =>
       match n with
       | S n' => ap (ren_Tm shift) (Eq n')
       | O => eq_refl
       end).
Qed.

Fixpoint compRenSubst_Ty (xi_Tm : nat -> nat) (tau_Tm : nat -> Tm)
(theta_Tm : nat -> Tm)
(Eq_Tm : forall x, funcomp tau_Tm xi_Tm x = theta_Tm x) (s : Ty) {struct s} :
subst_Ty tau_Tm (ren_Ty xi_Tm s) = subst_Ty theta_Tm s :=
  match s with
  | TyVar s0 => congr_TyVar (eq_refl s0)
  | TyPi s0 s1 =>
      congr_TyPi (compRenSubst_Ty xi_Tm tau_Tm theta_Tm Eq_Tm s0)
        (compRenSubst_Ty (upRen_Tm_Tm xi_Tm) (up_Tm_Tm tau_Tm)
           (up_Tm_Tm theta_Tm) (up_ren_subst_Tm_Tm _ _ _ Eq_Tm) s1)
  | TyTmApp s0 s1 =>
      congr_TyTmApp (compRenSubst_Ty xi_Tm tau_Tm theta_Tm Eq_Tm s0)
        (compRenSubst_Tm xi_Tm tau_Tm theta_Tm Eq_Tm s1)
  | TyUnit => congr_TyUnit
  end
with compRenSubst_Tm (xi_Tm : nat -> nat) (tau_Tm : nat -> Tm)
(theta_Tm : nat -> Tm)
(Eq_Tm : forall x, funcomp tau_Tm xi_Tm x = theta_Tm x) (s : Tm) {struct s} :
subst_Tm tau_Tm (ren_Tm xi_Tm s) = subst_Tm theta_Tm s :=
  match s with
  | TmVar s0 => Eq_Tm s0
  | TmAbs s0 s1 =>
      congr_TmAbs (compRenSubst_Ty xi_Tm tau_Tm theta_Tm Eq_Tm s0)
        (compRenSubst_Tm (upRen_Tm_Tm xi_Tm) (up_Tm_Tm tau_Tm)
           (up_Tm_Tm theta_Tm) (up_ren_subst_Tm_Tm _ _ _ Eq_Tm) s1)
  | TmApp s0 s1 =>
      congr_TmApp (compRenSubst_Tm xi_Tm tau_Tm theta_Tm Eq_Tm s0)
        (compRenSubst_Tm xi_Tm tau_Tm theta_Tm Eq_Tm s1)
  | TmUnit => congr_TmUnit
  end.

Lemma up_subst_ren_Tm_Tm (sigma : nat -> Tm) (zeta_Tm : nat -> nat)
  (theta : nat -> Tm)
  (Eq : forall x, funcomp (ren_Tm zeta_Tm) sigma x = theta x) :
  forall x,
  funcomp (ren_Tm (upRen_Tm_Tm zeta_Tm)) (up_Tm_Tm sigma) x =
  up_Tm_Tm theta x.
Proof.
exact (fun n =>
       match n with
       | S n' =>
           eq_trans
             (compRenRen_Tm shift (upRen_Tm_Tm zeta_Tm)
                (funcomp shift zeta_Tm) (fun x => eq_refl) (sigma n'))
             (eq_trans
                (eq_sym
                   (compRenRen_Tm zeta_Tm shift (funcomp shift zeta_Tm)
                      (fun x => eq_refl) (sigma n')))
                (ap (ren_Tm shift) (Eq n')))
       | O => eq_refl
       end).
Qed.

Fixpoint compSubstRen_Ty (sigma_Tm : nat -> Tm) (zeta_Tm : nat -> nat)
(theta_Tm : nat -> Tm)
(Eq_Tm : forall x, funcomp (ren_Tm zeta_Tm) sigma_Tm x = theta_Tm x) 
(s : Ty) {struct s} :
ren_Ty zeta_Tm (subst_Ty sigma_Tm s) = subst_Ty theta_Tm s :=
  match s with
  | TyVar s0 => congr_TyVar (eq_refl s0)
  | TyPi s0 s1 =>
      congr_TyPi (compSubstRen_Ty sigma_Tm zeta_Tm theta_Tm Eq_Tm s0)
        (compSubstRen_Ty (up_Tm_Tm sigma_Tm) (upRen_Tm_Tm zeta_Tm)
           (up_Tm_Tm theta_Tm) (up_subst_ren_Tm_Tm _ _ _ Eq_Tm) s1)
  | TyTmApp s0 s1 =>
      congr_TyTmApp (compSubstRen_Ty sigma_Tm zeta_Tm theta_Tm Eq_Tm s0)
        (compSubstRen_Tm sigma_Tm zeta_Tm theta_Tm Eq_Tm s1)
  | TyUnit => congr_TyUnit
  end
with compSubstRen_Tm (sigma_Tm : nat -> Tm) (zeta_Tm : nat -> nat)
(theta_Tm : nat -> Tm)
(Eq_Tm : forall x, funcomp (ren_Tm zeta_Tm) sigma_Tm x = theta_Tm x) 
(s : Tm) {struct s} :
ren_Tm zeta_Tm (subst_Tm sigma_Tm s) = subst_Tm theta_Tm s :=
  match s with
  | TmVar s0 => Eq_Tm s0
  | TmAbs s0 s1 =>
      congr_TmAbs (compSubstRen_Ty sigma_Tm zeta_Tm theta_Tm Eq_Tm s0)
        (compSubstRen_Tm (up_Tm_Tm sigma_Tm) (upRen_Tm_Tm zeta_Tm)
           (up_Tm_Tm theta_Tm) (up_subst_ren_Tm_Tm _ _ _ Eq_Tm) s1)
  | TmApp s0 s1 =>
      congr_TmApp (compSubstRen_Tm sigma_Tm zeta_Tm theta_Tm Eq_Tm s0)
        (compSubstRen_Tm sigma_Tm zeta_Tm theta_Tm Eq_Tm s1)
  | TmUnit => congr_TmUnit
  end.

Lemma up_subst_subst_Tm_Tm (sigma : nat -> Tm) (tau_Tm : nat -> Tm)
  (theta : nat -> Tm)
  (Eq : forall x, funcomp (subst_Tm tau_Tm) sigma x = theta x) :
  forall x,
  funcomp (subst_Tm (up_Tm_Tm tau_Tm)) (up_Tm_Tm sigma) x = up_Tm_Tm theta x.
Proof.
exact (fun n =>
       match n with
       | S n' =>
           eq_trans
             (compRenSubst_Tm shift (up_Tm_Tm tau_Tm)
                (funcomp (up_Tm_Tm tau_Tm) shift) (fun x => eq_refl)
                (sigma n'))
             (eq_trans
                (eq_sym
                   (compSubstRen_Tm tau_Tm shift
                      (funcomp (ren_Tm shift) tau_Tm) (fun x => eq_refl)
                      (sigma n')))
                (ap (ren_Tm shift) (Eq n')))
       | O => eq_refl
       end).
Qed.

Fixpoint compSubstSubst_Ty (sigma_Tm : nat -> Tm) (tau_Tm : nat -> Tm)
(theta_Tm : nat -> Tm)
(Eq_Tm : forall x, funcomp (subst_Tm tau_Tm) sigma_Tm x = theta_Tm x)
(s : Ty) {struct s} :
subst_Ty tau_Tm (subst_Ty sigma_Tm s) = subst_Ty theta_Tm s :=
  match s with
  | TyVar s0 => congr_TyVar (eq_refl s0)
  | TyPi s0 s1 =>
      congr_TyPi (compSubstSubst_Ty sigma_Tm tau_Tm theta_Tm Eq_Tm s0)
        (compSubstSubst_Ty (up_Tm_Tm sigma_Tm) (up_Tm_Tm tau_Tm)
           (up_Tm_Tm theta_Tm) (up_subst_subst_Tm_Tm _ _ _ Eq_Tm) s1)
  | TyTmApp s0 s1 =>
      congr_TyTmApp (compSubstSubst_Ty sigma_Tm tau_Tm theta_Tm Eq_Tm s0)
        (compSubstSubst_Tm sigma_Tm tau_Tm theta_Tm Eq_Tm s1)
  | TyUnit => congr_TyUnit
  end
with compSubstSubst_Tm (sigma_Tm : nat -> Tm) (tau_Tm : nat -> Tm)
(theta_Tm : nat -> Tm)
(Eq_Tm : forall x, funcomp (subst_Tm tau_Tm) sigma_Tm x = theta_Tm x)
(s : Tm) {struct s} :
subst_Tm tau_Tm (subst_Tm sigma_Tm s) = subst_Tm theta_Tm s :=
  match s with
  | TmVar s0 => Eq_Tm s0
  | TmAbs s0 s1 =>
      congr_TmAbs (compSubstSubst_Ty sigma_Tm tau_Tm theta_Tm Eq_Tm s0)
        (compSubstSubst_Tm (up_Tm_Tm sigma_Tm) (up_Tm_Tm tau_Tm)
           (up_Tm_Tm theta_Tm) (up_subst_subst_Tm_Tm _ _ _ Eq_Tm) s1)
  | TmApp s0 s1 =>
      congr_TmApp (compSubstSubst_Tm sigma_Tm tau_Tm theta_Tm Eq_Tm s0)
        (compSubstSubst_Tm sigma_Tm tau_Tm theta_Tm Eq_Tm s1)
  | TmUnit => congr_TmUnit
  end.

Lemma renRen_Ty (xi_Tm : nat -> nat) (zeta_Tm : nat -> nat) (s : Ty) :
  ren_Ty zeta_Tm (ren_Ty xi_Tm s) = ren_Ty (funcomp zeta_Tm xi_Tm) s.
Proof.
exact (compRenRen_Ty xi_Tm zeta_Tm _ (fun n => eq_refl) s).
Qed.

Lemma renRen'_Ty_pointwise (xi_Tm : nat -> nat) (zeta_Tm : nat -> nat) :
  pointwise_relation _ eq (funcomp (ren_Ty zeta_Tm) (ren_Ty xi_Tm))
    (ren_Ty (funcomp zeta_Tm xi_Tm)).
Proof.
exact (fun s => compRenRen_Ty xi_Tm zeta_Tm _ (fun n => eq_refl) s).
Qed.

Lemma renRen_Tm (xi_Tm : nat -> nat) (zeta_Tm : nat -> nat) (s : Tm) :
  ren_Tm zeta_Tm (ren_Tm xi_Tm s) = ren_Tm (funcomp zeta_Tm xi_Tm) s.
Proof.
exact (compRenRen_Tm xi_Tm zeta_Tm _ (fun n => eq_refl) s).
Qed.

Lemma renRen'_Tm_pointwise (xi_Tm : nat -> nat) (zeta_Tm : nat -> nat) :
  pointwise_relation _ eq (funcomp (ren_Tm zeta_Tm) (ren_Tm xi_Tm))
    (ren_Tm (funcomp zeta_Tm xi_Tm)).
Proof.
exact (fun s => compRenRen_Tm xi_Tm zeta_Tm _ (fun n => eq_refl) s).
Qed.

Lemma renSubst_Ty (xi_Tm : nat -> nat) (tau_Tm : nat -> Tm) (s : Ty) :
  subst_Ty tau_Tm (ren_Ty xi_Tm s) = subst_Ty (funcomp tau_Tm xi_Tm) s.
Proof.
exact (compRenSubst_Ty xi_Tm tau_Tm _ (fun n => eq_refl) s).
Qed.

Lemma renSubst_Ty_pointwise (xi_Tm : nat -> nat) (tau_Tm : nat -> Tm) :
  pointwise_relation _ eq (funcomp (subst_Ty tau_Tm) (ren_Ty xi_Tm))
    (subst_Ty (funcomp tau_Tm xi_Tm)).
Proof.
exact (fun s => compRenSubst_Ty xi_Tm tau_Tm _ (fun n => eq_refl) s).
Qed.

Lemma renSubst_Tm (xi_Tm : nat -> nat) (tau_Tm : nat -> Tm) (s : Tm) :
  subst_Tm tau_Tm (ren_Tm xi_Tm s) = subst_Tm (funcomp tau_Tm xi_Tm) s.
Proof.
exact (compRenSubst_Tm xi_Tm tau_Tm _ (fun n => eq_refl) s).
Qed.

Lemma renSubst_Tm_pointwise (xi_Tm : nat -> nat) (tau_Tm : nat -> Tm) :
  pointwise_relation _ eq (funcomp (subst_Tm tau_Tm) (ren_Tm xi_Tm))
    (subst_Tm (funcomp tau_Tm xi_Tm)).
Proof.
exact (fun s => compRenSubst_Tm xi_Tm tau_Tm _ (fun n => eq_refl) s).
Qed.

Lemma substRen_Ty (sigma_Tm : nat -> Tm) (zeta_Tm : nat -> nat) (s : Ty) :
  ren_Ty zeta_Tm (subst_Ty sigma_Tm s) =
  subst_Ty (funcomp (ren_Tm zeta_Tm) sigma_Tm) s.
Proof.
exact (compSubstRen_Ty sigma_Tm zeta_Tm _ (fun n => eq_refl) s).
Qed.

Lemma substRen_Ty_pointwise (sigma_Tm : nat -> Tm) (zeta_Tm : nat -> nat) :
  pointwise_relation _ eq (funcomp (ren_Ty zeta_Tm) (subst_Ty sigma_Tm))
    (subst_Ty (funcomp (ren_Tm zeta_Tm) sigma_Tm)).
Proof.
exact (fun s => compSubstRen_Ty sigma_Tm zeta_Tm _ (fun n => eq_refl) s).
Qed.

Lemma substRen_Tm (sigma_Tm : nat -> Tm) (zeta_Tm : nat -> nat) (s : Tm) :
  ren_Tm zeta_Tm (subst_Tm sigma_Tm s) =
  subst_Tm (funcomp (ren_Tm zeta_Tm) sigma_Tm) s.
Proof.
exact (compSubstRen_Tm sigma_Tm zeta_Tm _ (fun n => eq_refl) s).
Qed.

Lemma substRen_Tm_pointwise (sigma_Tm : nat -> Tm) (zeta_Tm : nat -> nat) :
  pointwise_relation _ eq (funcomp (ren_Tm zeta_Tm) (subst_Tm sigma_Tm))
    (subst_Tm (funcomp (ren_Tm zeta_Tm) sigma_Tm)).
Proof.
exact (fun s => compSubstRen_Tm sigma_Tm zeta_Tm _ (fun n => eq_refl) s).
Qed.

Lemma substSubst_Ty (sigma_Tm : nat -> Tm) (tau_Tm : nat -> Tm) (s : Ty) :
  subst_Ty tau_Tm (subst_Ty sigma_Tm s) =
  subst_Ty (funcomp (subst_Tm tau_Tm) sigma_Tm) s.
Proof.
exact (compSubstSubst_Ty sigma_Tm tau_Tm _ (fun n => eq_refl) s).
Qed.

Lemma substSubst_Ty_pointwise (sigma_Tm : nat -> Tm) (tau_Tm : nat -> Tm) :
  pointwise_relation _ eq (funcomp (subst_Ty tau_Tm) (subst_Ty sigma_Tm))
    (subst_Ty (funcomp (subst_Tm tau_Tm) sigma_Tm)).
Proof.
exact (fun s => compSubstSubst_Ty sigma_Tm tau_Tm _ (fun n => eq_refl) s).
Qed.

Lemma substSubst_Tm (sigma_Tm : nat -> Tm) (tau_Tm : nat -> Tm) (s : Tm) :
  subst_Tm tau_Tm (subst_Tm sigma_Tm s) =
  subst_Tm (funcomp (subst_Tm tau_Tm) sigma_Tm) s.
Proof.
exact (compSubstSubst_Tm sigma_Tm tau_Tm _ (fun n => eq_refl) s).
Qed.

Lemma substSubst_Tm_pointwise (sigma_Tm : nat -> Tm) (tau_Tm : nat -> Tm) :
  pointwise_relation _ eq (funcomp (subst_Tm tau_Tm) (subst_Tm sigma_Tm))
    (subst_Tm (funcomp (subst_Tm tau_Tm) sigma_Tm)).
Proof.
exact (fun s => compSubstSubst_Tm sigma_Tm tau_Tm _ (fun n => eq_refl) s).
Qed.

Lemma rinstInst_up_Tm_Tm (xi : nat -> nat) (sigma : nat -> Tm)
  (Eq : forall x, funcomp (TmVar) xi x = sigma x) :
  forall x, funcomp (TmVar) (upRen_Tm_Tm xi) x = up_Tm_Tm sigma x.
Proof.
exact (fun n =>
       match n with
       | S n' => ap (ren_Tm shift) (Eq n')
       | O => eq_refl
       end).
Qed.

Fixpoint rinst_inst_Ty (xi_Tm : nat -> nat) (sigma_Tm : nat -> Tm)
(Eq_Tm : forall x, funcomp (TmVar) xi_Tm x = sigma_Tm x) (s : Ty) {struct s}
   :
ren_Ty xi_Tm s = subst_Ty sigma_Tm s :=
  match s with
  | TyVar s0 => congr_TyVar (eq_refl s0)
  | TyPi s0 s1 =>
      congr_TyPi (rinst_inst_Ty xi_Tm sigma_Tm Eq_Tm s0)
        (rinst_inst_Ty (upRen_Tm_Tm xi_Tm) (up_Tm_Tm sigma_Tm)
           (rinstInst_up_Tm_Tm _ _ Eq_Tm) s1)
  | TyTmApp s0 s1 =>
      congr_TyTmApp (rinst_inst_Ty xi_Tm sigma_Tm Eq_Tm s0)
        (rinst_inst_Tm xi_Tm sigma_Tm Eq_Tm s1)
  | TyUnit => congr_TyUnit
  end
with rinst_inst_Tm (xi_Tm : nat -> nat) (sigma_Tm : nat -> Tm)
(Eq_Tm : forall x, funcomp (TmVar) xi_Tm x = sigma_Tm x) (s : Tm) {struct s}
   :
ren_Tm xi_Tm s = subst_Tm sigma_Tm s :=
  match s with
  | TmVar s0 => Eq_Tm s0
  | TmAbs s0 s1 =>
      congr_TmAbs (rinst_inst_Ty xi_Tm sigma_Tm Eq_Tm s0)
        (rinst_inst_Tm (upRen_Tm_Tm xi_Tm) (up_Tm_Tm sigma_Tm)
           (rinstInst_up_Tm_Tm _ _ Eq_Tm) s1)
  | TmApp s0 s1 =>
      congr_TmApp (rinst_inst_Tm xi_Tm sigma_Tm Eq_Tm s0)
        (rinst_inst_Tm xi_Tm sigma_Tm Eq_Tm s1)
  | TmUnit => congr_TmUnit
  end.

Lemma rinstInst'_Ty (xi_Tm : nat -> nat) (s : Ty) :
  ren_Ty xi_Tm s = subst_Ty (funcomp (TmVar) xi_Tm) s.
Proof.
exact (rinst_inst_Ty xi_Tm _ (fun n => eq_refl) s).
Qed.

Lemma rinstInst'_Ty_pointwise (xi_Tm : nat -> nat) :
  pointwise_relation _ eq (ren_Ty xi_Tm) (subst_Ty (funcomp (TmVar) xi_Tm)).
Proof.
exact (fun s => rinst_inst_Ty xi_Tm _ (fun n => eq_refl) s).
Qed.

Lemma rinstInst'_Tm (xi_Tm : nat -> nat) (s : Tm) :
  ren_Tm xi_Tm s = subst_Tm (funcomp (TmVar) xi_Tm) s.
Proof.
exact (rinst_inst_Tm xi_Tm _ (fun n => eq_refl) s).
Qed.

Lemma rinstInst'_Tm_pointwise (xi_Tm : nat -> nat) :
  pointwise_relation _ eq (ren_Tm xi_Tm) (subst_Tm (funcomp (TmVar) xi_Tm)).
Proof.
exact (fun s => rinst_inst_Tm xi_Tm _ (fun n => eq_refl) s).
Qed.

Lemma instId'_Ty (s : Ty) : subst_Ty (TmVar) s = s.
Proof.
exact (idSubst_Ty (TmVar) (fun n => eq_refl) s).
Qed.

Lemma instId'_Ty_pointwise : pointwise_relation _ eq (subst_Ty (TmVar)) id.
Proof.
exact (fun s => idSubst_Ty (TmVar) (fun n => eq_refl) s).
Qed.

Lemma instId'_Tm (s : Tm) : subst_Tm (TmVar) s = s.
Proof.
exact (idSubst_Tm (TmVar) (fun n => eq_refl) s).
Qed.

Lemma instId'_Tm_pointwise : pointwise_relation _ eq (subst_Tm (TmVar)) id.
Proof.
exact (fun s => idSubst_Tm (TmVar) (fun n => eq_refl) s).
Qed.

Lemma rinstId'_Ty (s : Ty) : ren_Ty id s = s.
Proof.
exact (eq_ind_r (fun t => t = s) (instId'_Ty s) (rinstInst'_Ty id s)).
Qed.

Lemma rinstId'_Ty_pointwise : pointwise_relation _ eq (@ren_Ty id) id.
Proof.
exact (fun s => eq_ind_r (fun t => t = s) (instId'_Ty s) (rinstInst'_Ty id s)).
Qed.

Lemma rinstId'_Tm (s : Tm) : ren_Tm id s = s.
Proof.
exact (eq_ind_r (fun t => t = s) (instId'_Tm s) (rinstInst'_Tm id s)).
Qed.

Lemma rinstId'_Tm_pointwise : pointwise_relation _ eq (@ren_Tm id) id.
Proof.
exact (fun s => eq_ind_r (fun t => t = s) (instId'_Tm s) (rinstInst'_Tm id s)).
Qed.

Lemma varL'_Tm (sigma_Tm : nat -> Tm) (x : nat) :
  subst_Tm sigma_Tm (TmVar x) = sigma_Tm x.
Proof.
exact (eq_refl).
Qed.

Lemma varL'_Tm_pointwise (sigma_Tm : nat -> Tm) :
  pointwise_relation _ eq (funcomp (subst_Tm sigma_Tm) (TmVar)) sigma_Tm.
Proof.
exact (fun x => eq_refl).
Qed.

Lemma varLRen'_Tm (xi_Tm : nat -> nat) (x : nat) :
  ren_Tm xi_Tm (TmVar x) = TmVar (xi_Tm x).
Proof.
exact (eq_refl).
Qed.

Lemma varLRen'_Tm_pointwise (xi_Tm : nat -> nat) :
  pointwise_relation _ eq (funcomp (ren_Tm xi_Tm) (TmVar))
    (funcomp (TmVar) xi_Tm).
Proof.
exact (fun x => eq_refl).
Qed.

Inductive Ki : Type :=
  | KiStar : Ki
  | KiPi : Ty -> Ki -> Ki.

Lemma congr_KiStar : KiStar = KiStar.
Proof.
exact (eq_refl).
Qed.

Lemma congr_KiPi {s0 : Ty} {s1 : Ki} {t0 : Ty} {t1 : Ki} (H0 : s0 = t0)
  (H1 : s1 = t1) : KiPi s0 s1 = KiPi t0 t1.
Proof.
exact (eq_trans (eq_trans eq_refl (ap (fun x => KiPi x s1) H0))
         (ap (fun x => KiPi t0 x) H1)).
Qed.

Fixpoint subst_Ki (sigma_Tm : nat -> Tm) (s : Ki) {struct s} : Ki :=
  match s with
  | KiStar => KiStar
  | KiPi s0 s1 =>
      KiPi (subst_Ty sigma_Tm s0) (subst_Ki (up_Tm_Tm sigma_Tm) s1)
  end.

Fixpoint idSubst_Ki (sigma_Tm : nat -> Tm)
(Eq_Tm : forall x, sigma_Tm x = TmVar x) (s : Ki) {struct s} :
subst_Ki sigma_Tm s = s :=
  match s with
  | KiStar => congr_KiStar
  | KiPi s0 s1 =>
      congr_KiPi (idSubst_Ty sigma_Tm Eq_Tm s0)
        (idSubst_Ki (up_Tm_Tm sigma_Tm) (upId_Tm_Tm _ Eq_Tm) s1)
  end.

Fixpoint ext_Ki (sigma_Tm : nat -> Tm) (tau_Tm : nat -> Tm)
(Eq_Tm : forall x, sigma_Tm x = tau_Tm x) (s : Ki) {struct s} :
subst_Ki sigma_Tm s = subst_Ki tau_Tm s :=
  match s with
  | KiStar => congr_KiStar
  | KiPi s0 s1 =>
      congr_KiPi (ext_Ty sigma_Tm tau_Tm Eq_Tm s0)
        (ext_Ki (up_Tm_Tm sigma_Tm) (up_Tm_Tm tau_Tm) (upExt_Tm_Tm _ _ Eq_Tm)
           s1)
  end.

Fixpoint compSubstSubst_Ki (sigma_Tm : nat -> Tm) (tau_Tm : nat -> Tm)
(theta_Tm : nat -> Tm)
(Eq_Tm : forall x, funcomp (subst_Tm tau_Tm) sigma_Tm x = theta_Tm x)
(s : Ki) {struct s} :
subst_Ki tau_Tm (subst_Ki sigma_Tm s) = subst_Ki theta_Tm s :=
  match s with
  | KiStar => congr_KiStar
  | KiPi s0 s1 =>
      congr_KiPi (compSubstSubst_Ty sigma_Tm tau_Tm theta_Tm Eq_Tm s0)
        (compSubstSubst_Ki (up_Tm_Tm sigma_Tm) (up_Tm_Tm tau_Tm)
           (up_Tm_Tm theta_Tm) (up_subst_subst_Tm_Tm _ _ _ Eq_Tm) s1)
  end.

Lemma substSubst_Ki (sigma_Tm : nat -> Tm) (tau_Tm : nat -> Tm) (s : Ki) :
  subst_Ki tau_Tm (subst_Ki sigma_Tm s) =
  subst_Ki (funcomp (subst_Tm tau_Tm) sigma_Tm) s.
Proof.
exact (compSubstSubst_Ki sigma_Tm tau_Tm _ (fun n => eq_refl) s).
Qed.

Lemma substSubst_Ki_pointwise (sigma_Tm : nat -> Tm) (tau_Tm : nat -> Tm) :
  pointwise_relation _ eq (funcomp (subst_Ki tau_Tm) (subst_Ki sigma_Tm))
    (subst_Ki (funcomp (subst_Tm tau_Tm) sigma_Tm)).
Proof.
exact (fun s => compSubstSubst_Ki sigma_Tm tau_Tm _ (fun n => eq_refl) s).
Qed.

Lemma instId'_Ki (s : Ki) : subst_Ki (TmVar) s = s.
Proof.
exact (idSubst_Ki (TmVar) (fun n => eq_refl) s).
Qed.

Lemma instId'_Ki_pointwise : pointwise_relation _ eq (subst_Ki (TmVar)) id.
Proof.
exact (fun s => idSubst_Ki (TmVar) (fun n => eq_refl) s).
Qed.

Class Up_Ki X Y :=
    up_Ki : X -> Y.

Class Up_Tm X Y :=
    up_Tm : X -> Y.

Class Up_Ty X Y :=
    up_Ty : X -> Y.

#[global] Instance Subst_Ki : (Subst1 _ _ _) := @subst_Ki.

#[global] Instance Subst_Tm : (Subst1 _ _ _) := @subst_Tm.

#[global] Instance Subst_Ty : (Subst1 _ _ _) := @subst_Ty.

#[global] Instance Up_Tm_Tm : (Up_Tm _ _) := @up_Tm_Tm.

#[global] Instance Ren_Tm : (Ren1 _ _ _) := @ren_Tm.

#[global] Instance Ren_Ty : (Ren1 _ _ _) := @ren_Ty.

#[global]
Instance VarInstance_Tm : (Var _ _) := @TmVar.

Notation "s [ sigma_Tm ]" := (subst_Ki sigma_Tm s)
( at level 7, left associativity, only printing)  : subst_scope.

Notation "↑__Ki" := up_Ki (only printing)  : subst_scope.

Notation "s [ sigma_Tm ]" := (subst_Tm sigma_Tm s)
( at level 7, left associativity, only printing)  : subst_scope.

Notation "↑__Tm" := up_Tm (only printing)  : subst_scope.

Notation "s [ sigma_Tm ]" := (subst_Ty sigma_Tm s)
( at level 7, left associativity, only printing)  : subst_scope.

Notation "↑__Ty" := up_Ty (only printing)  : subst_scope.

Notation "↑__Tm" := up_Tm_Tm (only printing)  : subst_scope.

Notation "s ⟨ xi_Tm ⟩" := (ren_Tm xi_Tm s)
( at level 7, left associativity, only printing)  : subst_scope.

Notation "s ⟨ xi_Tm ⟩" := (ren_Ty xi_Tm s)
( at level 7, left associativity, only printing)  : subst_scope.

Notation "'var'" := TmVar ( at level 1, only printing)  : subst_scope.

Notation "x '__Tm'" := (@ids _ _ VarInstance_Tm x)
( at level 5, format "x __Tm", only printing)  : subst_scope.

Notation "x '__Tm'" := (TmVar x) ( at level 5, format "x __Tm")  :
subst_scope.

#[global]
Instance subst_Ki_morphism :
 (Proper (respectful (pointwise_relation _ eq) (respectful eq eq))
    (@subst_Ki)).
Proof.
exact (fun f_Tm g_Tm Eq_Tm s t Eq_st =>
       eq_ind s (fun t' => subst_Ki f_Tm s = subst_Ki g_Tm t')
         (ext_Ki f_Tm g_Tm Eq_Tm s) t Eq_st).
Qed.

#[global]
Instance subst_Ki_morphism2 :
 (Proper (respectful (pointwise_relation _ eq) (pointwise_relation _ eq))
    (@subst_Ki)).
Proof.
exact (fun f_Tm g_Tm Eq_Tm s => ext_Ki f_Tm g_Tm Eq_Tm s).
Qed.

#[global]
Instance subst_Tm_morphism :
 (Proper (respectful (pointwise_relation _ eq) (respectful eq eq))
    (@subst_Tm)).
Proof.
exact (fun f_Tm g_Tm Eq_Tm s t Eq_st =>
       eq_ind s (fun t' => subst_Tm f_Tm s = subst_Tm g_Tm t')
         (ext_Tm f_Tm g_Tm Eq_Tm s) t Eq_st).
Qed.

#[global]
Instance subst_Tm_morphism2 :
 (Proper (respectful (pointwise_relation _ eq) (pointwise_relation _ eq))
    (@subst_Tm)).
Proof.
exact (fun f_Tm g_Tm Eq_Tm s => ext_Tm f_Tm g_Tm Eq_Tm s).
Qed.

#[global]
Instance subst_Ty_morphism :
 (Proper (respectful (pointwise_relation _ eq) (respectful eq eq))
    (@subst_Ty)).
Proof.
exact (fun f_Tm g_Tm Eq_Tm s t Eq_st =>
       eq_ind s (fun t' => subst_Ty f_Tm s = subst_Ty g_Tm t')
         (ext_Ty f_Tm g_Tm Eq_Tm s) t Eq_st).
Qed.

#[global]
Instance subst_Ty_morphism2 :
 (Proper (respectful (pointwise_relation _ eq) (pointwise_relation _ eq))
    (@subst_Ty)).
Proof.
exact (fun f_Tm g_Tm Eq_Tm s => ext_Ty f_Tm g_Tm Eq_Tm s).
Qed.

#[global]
Instance ren_Tm_morphism :
 (Proper (respectful (pointwise_relation _ eq) (respectful eq eq)) (@ren_Tm)).
Proof.
exact (fun f_Tm g_Tm Eq_Tm s t Eq_st =>
       eq_ind s (fun t' => ren_Tm f_Tm s = ren_Tm g_Tm t')
         (extRen_Tm f_Tm g_Tm Eq_Tm s) t Eq_st).
Qed.

#[global]
Instance ren_Tm_morphism2 :
 (Proper (respectful (pointwise_relation _ eq) (pointwise_relation _ eq))
    (@ren_Tm)).
Proof.
exact (fun f_Tm g_Tm Eq_Tm s => extRen_Tm f_Tm g_Tm Eq_Tm s).
Qed.

#[global]
Instance ren_Ty_morphism :
 (Proper (respectful (pointwise_relation _ eq) (respectful eq eq)) (@ren_Ty)).
Proof.
exact (fun f_Tm g_Tm Eq_Tm s t Eq_st =>
       eq_ind s (fun t' => ren_Ty f_Tm s = ren_Ty g_Tm t')
         (extRen_Ty f_Tm g_Tm Eq_Tm s) t Eq_st).
Qed.

#[global]
Instance ren_Ty_morphism2 :
 (Proper (respectful (pointwise_relation _ eq) (pointwise_relation _ eq))
    (@ren_Ty)).
Proof.
exact (fun f_Tm g_Tm Eq_Tm s => extRen_Ty f_Tm g_Tm Eq_Tm s).
Qed.

Ltac auto_unfold := repeat
                     unfold VarInstance_Tm, Var, ids, Ren_Ty, Ren1, ren1,
                      Ren_Tm, Ren1, ren1, Up_Tm_Tm, Up_Tm, up_Tm, Subst_Ty,
                      Subst1, subst1, Subst_Tm, Subst1, subst1, Subst_Ki,
                      Subst1, subst1.

Tactic Notation "auto_unfold" "in" "*" := repeat
                                           unfold VarInstance_Tm, Var, ids,
                                            Ren_Ty, Ren1, ren1, Ren_Tm, Ren1,
                                            ren1, Up_Tm_Tm, Up_Tm, up_Tm,
                                            Subst_Ty, Subst1, subst1,
                                            Subst_Tm, Subst1, subst1,
                                            Subst_Ki, Subst1, subst1 
                                            in *.

Ltac asimpl' := repeat (first
                 [ progress setoid_rewrite substSubst_Ki_pointwise
                 | progress setoid_rewrite substSubst_Ki
                 | progress setoid_rewrite substSubst_Tm_pointwise
                 | progress setoid_rewrite substSubst_Tm
                 | progress setoid_rewrite substSubst_Ty_pointwise
                 | progress setoid_rewrite substSubst_Ty
                 | progress setoid_rewrite substRen_Tm_pointwise
                 | progress setoid_rewrite substRen_Tm
                 | progress setoid_rewrite substRen_Ty_pointwise
                 | progress setoid_rewrite substRen_Ty
                 | progress setoid_rewrite renSubst_Tm_pointwise
                 | progress setoid_rewrite renSubst_Tm
                 | progress setoid_rewrite renSubst_Ty_pointwise
                 | progress setoid_rewrite renSubst_Ty
                 | progress setoid_rewrite renRen'_Tm_pointwise
                 | progress setoid_rewrite renRen_Tm
                 | progress setoid_rewrite renRen'_Ty_pointwise
                 | progress setoid_rewrite renRen_Ty
                 | progress setoid_rewrite instId'_Ki_pointwise
                 | progress setoid_rewrite instId'_Ki
                 | progress setoid_rewrite varLRen'_Tm_pointwise
                 | progress setoid_rewrite varLRen'_Tm
                 | progress setoid_rewrite varL'_Tm_pointwise
                 | progress setoid_rewrite varL'_Tm
                 | progress setoid_rewrite rinstId'_Tm_pointwise
                 | progress setoid_rewrite rinstId'_Tm
                 | progress setoid_rewrite rinstId'_Ty_pointwise
                 | progress setoid_rewrite rinstId'_Ty
                 | progress setoid_rewrite instId'_Tm_pointwise
                 | progress setoid_rewrite instId'_Tm
                 | progress setoid_rewrite instId'_Ty_pointwise
                 | progress setoid_rewrite instId'_Ty
                 | progress unfold up_Tm_Tm, upRen_Tm_Tm, up_ren
                 | progress cbn[subst_Ki subst_Tm subst_Ty ren_Tm ren_Ty]
                 | progress fsimpl ]).

Ltac asimpl := check_no_evars;
                repeat
                 unfold VarInstance_Tm, Var, ids, Ren_Ty, Ren1, ren1, Ren_Tm,
                  Ren1, ren1, Up_Tm_Tm, Up_Tm, up_Tm, Subst_Ty, Subst1,
                  subst1, Subst_Tm, Subst1, subst1, Subst_Ki, Subst1, subst1
                  in *;
                asimpl'; minimize.

Tactic Notation "asimpl" "in" hyp(J) := revert J; asimpl; intros J.

Tactic Notation "auto_case" := auto_case ltac:(asimpl; cbn; eauto).

Ltac substify := auto_unfold; try setoid_rewrite rinstInst'_Tm_pointwise;
                  try setoid_rewrite rinstInst'_Tm;
                  try setoid_rewrite rinstInst'_Ty_pointwise;
                  try setoid_rewrite rinstInst'_Ty.

Ltac renamify := auto_unfold; try setoid_rewrite_left rinstInst'_Tm_pointwise;
                  try setoid_rewrite_left rinstInst'_Tm;
                  try setoid_rewrite_left rinstInst'_Ty_pointwise;
                  try setoid_rewrite_left rinstInst'_Ty.

End Core.

Module Extra.

Import Core.

#[global] Hint Opaque subst_Ki: rewrite.

#[global] Hint Opaque subst_Tm: rewrite.

#[global] Hint Opaque subst_Ty: rewrite.

#[global] Hint Opaque ren_Tm: rewrite.

#[global] Hint Opaque ren_Ty: rewrite.

End Extra.

Module interface.

Export Core.

Export Extra.

End interface.

Export interface.

