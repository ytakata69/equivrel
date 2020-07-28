Require Import equiv.

Lemma type_guarantees_applicability :
  forall (theta : assignment) gamma b,
  is_equiv_rel gamma ->
    theta |= gamma -> gamma |= b <-> exists d, (theta , d) |= b.
Proof.
  intros theta gamma b gamma_equiv;
  intros theta_gamma.
  destruct gamma_equiv as [gref [gsym gtran]].
  split; intros gamma_b.
  - destruct (b_is_empty_or_not b) as [b_empty | [i1 bi1]].
    + destruct (outside_data_exists theta) as [dd dd_neq].
      exists dd.
      unfold models. unfold assignmentD_models_guard.
      intros i0.
      split; intros H'.
      * apply dd_neq in H'. contradiction.
      * apply b_empty in H'. contradiction.
    + apply gamma_b in bi1.
      exists (theta i1).
      unfold models. unfold assignmentD_models_guard.
      intros i0.
      split; intros H'.
      * apply bi1. apply theta_gamma. auto.
      * apply theta_gamma. apply gsym. apply bi1. auto.
  - destruct gamma_b as [d theta_d_b].
    unfold models. unfold rel_models_guard.
    intros i1 bi1 j1.
    split; intros H.
    + apply theta_gamma.
      apply theta_d_b in bi1. rewrite bi1.
      apply theta_d_b in H. rewrite H. reflexivity.
    + apply theta_d_b in bi1.
      apply theta_d_b. rewrite <- bi1.
      apply theta_gamma.
      apply gsym. auto.
Qed.

Lemma type_uniqueness :
  forall (theta : assignment) gamma gamma',
  is_equiv_rel gamma ->
  is_equiv_rel gamma' ->
    theta |= gamma /\ theta |= gamma' -> gamma = gamma'.
Proof.
  intros theta gamma gamma';
  intros gamma_equiv gamma'_equiv.
  unfold models; unfold assignment_models_rel.
  intros [[gsimpl tg] [g'simpl tg']].
  apply rel_extensionality.
  intros x y.
  split; intros Hg.
  - case x, y.
    + apply tg'. apply tg in Hg. assumption.
    + apply (gsimpl (X i) (X' i0)) in Hg. discriminate.
    + apply (gsimpl (X' i) (X i0)) in Hg. discriminate.
    + apply (gsimpl (X' i) (X' i0)) in Hg.
      case Hg.
      destruct gamma'_equiv as [g'ref _].
      apply g'ref.
  - case x, y.
    + apply tg. apply tg' in Hg. assumption.
    + apply (g'simpl (X i) (X' i0)) in Hg. discriminate.
    + apply (g'simpl (X' i) (X i0)) in Hg. discriminate.
    + apply (g'simpl (X' i) (X' i0)) in Hg.
      case Hg.
      destruct gamma_equiv as [gref _].
      apply gref.
Qed.

Lemma updater_must_exist :
  forall (theta : assignment) gamma b,
    is_equiv_rel gamma -> theta |= gamma -> gamma |= b ->
    exists d : D, (theta, d) |= b.
Proof.
  intros theta gamma b;
  intros [_ [ga_sym _]] th_ga ga_b.
  destruct (b_is_empty_or_not b) as [b_empty | [i bi]].
  - destruct (outside_data_exists theta) as [d d_notin].
    exists d.
    unfold models; unfold assignmentD_models_guard.
    intros i.
    split; intros H.
  + elim (d_notin i); exact H.
  + elim (b_empty i); exact H.
  - exists (theta i).
    unfold models; unfold assignmentD_models_guard.
    intros j.
    split; intros H.
  + apply th_ga in H.
    apply ga_sym in H.
    apply ga_b in H.
  * exact H.
  * exact bi.
  + apply th_ga.
    apply ga_b.
  * exact H.
  * exact bi.
Qed.

(* lat *)

Lemma lat_phi_is_equiv_rel :
  forall (phi : Rel), is_equiv_rel phi -> is_equiv_rel (lat phi).
Proof.
  intros phi phi_equiv.
  destruct phi_equiv as [phi_refl [phi_sym phi_tran]].
  unfold is_equiv_rel.
  repeat split.
  - unfold is_reflexive.
    intros x.
    unfold lat.
    case x; try auto.
  - unfold is_symmetric.
    unfold lat.
    intros x y H.
    case x, y; try auto.
  - unfold is_transitive.
    unfold lat.
    intros x y z [H1 H2].
    case x, y, z; try discriminate; try auto.
  + apply (phi_tran _ (X' i0) _).
    auto.
  + rewrite H1; exact H2.
Qed.

Lemma lat_phi_is_simpl_rel :
  forall (phi : Rel), is_simpl_rel (lat phi).
Proof.
  intros phi.
  unfold is_simpl_rel; unfold lat.
  intros x y.
  case x, y; try reflexivity.
Qed.

Lemma gamma_lat_phi :
  forall (gamma phi : Rel) (theta theta' : assignment),
    is_simpl_rel gamma ->
    (theta', theta) |= phi ->
    theta |= gamma <-> gamma = lat phi.
Proof.
  intros gamma phi theta theta';
  intros ga_simpl theta_phi.
  split.
{
  intros th_ga.
  apply rel_extensionality.
  intros x y.
  split; intros H.
  - unfold lat.
    case x, y.
  + apply theta_phi; apply th_ga; exact H.
  + apply (ga_simpl (X i) (X' i0)); exact H.
  + apply (ga_simpl (X' i) (X i0)); exact H.
  + apply (ga_simpl (X' i) (X' i0)); exact H.
  - case x, y.
  + unfold lat in H.
    apply th_ga; apply theta_phi; exact H.
  + unfold lat in H.
    apply (ga_simpl (X i) (X' i0)); exact H.
  + unfold lat in H.
    apply (ga_simpl (X' i) (X i0)); exact H.
  + unfold lat in H.
    apply (ga_simpl (X' i) (X' i0)); exact H.
}
{
  intros ga_latphi.
  unfold models; unfold assignment_models_rel.
  split; try auto.
  intros i j.
  rewrite ga_latphi.
  unfold lat.
  split; intros H.
  - apply theta_phi; exact H.
  - apply theta_phi; exact H.
}
Qed.

Lemma lat_eq_lat_afterL :
  forall phi j,
    lat phi = lat (afterL phi j).
Proof.
  intros phi j.
  apply rel_extensionality.
  unfold lat.
  case x, y; try reflexivity.
Qed.

Lemma gamma_lat_rel_between :
  forall (gamma : Rel) (theta theta' : assignment),
    is_simpl_rel gamma ->
    theta |= gamma ->
      gamma = lat (rel_between theta' theta).
Proof.
  intros gamma theta theta';
  intros ga_simpl th_ga.
  apply rel_extensionality.
  unfold lat; unfold rel_between.
  case x, y.
  - split; intros H; apply th_ga; exact H.
  - split; intros H;
    apply (ga_simpl (X i) (X' i0)); exact H.
  - split; intros H;
    apply (ga_simpl (X' i) (X i0)); exact H.
  - split; intros H;
    apply (ga_simpl (X' i) (X' i0)); exact H.
Qed.

(* rel_between *)

Lemma assignments_model_rel_between :
  forall theta theta',
  (theta, theta') |= rel_between theta theta'.
Proof.
  intros theta theta'.
  unfold models; unfold two_assignments_model_rel.
  unfold rel_between.
  intros i j.
  repeat split; auto.
Qed.
