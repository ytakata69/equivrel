Require Import equiv.
Require Import after after_r after_l.

(* auxiliary lemmas *)

Lemma gamma_lat_phi :
  forall (gamma phi : Rel) (theta theta' : assignment),
    is_simpl_rel gamma ->
    theta |= gamma ->
    (theta', theta) |= phi ->
      gamma = lat phi.
Proof.
  intros gamma phi theta theta';
  intros ga_simpl th_ga theta_phi.
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

(* main lemmas *)

Parameter A B : V.
Parameter phi : Rel.
Axiom phi_equiv : is_equiv_rel phi.

Lemma derivG_implies_derivG'_1 :
  forall gamma gamma' theta1 theta2 theta'1,
    is_simpl_rel gamma ->
    derivG ((A, gamma), theta1) None ((B, gamma'), theta2) ->
    theta1 |= gamma ->
    (theta'1, theta1) |= phi ->
  exists phi',
    theta2 |= gamma' /\
    (theta'1, theta2) |= phi' /\
    derivG' ((A, phi), theta'1) None ((B, phi'), theta'1).
Proof.
  intros gamma gamma' theta1 theta2 theta'1.
  intros ga_simpl derivGAB th1_ga theta_phi.
  unfold derivG in derivGAB.

  assert (gaphi: gamma = lat phi).
  { apply (gamma_lat_phi _ _ theta1 theta'1); try auto. }

  destruct derivGAB
  as [[rAB th1th2] | [b [i [d [rAB [th1db th2up]]]]]].
  - (* th1th2: theta1 = theta2 *)
    exists phi.
    apply ruleG_is_normal_form in rAB as gaga'.
    split.
    { rewrite <- gaga'; rewrite <- th1th2; exact th1_ga. }
    split.
    { rewrite <- th1th2; exact theta_phi. }
    { unfold derivG'.
      split; auto.
      unfold ruleG'.
      left.
      repeat split. (* one nontrivial case remains *)
      rewrite <- gaphi.
      rewrite <- gaga' in rAB.
      exact rAB.
    }
  - (* th2up: theta2 = update theta1 i d *)
    exists (rel_between theta'1 theta2).
    apply ruleG_is_normal_form in rAB as gaga'.
    split.
    { (* theta2 |= gamma' *)
      rewrite gaga'; rewrite th2up.
      apply updated_assignment_models_after.
      auto. }
    split.
    { (* theta'1, theta2) |= rel_between theta'1 theta2 *)
      apply assignments_model_rel_between. }
    { (* derivG' (A, phi, theta'1) None (B, rel_between..., theta'1) *)
      unfold derivG'.
      repeat split.
      unfold ruleG'.
      right.
      exists b; exists i.
      split.
    - rewrite <- gaphi.
      assert (ga'phi': gamma' = lat (rel_between theta'1 theta2)).
      { apply gamma_lat_rel_between.
        rewrite gaga'.
        apply after_is_simpl_rel.
        rewrite gaga'; rewrite th2up.
        apply updated_assignment_models_after.
        auto. }
      rewrite <- ga'phi'.
      exact rAB.
    - split; auto.
      apply (deriv_implies_afterR _ _ theta1 theta'1 b i d);
        auto.
      rewrite <- th2up.
      apply assignments_model_rel_between.
    }
Qed.

Lemma derivG_implies_derivG'_2 :
  forall gamma theta1 theta'1 d,
    is_simpl_rel gamma ->
    derivG ((A, gamma), theta1) (Some d) ((B, gamma), theta1) ->
    theta1 |= gamma ->
    (theta'1, theta1) |= phi ->
  exists phi' theta'2,
    (theta'2, theta1) |= phi' /\
    derivG' ((A, phi), theta'1) (Some d) ((B, phi'), theta'2).
Proof.
  intros gamma theta1 theta'1 d;
  intros ga_simpl derivGAB th1_ga theta_phi.
  unfold derivG in derivGAB.

  destruct derivGAB as [j [rAB [_ d_th1]]].
  exists (afterL phi j); exists (update theta'1 j d).
  split.
  - (* (update theta'1 j d, theta1) |= afterL phi j *)
    destruct (deriv_implies_afterL phi theta1 theta'1 j d);
    try auto.
  - (* derivG' (A, phi, theta'1) (Some d) (B, afterL phi j, theta'2) *)
    unfold derivG'.
    exists (inv phi j); exists j; exists j; exists d.
    unfold ruleG'.
    repeat split; try auto.
  + assert (gaphi: gamma = lat phi).
    { apply (gamma_lat_phi _ _ theta1 theta'1); try auto. }
    rewrite <- gaphi.
    assert (latphi: lat phi = lat (afterL phi j)).
    { apply lat_eq_lat_afterL. }
    rewrite <- latphi; rewrite <- gaphi. exact rAB.
  + intros H.
    unfold inv; apply theta_phi.
    rewrite H. exact d_th1.
  + intros H.
    unfold inv in H; apply theta_phi in H.
    rewrite d_th1. exact H.
  + unfold update.
    rewrite <- beq_nat_refl.
    reflexivity.
Qed.
