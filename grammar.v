Require Import equiv.
Require Import register_type.
Require Import after after_r after_l.

Parameter A B : V.
Parameter phi : Rel.
Axiom phi_equiv : is_equiv_rel phi.

Lemma derivG'_implies_derivG :
  classic ->
  forall phi phi' gamma theta1 theta'1,
    is_equiv_rel phi -> is_equiv_rel phi' ->
    derivG' ((A, phi), theta'1) None ((B, phi'), theta'1) ->
    gamma = lat phi ->
    theta1 |= gamma ->
    (theta'1, theta1) |= phi ->
  exists theta2 gamma',
    theta2 |= gamma' /\
    (theta'1, theta2) |= phi' /\
    derivG ((A, gamma), theta1) None ((B, gamma'), theta2).
Proof.
  intros Classic;
  intros phi phi' gamma theta1 theta'1;
  intros phi_equiv phi'_equiv.
  intros derivG'AB ga_phi th1_ga theta_phi.
  destruct derivG'AB as [r'AB _].
  destruct r'AB as [[rAB [p'p _]] | [b [i [rAB [phi'_afterR _]]]]].

  - rewrite p'p in rAB; rewrite <- ga_phi in rAB.
    rewrite p'p.
    exists theta1; exists gamma.
    repeat split; try auto.
  + rewrite ga_phi.
    apply lat_phi_is_simpl_rel.
  + intros H; apply th1_ga; exact H.
  + intros H; apply th1_ga; exact H.
  + intros H; apply theta_phi; exact H.
  + intros H; apply theta_phi; exact H.
  + intros H; apply theta_phi; exact H.
  + intros H; apply theta_phi; exact H.
  + intros H; apply theta_phi; exact H.
  + intros H; apply theta_phi; exact H.
  + intros H; apply theta_phi; exact H.
  + intros H; apply theta_phi; exact H.
  + unfold derivG.
    left.
    split; auto.

  - assert (lat_phi_b: lat phi |= b).
    { apply (type_guarantees_applicability theta1 (lat phi) b).
    - apply lat_phi_is_equiv_rel.
      assumption.
    - rewrite <- ga_phi; assumption.
    - apply (updater_must_exist theta1 gamma b).
      rewrite ga_phi.
      apply lat_phi_is_equiv_rel.
      apply phi_equiv.
      apply th1_ga.
      apply ruleG_is_normal_form in rAB as [lat_phi_b _].
      rewrite ga_phi.
      assumption.
    }
    destruct (afterR_implies_deriv Classic phi phi' theta1 theta'1 b
              phi_equiv phi'_equiv theta_phi lat_phi_b i) as [d [H0 H1]].
      assumption.
    exists (update theta1 i d).
    exists (after gamma b i).
    split.
    { (* update theta1 i d |= after gamma b i *)
      apply updated_assignment_models_after.
      split; try assumption.
    }
    split; try assumption.
    { (* derivG ... *)
      unfold derivG.
      right.
      exists b; exists i; exists d.
      split; try auto.
    - rewrite ga_phi.

      assert (lat_phi_after: lat phi' = after (lat phi) b i).
      { apply rel_extensionality.
        unfold lat; unfold after.
        case x, y; try reflexivity.
      - case_eq (i0 =? i); case_eq (i1 =? i); intros i1i i0i.
      + apply beq_nat_true in i0i;
        apply beq_nat_true in i1i.
        rewrite i0i; rewrite i1i.
        split; intros H.
      * right; reflexivity.
      * destruct phi'_equiv as [phi'_refl _].
        apply phi'_refl.
      + apply beq_nat_true in i0i.
        rewrite i0i.
        split; intros H.
      * apply H1 in H.
        unfold update in H.
        rewrite i1i in H; rewrite <- beq_nat_refl in H.
        left; apply H0.
        symmetry. exact H.
      * apply H1.
        unfold update.
        rewrite i1i; rewrite <- beq_nat_refl.
        destruct H as [H | H].
      -- apply H0 in H; auto.
      -- apply beq_nat_false in i1i.
        elim i1i. exact H.
      + apply beq_nat_true in i1i.
        rewrite i1i.
        split; intros H.
      * apply H0.
        apply H1 in H.
        unfold update in H.
        rewrite i0i in H; rewrite <- beq_nat_refl in H.
        exact H.
      * apply H1; unfold update.
        rewrite i0i; rewrite <- beq_nat_refl.
        apply H0 in H; exact H.
      + split; intros H.
      * apply theta_phi.
        apply H1 in H.
        unfold update in H.
        rewrite i0i in H; rewrite i1i in H.
        exact H.
      * apply H1; unfold update.
        rewrite i0i; rewrite i1i.
        apply theta_phi in H.
        exact H.
      }

      rewrite <- lat_phi_after.
      assumption.
    }
Qed.

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
    destruct gaga' as [_ gaga'].
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
