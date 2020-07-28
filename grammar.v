Require Import equiv.
Require Import after after_r.

Parameter A B : V.
Parameter phi : Rel.
Axiom phi_equiv : is_equiv_rel phi.

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

Lemma derivG_implies_derivG' :
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
  { apply rel_extensionality.
    intros x y.
    split; intros H.
  - unfold lat.
    case x, y.
  + apply theta_phi; apply th1_ga; exact H.
  + apply (ga_simpl (X i) (X' i0)); exact H.
  + apply (ga_simpl (X' i) (X i0)); exact H.
  + apply (ga_simpl (X' i) (X' i0)); exact H.
  - case x, y.
  + unfold lat in H.
    apply th1_ga; apply theta_phi; exact H.
  + unfold lat in H.
    apply (ga_simpl (X i) (X' i0)); exact H.
  + unfold lat in H.
    apply (ga_simpl (X' i) (X i0)); exact H.
  + unfold lat in H.
    apply (ga_simpl (X' i) (X' i0)); exact H.
  }

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
      { apply rel_extensionality.
        intros x y.
        rewrite gaga'.
        unfold after.
        unfold rel_between; unfold lat.
        case x, y; try reflexivity.
      - (* x = X i0, y = X i1 *)
        case_eq (i0 =? i); intros i0i.
      + (* i0 = i *)
        apply beq_nat_true in i0i.
        split; intros H.
      * (* b i1 \/ i1 = i -> theta2 i0 = theta2 i1 *)
        rewrite i0i.
        rewrite th2up; unfold update.
        rewrite <- beq_nat_refl.
        destruct H as [H | H].
      -- apply th1db in H.
        case (i1 =? i); auto.
      -- rewrite H; rewrite <- beq_nat_refl.
        reflexivity.
      * (* <- *)
        rewrite i0i in H.
        case_eq (i1 =? i); intros i1i.
      -- apply beq_nat_true in i1i.
        right; assumption.
      -- left.
        apply th1db.
        rewrite th2up in H.
        unfold update in H.
        rewrite <- beq_nat_refl in H.
        rewrite i1i in H.
        symmetry; exact H.
      + (* i0 <> i *)
        split; intros H.
      * (* (if i1 =? i then b i 0 else gamma (X i0) (X i1))
           -> theta2 i0 = theta2 i1 *)
        case_eq (i1 =? i); intros i1i.
      -- rewrite i1i in H.
        apply th1db in H.
        rewrite th2up; unfold update.
        rewrite i0i; rewrite i1i.
        exact H.
      -- rewrite i1i in H.
        rewrite th2up; unfold update.
        rewrite i0i; rewrite i1i.
        apply th1_ga; exact H.
      * (* <- *)
        case_eq (i1 =? i); intros i1i.
      -- apply th1db.
        rewrite th2up in H; unfold update in H.
        rewrite i0i in H; rewrite i1i in H.
        exact H.
      -- apply th1_ga.
        rewrite th2up in H; unfold update in H.
        rewrite i0i in H; rewrite i1i in H.
        exact H.
      }
      rewrite <- ga'phi'.
      exact rAB.
    - split; auto.
      apply (deriv_implies_afterR _ _ theta1 theta'1 b i d);
        auto.
      rewrite <- th2up.
      apply assignments_model_rel_between.
    }
Qed.
