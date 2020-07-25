Require Import equiv.

Parameter b : guard.
Parameter theta theta' : assignment.
Parameter phi : Rel.
Parameter phi_equiv : is_equiv_rel phi.
Parameter theta_phi : (theta', theta) |= phi.

Lemma deriv_implies_afterL :
  forall (d : D) (j : nat),
    theta j = d ->
      (theta', d) |= inv phi j /\
      ((update theta' j d), theta) |= afterL phi j.
Proof.
  intros d j theta_j_d.
  split.
  - (* (theta', d) |= inv phi j *)
    unfold models; unfold assignmentD_models_guard.
    intros i.
    split; intros H.
    { unfold inv.
      apply theta_phi.
      rewrite H. auto. }
    rewrite <- theta_j_d.
    apply theta_phi.
    apply H.
  - (* ((update theta' j d), theta) |= afterL phi j *)
    unfold models; unfold two_assignments_model_rel.
    split. (* 4 cases *)
    { (* update theta' j d i = update theta' j d j0
         <-> afterL phi j (X i) (X j0) *)
      split; intros H.
    + (* -> *)
      unfold afterL. unfold after.
      case_eq (i =? j); intros ij.
    * (* ij: (i =? j) = true *)
      unfold inv.
      unfold update in H.
      rewrite ij in H.
      case_eq (j0 =? j); intros j0j.
        right. apply beq_nat_eq. auto.
      rewrite j0j in H.
      left.
      apply theta_phi.
      rewrite theta_j_d. auto.
    * (* ij: (i =? j) = false *)
      unfold update in H.
      rewrite ij in H.
      case_eq (j0 =? j); intros j0j.
    -- (* j0j: (j0 =? j) = true *)
      rewrite j0j in H.
      unfold inv.
      apply theta_phi.
      rewrite theta_j_d. auto.
    -- (* j0j: (j0 =? j) = false *)
      rewrite j0j in H.
      unfold former.
      apply theta_phi. assumption.
    + (* <- *)
      unfold update.
      unfold afterL in H.
      unfold after in H.
      case_eq (i =? j); intros ij.
    * (* ij: (i =? j) = true *)
      rewrite ij in H.
      destruct H as [H | H].
    -- unfold inv in H.
      apply theta_phi in H.
      rewrite H.
      rewrite theta_j_d.
      case (j0 =? j); trivial.
    -- rewrite H.
      rewrite <- beq_nat_refl. trivial.
    * (* ij: (i =? j) = false *)
      rewrite ij in H.
      case_eq (j0 =? j); intros j0j.
    -- (* j0j: (j0 =? j) = true *)
      rewrite j0j in H.
      unfold inv in H.
      apply theta_phi in H.
      rewrite theta_j_d in H. assumption.
    -- (* j0j: (j0 =? j) = false *)
      rewrite j0j in H.
      unfold former in H.
      apply theta_phi in H. assumption.
    }
    split. (* last 3 cases *)
    { (* theta i = theta j0 <-> afterL phi j (X' i) (X' j0) *)
      split; intros H.
    + (* -> *)
      unfold afterL.
      apply theta_phi in H.
      assumption.
    + (* <- *)
      unfold afterL in H.
      apply theta_phi.
      assumption.
    }
    split. (* last 2 cases *)
    { (* update theta' j d i = theta j0 <-> afterL phi j (X i) (X' j0) *)
      split; intros H.
    + (* -> *)
      unfold afterL.
      case_eq (i =? j); intros ij.
    * apply theta_phi.
      rewrite theta_j_d.
      unfold update in H.
      rewrite ij in H.
      assumption.
    * apply theta_phi.
      unfold update in H.
      rewrite ij in H.
      assumption.
    + (* <- *)
      unfold afterL in H.
      unfold update.
      case_eq (i =? j); intros ij.
    * rewrite ij in H.
      apply theta_phi in H.
      rewrite theta_j_d in H.
      assumption.
    * rewrite ij in H.
      apply theta_phi in H.
      assumption.
    }
    { (* theta i = update theta' j d j0 <-> afterL phi j (X' i) (X j0) *)
      split; intros H.
    + (* -> *)
      unfold afterL.
      case_eq (j0 =? j); intros j0j.
    * apply theta_phi.
      rewrite theta_j_d.
      unfold update in H.
      rewrite j0j in H. auto.
    * apply theta_phi.
      unfold update in H.
      rewrite j0j in H.
      assumption.
    + (* <- *)
      unfold afterL in H.
      unfold update.
      case_eq (j0 =? j); intros j0j.
    * rewrite j0j in H.
      apply theta_phi in H.
      rewrite theta_j_d in H. auto.
    * rewrite j0j in H.
      apply theta_phi in H.
      assumption.
    }
Qed.
