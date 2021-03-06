Require Import equiv.
Require Import register_type.

Lemma updated_assignment_models_former_afterL :
  forall phi theta' j d,
    theta' |= former phi ->
    (theta', d) |= inv phi j ->
    update theta' j d |= former (afterL phi j).
Proof.
  intros phi theta' j d theta_phi theta'_d_b.
  unfold models; unfold assignment_models_rel.
  split.
    apply former_is_simpl_rel.
  intros i0 j0.
  unfold update; unfold former; unfold afterL;
  unfold after.
  case_eq (i0 =? j); intros i0j.
  - case_eq (j0 =? j); intros j0j.
  + split; intros H.
  * right; apply beq_nat_true; exact j0j.
  * reflexivity.
  + split; intros H.
  * left.
    apply theta'_d_b; auto.
  * destruct H as [H | H].
      apply theta'_d_b in H; auto.
    apply beq_nat_false in j0j.
    contradiction.
  - case_eq (j0 =? j); intros j0j.
  + split; intros H.
  * apply theta'_d_b; exact H.
  * apply theta'_d_b in H; exact H.
  + unfold former.
    split; intros H;
    apply theta_phi; exact H.
Qed.

Lemma deriv_implies_afterL :
  forall phi theta theta' j d,
    (theta', theta) |= phi ->
    theta j = d ->
      (theta', d) |= inv phi j /\
      (update theta' j d, theta) |= afterL phi j.
Proof.
  intros phi theta theta' j d;
  intros theta_phi theta_j_d.
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

Lemma afterL_is_equiv_rel :
forall phi j,
is_equiv_rel phi ->
is_equiv_rel (afterL phi j).
Proof.
  intros phi j [phi_refl [phi_sym phi_tran]].
  repeat split.
- unfold is_reflexive.
  intros x.
  unfold afterL; unfold after.
  case x.
+ intros i.
  case_eq (i =? j); intros ij.
* right; apply beq_nat_true; exact ij.
* unfold former.
  apply phi_refl.
+ intros i.
  apply phi_refl.
- unfold is_symmetric.
  intros x y.
  unfold afterL; unfold after.
  case x, y.
+ case_eq (i =? j); case_eq (i0 =? j); intros i0j; intros ij.
* intros _.
  right.
  apply beq_nat_true; assumption.
* intros [H | H].
    assumption.
  apply beq_nat_false in i0j; contradiction.
* auto.
* unfold former.
  apply phi_sym.
+ case_eq (i =? j); intros ij; auto.
+ case_eq (i0 =? j); intros i0j; auto.
+ apply phi_sym.

- unfold is_transitive.
  intros x y z.
  case x, y, z;
  unfold afterL; unfold after.
+ case_eq (i =? j); case_eq (i0 =? j); intros i0j; intros ij.
* intros [_ [H | H]]; auto.
* case_eq (i1 =? j); intros i1j.
-- intros _.
  right; apply beq_nat_true; assumption.
-- intros [[H1 | H1] H2].
++ unfold inv in H1.
  unfold former in H2.
  apply phi_sym in H2.
  left.
  unfold inv.
  apply (phi_tran _ (X i0) _).
  split; assumption.
++ apply beq_nat_false in i0j. contradiction.
* case_eq (i1 =? j); intros i1j.
-- intros [H _]; assumption.
-- unfold inv; unfold former.
  intros [H1 [H2 | H2]].
++ apply phi_sym in H2.
  apply (phi_tran _ (X' j) _); auto.
++ apply beq_nat_false in i1j. contradiction.
* case_eq (i1 =? j); intros i1j.
-- unfold inv; unfold former.
  intros [H1 H2].
  apply (phi_tran _ (X i0) _); auto.
-- unfold former.
  apply phi_tran.
+ case_eq (i =? j); case_eq (i0 =? j); intros i0j; intros ij.
* intros [[H1 | H1] H2]; assumption.
* intros [[H1 | H1] H2].
-- unfold inv in H1.
  apply phi_sym in H1.
  apply (phi_tran _ (X i0) _).
  split; assumption.
-- apply beq_nat_false in i0j. contradiction.
* unfold inv.
  apply phi_tran.
* unfold former.
  apply phi_tran.
+ case_eq (i =? j); case_eq (i1 =? j); intros i1j; intros ij.
* intros _.
  right; apply beq_nat_true; assumption.
* intros [H1 H2].
  left.
  unfold inv.
  apply phi_sym.
  apply (phi_tran _ (X' i0) _).
  split; assumption.
* intros [H1 H2].
  apply phi_sym in H2.
  unfold inv.
  apply (phi_tran _ (X' i0) _).
  split; assumption.
* unfold former.
  apply phi_tran.
+ case_eq (i =? j); intros ij; apply phi_tran.
+ case_eq (i0 =? j); case_eq (i1 =? j); intros i1j; intros i0j.
* intros [H1 _]; assumption.
* intros [H1 [H2 | H2]].
-- unfold inv in H2.
  apply phi_sym.
  apply (phi_tran _ (X' j) _).
  split; assumption.
-- apply beq_nat_false in i1j. contradiction.
* intros [H1 H2].
  unfold inv in H2.
  apply phi_sym.
  apply (phi_tran _ (X i0) _).
  split; assumption.
* unfold former.
  apply phi_tran.
+ case_eq (i0 =? j); intros i0j.
* intros [H1 H2].
  apply phi_sym in H1.
  apply (phi_tran _ (X' j) _).
  split; assumption.
* apply phi_tran.
+ case_eq (i1 =? j); intros i1j.
* intros [H1 H2].
  apply phi_sym in H2.
  apply phi_sym.
  apply (phi_tran _ (X' i0) _).
  split; assumption.
* apply phi_tran.
+ apply phi_tran.
Qed.
