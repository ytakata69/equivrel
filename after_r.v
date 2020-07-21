Require Import equiv.

Parameter b : guard.
Parameter phi : Rel.
Parameter phi_equiv : is_equiv_rel phi.

Lemma afterR_well_defined :
  lat phi |= b -> forall j,
    ~((exists l1, phi (X j) (X' l1) /\ b l1) /\
       exists l2, ~(phi (X j) (X' l2) <-> b l2)).
Proof.
  intros lat_phi_b j.
  destruct phi_equiv as [eqref [eqsym eqtran]].
  intros [[l1 [pjl1 bl1]] [l2 H2]].
  apply lat_phi_b in bl1.
  apply H2.
  split; intros H.
  - apply bl1.
    apply eqsym in pjl1.
    apply (eqtran _ (X j) _).
    auto.
  - apply bl1 in H.
    apply (eqtran _ (X' l1) _).
    auto.
Qed.

(* another representation of the above lemma *)
Lemma afterR_well_defined'1 :
  lat phi |= b -> forall j,
    (exists l1, phi (X j) (X' l1) /\ b l1) ->
     forall l2, phi (X j) (X' l2) <-> b l2.
Proof.
  intros lat_phi_b j.
  intros el1 l2.
  destruct phi_equiv as [_ [eqsym eqtran]].
  destruct el1 as [l1 [pjl1 bl1]].
  apply lat_phi_b in bl1.
  split; intros H.
  - apply bl1.
    apply eqsym in pjl1.
    apply (eqtran _ (X j) _).
    auto.
  - apply bl1 in H.
    apply (eqtran _ (X' l1) _).
    auto.
Qed.

Lemma afterR_well_defined'2 :
  lat phi |= b -> forall j,
    (exists l1, ~ (phi (X j) (X' l1) <-> b l1)) ->
     forall l2, ~ (phi (X j) (X' l2) /\ b l2).
Proof.
  intros lat_phi_b j.
  intros el1 l2 [pjl2 bl2].
  destruct phi_equiv as [_ [eqsym eqtran]].
  apply lat_phi_b in bl2.
  unfold lat in bl2.
  destruct el1 as [l1 npjl1].
  apply npjl1.
  split; intros H.
  - apply bl2.
    apply eqsym in pjl2.
    apply (eqtran _ (X j) _).
    auto.
  - apply bl2 in H.
    apply (eqtran _ (X' l2) _).
    auto.
Qed.

Parameter theta theta' : assignment.
Parameter phi' : Rel.
Parameter phi'_equiv : is_equiv_rel phi'.

Lemma afterR_exists_core' :
  forall d : D, (theta, d) |= b ->
    forall j l, (theta' j = theta l /\ b l -> theta' j = d) /\
             (~ (theta' j = theta l <-> b l) -> theta' j <> d).
Proof.
  intros d theta_d_b.
  intros j l.
  split.
  - intros [theta_jl bl].
    rewrite theta_jl.
    apply theta_d_b.
    assumption.
  - intros thjl_neq_bl th'j_d.
    apply thjl_neq_bl.
    split; intros H.
    + apply theta_d_b.
      rewrite <- H. assumption.
    + rewrite th'j_d.
      apply theta_d_b in H.
      auto.
Qed.

Parameter theta_phi : (theta', theta) |= phi.

Lemma afterR_exists_core :
  forall d : D, (theta, d) |= b ->
    forall i : nat,
      (theta', update theta i d) |= phi' ->
        forall j l, (phi (X j) (X' l) /\ b l -> phi' (X j) (X' i)) /\
                 (~ (phi (X j) (X' l) <-> b l) -> ~ phi' (X j) (X' i)).
Proof.
  intros d theta_d_b i theta_phi'.
  intros j l.
  split.
  - intros [pjl bl].
    apply theta_phi'.
    apply theta_phi in pjl.
    unfold update.
    rewrite <- beq_nat_refl.
    rewrite pjl.
    apply theta_d_b. assumption.
  - intros pjl_neq_bl p'ji.
    apply pjl_neq_bl.
    apply theta_phi' in p'ji.
    unfold update in p'ji.
    rewrite <- beq_nat_refl in p'ji.
    split; intros H.
    + apply theta_d_b.
      apply theta_phi in H.
      rewrite <- H.
      assumption.
    + apply theta_phi.
      apply theta_d_b in H.
      rewrite H.
      assumption.
Qed.

Lemma deriv_implies_afterR :
  forall (d : D) (i : nat),
    (theta, d) |= b ->
    (theta', update theta i d) |= phi' ->
      afterR phi b i phi'.
Proof.
  intros d i theta_d_b theta_phi'.
  unfold afterR.
  split. (* many cases *)
  { (* former phi' = former phi *)
    apply rel_extensionality.
    intros x y.
    split; intros H.
    - (* -> *)
      case x, y.
      { apply theta_phi.
        apply theta_phi' in H.
        assumption. }
      { discriminate. }
      { discriminate. }
      { assumption. }
    - (* <- *)
      case x, y.
      { apply theta_phi'.
        apply theta_phi in H.
        assumption. }
      { discriminate. }
      { discriminate. }
      { assumption. }
  }
  split.
  { (* lat phi' = after (lat phi) b i *)
    apply rel_extensionality.
    intros x y.
    split; intros H.
    - (* -> *)
      case x, y.
      { unfold after.
        unfold lat in H.
        apply theta_phi' in H.
        unfold update in H.
        case_eq (i0 =? i); intros i0i.
        - rewrite i0i in H.
          case_eq (i1 =? i); intros i1i.
          + right. apply beq_nat_true. assumption.
          + rewrite i1i in H.
            symmetry in H.
            apply theta_d_b in H. auto.
        - rewrite i0i in H.
          case_eq (i1 =? i); intros i1i.
          + rewrite i1i in H.
            apply theta_d_b in H. assumption.
          + rewrite i1i in H.
            unfold lat.
            apply theta_phi. assumption. }
      { discriminate. }
      { discriminate. }
      { assumption. }
    - (* <- *)
      case x, y.
      { unfold lat.
        apply theta_phi'.
        unfold update.
        unfold after in H.
        case_eq (i0 =? i); intros i0i.
        - rewrite i0i in H.
          case_eq (i1 =? i); intros i1i.
          + reflexivity.
          + destruct H as [H | H].
            * symmetry. apply theta_d_b. assumption.
            * apply beq_nat_false in i1i. contradiction.
        - rewrite i0i in H.
          case_eq (i1 =? i); intros i1i.
          + rewrite i1i in H.
            apply theta_d_b in H. assumption.
          + rewrite i1i in H.
            unfold lat in H.
            apply theta_phi in H. assumption. }
      { discriminate. }
      { discriminate. }
      { assumption. }
  }
  split.
  { apply (afterR_exists_core _ theta_d_b _ theta_phi'). }
  { intros j l nli.
    split; intros H.
    - apply theta_phi'.
      apply theta_phi in H.
      unfold update.
      case_eq (l =? i); intros li.
      + apply beq_nat_true in li. contradiction.
      + assumption.
    - apply theta_phi.
      apply theta_phi' in H.
      unfold update in H.
      case_eq (l =? i); intros li.
      + apply beq_nat_true in li. contradiction.
      + rewrite li in H. assumption.
  }
Qed.
