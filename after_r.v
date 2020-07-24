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
  repeat split. (* many cases *)
  - (* former phi' = former phi *)
    apply rel_extensionality.
    intros x y.
    split; intros H.
  + (* -> *)
    case x, y; try auto.
    { apply theta_phi.
      apply theta_phi' in H.
      assumption. }
  + (* <- *)
    case x, y; try auto.
    { apply theta_phi'.
      apply theta_phi in H.
      assumption. }
  - (* lat phi' = after (lat phi) b i *)
    apply rel_extensionality.
    intros x y.
    split; intros H.
  + (* -> *)
    case x, y; try auto.
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
  + (* <- *)
    case x, y; try auto.
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
  - (* phi (X j) (X' l) /\ b l <-> phi' (X j) (X' i) *)
    apply (afterR_exists_core _ theta_d_b _ theta_phi').
  - apply (afterR_exists_core _ theta_d_b _ theta_phi').
  - (* phi (X j) (X' l) <-> phi' (X j) (X' l) *)
    case_eq (l =? i); intros li.
  + apply beq_nat_true in li. contradiction.
  + intros phi_jl.
    apply theta_phi'.
    unfold update.
    rewrite li.
    apply theta_phi.
    assumption.
  - case_eq (l =? i); intros li.
  + apply beq_nat_true in li. contradiction.
  + intros phi'_jl.
    apply theta_phi' in phi'_jl.
    unfold update in phi'_jl.
    rewrite li in phi'_jl.
    apply theta_phi.
    assumption.
Qed.


Lemma elim_former :
  forall phi i j,
  former phi (X i) (X j) = phi (X i) (X j).
Proof.
  intros phi i j.
  unfold former.
  reflexivity.
Qed.

Lemma elim_lat :
  forall phi i j,
  lat phi (X i) (X j) = phi (X' i) (X' j).
Proof.
  intros phi i j.
  unfold lat.
  reflexivity.
Qed.

Axiom classic : forall P : Prop, ~ ~ P -> P.

Lemma phi_ji_or_not :
  forall (phi : Rel) (i : nat),
    (exists j, phi (X j) (X' i)) \/ forall j, ~ phi (X j) (X' i).
Proof.
  intros phi i.
  apply classic.
  intros H. apply H. right.
  intros j p. apply H. left.
  exists j. assumption.
Qed.

Lemma contrapositive : forall P Q : Prop, (~ P -> ~ Q) -> Q -> P.
Proof.
  intros P Q npnq q.
  apply classic.
  intros np.
  apply npnq. assumption. assumption.
Qed.

Lemma afterR_implies_deriv :
  lat phi |= b ->
  forall i : nat,
  afterR phi b i phi' ->
    exists d : D, (theta, d) |= b /\ (theta', update theta i d) |= phi'.
Proof.
  intros lat_phi_b.
  intros i phi'_in_after.
  unfold afterR in phi'_in_after.
  destruct phi'_in_after as [fo [la [Hi Ho]]].
  destruct phi_equiv  as [_ [phi_sym _]].
  destruct phi'_equiv as [phi'_refl [phi'_sym phi'_tran]].
  assert (phi_phi': forall i j, phi (X i) (X j) <-> phi' (X i) (X j)).
  {
    intros l j.
    split; intros H.
    - rewrite <- elim_former.
      rewrite fo.
      rewrite -> elim_former. assumption.
    - rewrite <- elim_former.
      rewrite <- fo.
      rewrite -> elim_former. assumption.
  }
  destruct (b_is_empty_or_not b) as [b_empty | [j bj]].
  - (* b_empty: forall i, ~ b i *)
    destruct (phi_ji_or_not phi' i) as [[j phi'_ji] | not_phi'_ji].
  + (* phi'_ji: phi' (X j) (X' i) *)
    exists (theta' j).
    split.
  * (* theta, theta' j) |= b *)
    unfold models. unfold assignmentD_models_guard.
    intros l.
    split; intros H.
  -- (* theta l = theta' j -> b l *)
    apply theta_phi in H.
    destruct (Hi j l) as [_ Hi1].
    elimtype False.
    apply Hi1.
  ++ (* ~ (phi (X j) (X' l) <-> b l) *)
    intros pjl_bl.
    apply phi_sym in H.
    rewrite pjl_bl in H.
    apply b_empty in H. contradiction.
  ++ (* phi' (X j) (X' i) *)
    assumption.
  -- (* b l -> theta l = theta' j *)
    apply b_empty in H. contradiction.

  * (* (theta', update theta i (theta' j)) |= phi' *)
    unfold models. unfold two_assignments_model_rel.
    intros i0 j0.
    split.
  { (* theta' i0 = theta' j0 <-> phi' (X i0) (X j0) *)
    split; intros H.
  - (* -> *)
    apply theta_phi in H.
    apply phi_phi'. assumption.
  - (* <- *)
    apply theta_phi.
    apply phi_phi'. assumption.
  }
  split.
  { (* update theta i (theta' j) i0 = update theta i (theta' j) j0
       <-> phi' (X' i0) (X' j0) *)
    unfold update.
    split; intros H.
  - (* -> *)
    rewrite <- elim_lat.
    rewrite la.
    unfold after.
    case_eq (i0 =? i); intros i0i.
  + case_eq (j0 =? i); intros j0i.
  * right. apply beq_nat_true. assumption.
  * rewrite i0i in H. rewrite j0i in H.
    apply theta_phi in H.
    destruct (Hi j j0) as [_ Hi1].
    elimtype False.
    apply Hi1.
      intros pjj0_bj0.
      apply pjj0_bj0 in H.
      apply b_empty in H. contradiction.
    assumption.
  + rewrite i0i in H.
    case_eq (j0 =? i); intros j0i.
  * rewrite j0i in H.
    apply theta_phi in H.
    apply phi_sym in H.
    destruct (Hi j i0) as [_ Hi1].
    elimtype False.
    apply Hi1.
      intros pji0_bi0.
      apply pji0_bi0 in H.
      apply b_empty in H. contradiction.
    assumption.
  * rewrite j0i in H.
    unfold lat.
    apply theta_phi.
    assumption.
  - (* <- *)
    rewrite <- elim_lat in H.
    rewrite la in H.
    unfold after in H.
    case_eq (i0 =? i); intros i0i.
  + case_eq (j0 =? i); intros j0i.
  * reflexivity.
  * rewrite i0i in H.
    destruct H as [H | H].
      apply b_empty in H. contradiction.
    apply beq_nat_false in j0i. contradiction.
  + rewrite i0i in H.
    case_eq (j0 =? i); intros j0i.
  * rewrite j0i in H.
    apply b_empty in H. contradiction.
  * rewrite j0i in H.
    unfold lat in H.
    apply theta_phi. assumption.
  }
  split.
  { (* theta' i0 = update theta i (theta' j) j0 <-> phi' (X i0) (X' j0) *)
    split; intros H.
  - (* -> *)
    unfold update in H.
    case_eq (j0 =? i); intros j0i.
  + rewrite j0i in H.
    apply beq_nat_true in j0i.
    rewrite j0i.
    apply theta_phi in H.
    apply phi_phi' in H.
    apply (phi'_tran _ (X j) _).
    auto.
  + rewrite j0i in H.
    apply theta_phi in H.
    apply Ho.
      apply beq_nat_false. assumption.
    assumption.
  - (* <- *)
    unfold update.
    case_eq (j0 =? i); intros j0i.
  + apply theta_phi.
    apply phi_phi'.
    apply (phi'_tran _ (X' i) _).
    apply beq_nat_true in j0i.
    rewrite j0i in H.
    apply phi'_sym in phi'_ji.
    auto.
  + apply theta_phi.
    apply Ho.
      apply beq_nat_false. assumption.
    assumption.
  }
  { (* update theta i (theta' j) i0 = theta' j0 <-> phi' (X' i0) (X j0) *)
    split; intros H.
  - (* -> *)
    unfold update in H.
    case_eq (i0 =? i); intros i0i.
  + rewrite i0i in H.
    apply beq_nat_true in i0i.
    rewrite i0i.
    apply theta_phi in H.
    apply phi_phi' in H.
    apply (phi'_tran _ (X j) _).
    auto.
  + rewrite i0i in H.
    apply theta_phi in H.
    apply phi'_sym.
    apply Ho.
      apply beq_nat_false. assumption.
    apply phi_sym. assumption.
  - (* <- *)
    unfold update.
    case_eq (i0 =? i); intros i0i.
  + apply theta_phi.
    apply phi_phi'.
    apply (phi'_tran _ (X' i) _).
    apply beq_nat_true in i0i.
    rewrite i0i in H.
    apply phi'_sym in phi'_ji.
    auto.
  + apply theta_phi.
    apply phi_sym.
    apply Ho.
      apply beq_nat_false. assumption.
    auto.
  }
  + (* not_phi'_ji: forall j, ~ phi' (X j) (X' i) *)
    destruct (outside_data_exists' theta theta') as [d [theta_nd theta'_nd]].
    exists d.
    split.
  * (* theta, d) |= b *)
    unfold models. unfold assignmentD_models_guard.
    intros l.
    split; intros H.
  -- (* theta l = d -> b l *)
    apply theta_nd in H.
    contradiction.
  -- (* b l -> theta l = d *)
    apply b_empty in H. contradiction.

  * (* (theta', update theta i d) |= phi' *)
    unfold models. unfold two_assignments_model_rel.
    intros i0 j0.
    split.
  { (* theta' i0 = theta' j0 <-> phi' (X i0) (X j0) *)
    split; intros H.
  - (* -> *)
    apply theta_phi in H.
    apply phi_phi'. assumption.
  - (* <- *)
    apply theta_phi.
    apply phi_phi'. assumption.
  }
  split.
  { (* update theta i d i0 = update theta i d j0 <-> phi' (X' i0) (X' j0) *)
    unfold update.
    split; intros H.
  - (* -> *)
    rewrite <- elim_lat.
    rewrite la.
    unfold after.
    case_eq (i0 =? i); intros i0i.
  + case_eq (j0 =? i); intros j0i.
  * right. apply beq_nat_true. assumption.
  * rewrite i0i in H. rewrite j0i in H.
    symmetry in H. apply theta_nd in H. contradiction.
  + rewrite i0i in H.
    case_eq (j0 =? i); intros j0i.
  * rewrite j0i in H.
    apply theta_nd in H. contradiction.
  * rewrite j0i in H.
    unfold lat.
    apply theta_phi.
    assumption.
  - (* <- *)
    rewrite <- elim_lat in H.
    rewrite la in H.
    unfold after in H.
    case_eq (i0 =? i); intros i0i.
  + case_eq (j0 =? i); intros j0i.
  * reflexivity.
  * rewrite i0i in H.
    destruct H as [H | H].
      apply b_empty in H. contradiction.
    apply beq_nat_false in j0i. contradiction.
  + rewrite i0i in H.
    case_eq (j0 =? i); intros j0i.
  * rewrite j0i in H.
    apply b_empty in H. contradiction.
  * rewrite j0i in H.
    unfold lat in H.
    apply theta_phi. assumption.
  }
  split.
  { (* theta' i0 = update theta i d j0 <-> phi' (X i0) (X' j0) *)
    split; intros H.
  - (* -> *)
    unfold update in H.
    case_eq (j0 =? i); intros j0i.
  + rewrite j0i in H.
    apply theta'_nd in H. contradiction.
  + rewrite j0i in H.
    apply theta_phi in H.
    apply Ho.
      apply beq_nat_false. assumption.
    assumption.
  - (* <- *)
    unfold update.
    case_eq (j0 =? i); intros j0i.
  + apply beq_nat_true in j0i.
    rewrite j0i in H.
    apply not_phi'_ji in H.
    contradiction.
  + apply theta_phi.
    apply (Ho i0 j0).
      apply beq_nat_false. assumption.
    assumption.
  }
  { (* update theta i d i0 = theta' j0 <-> phi' (X' i0) (X j0) *)
    split; intros H.
  - (* -> *)
    unfold update in H.
    case_eq (i0 =? i); intros i0i.
  + rewrite i0i in H.
    symmetry in H. apply theta'_nd in H. contradiction.
  + rewrite i0i in H.
    apply phi'_sym.
    apply (Ho j0 i0).
      apply beq_nat_false. assumption.
    apply theta_phi. symmetry. assumption.
  - (* <- *)
    unfold update.
    case_eq (i0 =? i); intros i0i.
  + apply beq_nat_true in i0i.
    rewrite i0i in H.
    apply phi'_sym in H.
    apply not_phi'_ji in H. contradiction.
  + apply theta_phi.
    apply phi_sym.
    apply (Ho j0 i0).
      apply beq_nat_false. assumption.
    auto.
  }

  - (* bj: b j *)
    exists (theta j).
    split.
  * (* theta, theta j) |= b *)
    unfold models. unfold assignmentD_models_guard.
    intros l.
    split; intros H.
  -- (* theta l = theta' j -> b l *)
    apply theta_phi in H.
    apply phi_sym in H.
    rewrite <- elim_lat in H.
    apply lat_phi_b in H.
      assumption.
    assumption.
  -- (* b l -> theta l = theta j *)
    apply theta_phi.
    apply lat_phi_b.
      assumption.
    assumption.
  * (* (theta', update theta i (theta j)) |= phi' *)
    unfold models. unfold two_assignments_model_rel.
    intros i0 j0.
    split.
  { (* theta' i0 = theta' j0 <-> phi' (X i0) (X j0) *)
    split; intros H.
  - (* -> *)
    apply theta_phi in H.
    apply phi_phi'. assumption.
  - (* <- *)
    apply theta_phi.
    apply phi_phi'. assumption.
  }
  split.
  { (* update theta i (theta j) i0 = update theta i (theta j) j0
       <-> phi' (X' i0) (X' j0) *)
    unfold update.
    split; intros H.
  - (* -> *)
    case_eq (i0 =? i); intros i0i.
  + case_eq (j0 =? i); intros j0i.
  * apply beq_nat_true in i0i. rewrite i0i.
    apply beq_nat_true in j0i. rewrite j0i.
    apply phi'_refl.
  * rewrite i0i in H. rewrite j0i in H.
    rewrite <- elim_lat.
    rewrite la.
    unfold after.
    rewrite i0i.
    apply theta_phi in H.
    apply lat_phi_b in H.
      auto.
    assumption.
  + rewrite <- elim_lat.
    rewrite la.
    unfold after.
    rewrite i0i.
    rewrite i0i in H.
    case_eq (j0 =? i); intros j0i.
  * rewrite j0i in H.
    symmetry in H.
    apply theta_phi in H.
    apply lat_phi_b in H.
      assumption.
    assumption.
  * rewrite j0i in H.
    apply theta_phi in H.
    rewrite elim_lat.
    assumption.
  - (* <- *)
    rewrite <- elim_lat in H.
    rewrite la in H.
    unfold after in H.
    case_eq (i0 =? i); intros i0i.
  + case_eq (j0 =? i); intros j0i.
  * reflexivity.
  * rewrite i0i in H.
    destruct H as [H | H].
      apply theta_phi.
      apply lat_phi_b.
        assumption.
      assumption.
    apply beq_nat_false in j0i. contradiction.
  + rewrite i0i in H.
    case_eq (j0 =? i); intros j0i.
  * rewrite j0i in H.
    apply theta_phi.
    apply lat_phi_b.
      assumption.
    assumption.
  * rewrite j0i in H.
    unfold lat in H.
    apply theta_phi. assumption.
  }
  split.
  { (* theta' i0 = update theta i (theta j) j0 <-> phi' (X i0) (X' j0) *)
    split; intros H.
  - (* -> *)
    unfold update in H.
    case_eq (j0 =? i); intros j0i.
  + rewrite j0i in H.
    apply beq_nat_true in j0i.
    rewrite j0i.
    destruct (Hi i0 j) as [Hi0 _].
    apply Hi0.
    split.
    * apply theta_phi. assumption.
    * assumption.
  + rewrite j0i in H.
    apply theta_phi in H.
    apply Ho.
      apply beq_nat_false. assumption.
    assumption.
  - (* <- *)
    unfold update.
    case_eq (j0 =? i); intros j0i.
  + apply beq_nat_true in j0i.
    rewrite j0i in H.
    destruct (Hi i0 j) as [_ Hi1].
    apply (contrapositive (phi (X i0) (X' j) <-> b j) _) in Hi1; try auto.
    apply Hi1 in bj.
    apply theta_phi.
    assumption.
  + apply theta_phi.
    apply (Ho i0 j0).
      apply beq_nat_false. assumption.
    assumption.
  }
  { (* update theta i (theta j) i0 = theta' j0 <-> phi' (X' i0) (X j0) *)
    split; intros H.
  - (* -> *)
    unfold update in H.
    case_eq (i0 =? i); intros i0i.
  + rewrite i0i in H.
    apply beq_nat_true in i0i.
    rewrite i0i.
    destruct (Hi j0 j) as [Hi0 _].
    apply phi'_sym.
    apply Hi0.
    split.
    * apply theta_phi. symmetry. assumption.
    * assumption.
  + rewrite i0i in H.
    apply theta_phi in H.
    apply phi'_sym.
    apply Ho.
      apply beq_nat_false. assumption.
    apply phi_sym. assumption.
  - (* <- *)
    unfold update.
    case_eq (i0 =? i); intros i0i.
  + apply beq_nat_true in i0i.
    rewrite i0i in H.
    destruct (Hi j0 j) as [_ Hi1].
    apply (contrapositive (phi (X j0) (X' j) <-> b j) _) in Hi1; try auto.
    apply Hi1 in bj.
    apply theta_phi.
    apply phi_sym.
    assumption.
  + apply theta_phi.
    apply phi_sym.
    apply (Ho j0 i0).
      apply beq_nat_false. assumption.
    apply phi'_sym.
    assumption.
  }
Qed.
