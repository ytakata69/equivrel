Require Import equiv.

Parameter b : guard.
Parameter i : nat.
Parameter gamma : Rel.
Parameter gamma_equiv : is_equiv_rel gamma.

(* "after" is an equivalence relation *)

Lemma after_is_reflexive :
  is_reflexive (after gamma b i).
Proof.
  unfold is_reflexive.
  intros x.
  case x; intros i0.
  - (* x = (X i0) *)
    unfold after.
    case_eq (i0 =? i); intros Hi0.
    + (* Hi: (i0 =? i) = true *)
      right. apply beq_nat_true. assumption.
    + (* Hi: (i0 =? i) = false *)
      destruct gamma_equiv as [gref _].
      apply gref.
  - (* x = (X' i0) *)
    unfold after. reflexivity.
Qed.

Lemma after_is_symmetric :
  is_symmetric (after gamma b i).
Proof.
  unfold is_symmetric.
  intros x y Ha.
  case x, y.
  - (* x = (X i0), y = (X i1) *)
    unfold after.
    case_eq (i1 =? i); intros Hi1.
    + (* Hi1: (i1 =? i) = true *)
      case_eq (i0 =? i); intros Hi0.
      * (* Hi0: (i0 =? i) = true *)
        right. apply beq_nat_true. assumption.
      * (* Hi0: (i0 =? i) = false *)
        unfold after in Ha.
        rewrite Hi0 in Ha.
        rewrite Hi1 in Ha.
        auto.
    + (* Hi1: (i1 =? i) = false *)
      unfold after in Ha.
      case_eq (i0 =? i); intros Hi0.
      * (* Hi0: (i0 =? i) = true *)
        rewrite Hi0 in Ha.
        destruct Ha as [Ha | Ha].
          assumption.
        apply beq_nat_false in Hi1.
        contradiction.
      * (* Hi0: (i0 =? i) = false *)
        rewrite Hi0 in Ha.
        rewrite Hi1 in Ha.
        destruct gamma_equiv as [_ [gsym _]].
        apply gsym. assumption.
  - (* x = (X i0), y = (X' i1) *)
    unfold after. auto.
  - (* x = (X' i0), y = (X i1) *)
    unfold after. auto.
  - (* x = (X' i0), y = (X' i1) *)
    unfold after.
    case_eq (i0 =? i1); intros Hi.
    + (* Hi: (i0 =? i1) = true *)
      apply beq_nat_true in Hi. rewrite Hi. reflexivity.
    + (* Hi: (i0 =? i1) = false *)
      apply beq_nat_false in Hi. auto.
Qed.

Lemma after_is_transitive :
  gamma |= b -> is_transitive (after gamma b i).
Proof.
  intros gamma_b.
  unfold is_transitive.
  intros x y z [Haxy Hayz].
  case x, y, z.
  - (* x = (X i0), y = (X i1), z = (X i2) *)
    unfold after.
    case_eq (i0 =? i); intros Hi0.
    + (* Hi0: (i0 =? i) = true *)
      case_eq (i2 =? i); intros Hi2.
      * (* Hi2: (i2 =? i) = true *)
        right. apply beq_nat_true. assumption.
      * (* Hi2: (i2 =? i) = false *)
        case_eq (i1 =? i); intros Hi1.
          unfold after in Hayz.
          rewrite Hi1 in Hayz.
          assumption.
        (* Hi1: (i1 =? i) = false *)
        unfold after in Haxy.
        rewrite Hi0 in Haxy.
        destruct Haxy as [bi1 | Hi1'].
          unfold after in Hayz.
          rewrite Hi1 in Hayz.
          rewrite Hi2 in Hayz.
          apply gamma_b in Hayz.
            left. assumption.
          assumption.
        apply beq_nat_false in Hi1.
        contradiction.
    + (* Hi0: (i0 =? i) = false *)
      case_eq (i2 =? i); intros Hi2.
      * (* Hi2: (i2 =? i) = true *)
        unfold after in Haxy.
        rewrite Hi0 in Haxy.
        case_eq (i1 =? i); intros Hi1.
          rewrite Hi1 in Haxy. assumption.
        unfold after in Hayz.
        rewrite Hi1 in Haxy.
        rewrite Hi1 in Hayz.
        rewrite Hi2 in Hayz.
        apply gamma_b in Hayz.
        apply Hayz.
        destruct gamma_equiv as [_ [gsym _]].
        apply gsym in Haxy.
        assumption.
      * (* Hi2: (i2 =? i) = false *)
        unfold after in Haxy.
        rewrite Hi0 in Haxy.
        case_eq (i1 =? i); intros Hi1.
          rewrite Hi1 in Haxy.
          apply gamma_b.
            assumption.
          unfold after in Hayz.
          rewrite Hi1 in Hayz.
          destruct Hayz as [bi2 | Hi2'].
            assumption.
          apply beq_nat_false in Hi2.
          contradiction.
        rewrite Hi1 in Haxy.
        unfold after in Hayz.
        rewrite Hi1 in Hayz.
        rewrite Hi2 in Hayz.
        destruct gamma_equiv as [_ [_ gtran]].
        apply (gtran _ (X i1) _).
        auto.
  - (* x = (X i0), y = (X i1), z = (X' i2) *)
    unfold after in Hayz. discriminate.
  - (* x = (X i0), y = (X' i1), z = (X i2) *)
    unfold after in Hayz. discriminate.
  - (* x = (X i0), y = (X' i1), z = (X' i2) *)
    unfold after in Haxy. discriminate.
  - (* x = (X' i0), y = (X i1), z = (X i2) *)
    unfold after in Haxy. discriminate.
  - (* x = (X' i0), y = (X i1), z = (X' i2) *)
    unfold after in Haxy. discriminate.
  - (* x = (X' i0), y = (X' i1), z = (X i2) *)
    unfold after in Hayz. discriminate.
  - (* x = (X' i0), y = (X' i1), z = (X' i2) *)
    unfold after.
    unfold after in Haxy.
    unfold after in Hayz.
    rewrite Haxy.
    assumption.
Qed.

Lemma after_is_equiv_rel :
  gamma |= b -> is_equiv_rel (after gamma b i).
Proof.
  intros gamma_b.
  unfold is_equiv_rel.
  split.
    apply after_is_reflexive.
  split.
    apply after_is_symmetric.
    apply after_is_transitive. assumption.
Qed.


Lemma after_is_simpl_rel : (* a relation over (X i) *)
  is_simpl_rel (after gamma b i).
Proof.
  unfold is_simpl_rel.
  intros xi xj.
  case xi, xj.
  - auto.
  - unfold after. reflexivity.
  - unfold after. reflexivity.
  - unfold after. reflexivity.
Qed.

Parameter theta : assignment.

Lemma updated_assignment_models_after :
  forall d,
    theta |= gamma /\ (theta, d) |= b -> update theta i d |= after gamma b i.
Proof.
  intros d [theta_gamma theta_d_b].
  unfold models. unfold assignment_models_rel.
  split.
    apply after_is_simpl_rel.
  intros i0 j.
  split; intros H.
  - (* H: update theta i d i0 = update theta i d j *)
    unfold after.
    case_eq (i0 =? i); intros Hi0.
    + (* Hi0: (i0 =? i) = true *)
      unfold update in H.
      rewrite Hi0 in H.
      case_eq (j =? i); intros Hj.
      * (* Hj: (j =? i) = true *)
        apply beq_nat_true in Hj. auto.
      * (* Hj: (j =? i) = false *)
        left. apply theta_d_b.
        rewrite Hj in H.
        auto.
    + (* Hi0: (i0 =? i) = false *)
      unfold update in H.
      rewrite Hi0 in H.
      case_eq (j =? i); intros Hj.
      * (* Hj: (j =? i) = true *)
        rewrite Hj in H.
        apply theta_d_b. assumption.
      * (* Hj: (j =? i) = false *)
        rewrite Hj in H.
        apply theta_gamma. assumption.
  - (* H: after gamma b i (X i0) (X j) *)
    unfold update.    
    case_eq (i0 =? i); intros Hi0.
    + (* Hi0: (i0 =? i) = true *)
      unfold after in H.
      rewrite Hi0 in H.
      destruct H as [bj | ji].
        apply theta_d_b in bj.
        rewrite bj.
        case (j =? i). trivial. trivial.
      rewrite ji.
      rewrite <- beq_nat_refl.
      reflexivity.
    + (* Hi0: (i0 =? i) = false *)
      unfold after in H.
      rewrite Hi0 in H.
      case_eq (j =? i); intros Hj.
      * (* Hj: (j =? i) = true *)
        rewrite Hj in H.
        apply theta_d_b. assumption.
      * (* Hj: (j =? i) = false *)      
        rewrite Hj in H.
        apply theta_gamma. assumption.
Qed.
