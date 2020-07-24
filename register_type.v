Require Import equiv.

Parameter b : guard.
Parameter theta : assignment.
Parameter gamma : Rel.
Parameter gamma_equiv : is_equiv_rel gamma.

Lemma type_guarantees_applicability :
  theta |= gamma -> gamma |= b <-> exists d, (theta , d) |= b.
Proof.
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

Parameter gamma' : Rel.
Parameter gamma'_equiv : is_equiv_rel gamma'.

Lemma type_uniqueness :
  theta |= gamma /\ theta |= gamma' -> gamma = gamma'.
Proof.
  unfold models. unfold assignment_models_rel.
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
