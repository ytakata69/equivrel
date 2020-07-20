(* sketch on equivalence relation *)

Require Import Bool Arith.

Section EquivRel.

(* assignments *)

Variable D : Set.
Definition assignment := nat -> D.

Definition update (theta : assignment) (i : nat) (d : D) (j : nat) : D :=
  if j =? i then d else theta j.

(* guard *)

Definition guard := nat -> Prop.  (* a subset of nat *)

(* equivalence relations *)

Inductive register :=
  | X  (i : nat)
  | X' (i : nat).

Definition Rel := register -> register -> Prop.

Definition is_reflexive  (phi : Rel) : Prop := forall x, phi x x.
Definition is_symmetric  (phi : Rel) : Prop := forall x y, phi x y -> phi y x.
Definition is_transitive (phi : Rel) : Prop :=
  forall x y z, phi x y /\ phi y z -> phi x z.
Definition is_equiv_rel   (phi : Rel) : Prop :=
  is_reflexive phi /\ is_symmetric phi /\ is_transitive phi.

Definition lat (phi : Rel) (xi xj : register) : Prop :=
  match xi, xj with
  | (X i), (X j) => phi (X' i) (X' j)
  | x, y => x = y
  end.

Definition after (gamma : Rel) (b : guard) (i : nat) (xi xj : register) :=
  match xi, xj with
  | (X j), (X l) => if j =? i then b l \/ l = i else
                    if l =? i then b j          else gamma (X j) (X l)
  | x, y => x = y
  end.

(* an equivalence relation over (X i)'s *)
Definition is_simpl_rel (phi : Rel) :=
  forall xi xj : register,
    match xi, xj with
    | (X i), (X j) => True
    | x, y => phi x y <-> x = y
    end.

Axiom rel_extensionality :
  forall phi phi' : Rel,
    (forall xi xj, phi xi xj <-> phi' xi xj) -> phi = phi'.

(* models *)

Class Models (A B : Type) := models : A -> B -> Prop.
Notation "S '|=' T" := (models S T) (at level 59).

Instance rel_models_guard : Models Rel guard :=
  { models phi b := forall i, b i ->
                    forall j, b j <-> phi (X i) (X j) }.
Instance assignment_models_rel : Models assignment Rel :=
  { models theta phi := is_simpl_rel phi /\
                        forall i j, theta i = theta j <-> phi (X i) (X j) }.
Instance assignmentD_models_guard : Models (assignment * D) guard :=
  { models theta_d b :=
      match theta_d with
      | (theta, d) => forall i, theta i = d <-> b i
      end }.

(* lemmas *)

Variables b : guard.

Section AfterIsEquivRel.

Variable i : nat.
Variable gamma : Rel.
Hypothesis gamma_equiv : is_equiv_rel gamma.

Lemma after_is_reflexive :
  is_reflexive (after gamma b i).
Proof.
  unfold is_reflexive.
  intros x.
  case x; intros i0.
  - (* x = (X i0) *)
    assert (Hi0: (i0 =? i) = true \/ (i0 =? i) = false).
      case (i0 =? i). auto. auto.
    destruct Hi0 as [Hi0 | Hi0].
    + (* Hi: (i0 =? i) = true *)
      unfold after. rewrite Hi0.
      right. apply Nat.eqb_eq. assumption.
    + (* Hi: (i0 =? i) = false *)
      unfold after.
      rewrite Hi0.
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
    assert (Hi1: (i1 =? i) = true \/ (i1 =? i) = false).
      case (i1 =? i). auto. auto.
    destruct Hi1 as [Hi1 | Hi1].
    + (* Hi1: (i1 =? i) = true *)
      unfold after. rewrite Hi1.
      assert (Hi0: (i0 =? i) = true \/ (i0 =? i) = false).
        case (i0 =? i). auto. auto.
      destruct Hi0 as [Hi0 | Hi0].
      * (* Hi0: (i0 =? i) = true *)
        right. apply Nat.eqb_eq. assumption.
      * (* Hi0: (i0 =? i) = false *)
        unfold after in Ha.
        rewrite Hi0 in Ha.
        rewrite Hi1 in Ha.
        auto.
    + (* Hi1: (i1 =? i) = false *)
      unfold after.
      rewrite Hi1.
      assert (Hi0: (i0 =? i) = true \/ (i0 =? i) = false).
        case (i0 =? i). auto. auto.
      destruct Hi0 as [Hi0 | Hi0].
      * (* Hi0: (i0 =? i) = true *)
        rewrite Hi0.
        unfold after in Ha.
        rewrite Hi0 in Ha.
        destruct Ha as [Ha | Ha].
          assumption.
        apply Nat.eqb_neq in Hi1.
        apply Hi1 in Ha. case Ha.
      * (* Hi0: (i0 =? i) = false *)
        rewrite Hi0.
        unfold after in Ha.
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
    assert (Hi: (i0 =? i1) = true \/ (i0 =? i1) = false).
      case (i0 =? i1). auto. auto.
    destruct Hi as [Hi | Hi].
    + (* Hi: (i0 =? i1) = true *)
      apply Nat.eqb_eq in Hi. rewrite Hi. reflexivity.
    + (* Hi: (i0 =? i1) = false *)
      apply Nat.eqb_neq in Hi. auto.
Qed.

Lemma after_is_transitive :
  gamma |= b -> is_transitive (after gamma b i).
Proof.
  intros gamma_b.
  unfold is_transitive.
  intros x y z [Haxy Hayz].
  case x, y, z.
  - (* x = (X i0), y = (X i1), z = (X i2) *)
    assert (Hi0: (i0 =? i) = true \/ (i0 =? i) = false).
      case (i0 =? i). auto. auto.
    destruct Hi0 as [Hi0 | Hi0].
    + (* Hi0: (i0 =? i) = true *)
      unfold after.
      rewrite Hi0.
      assert (Hi2: (i2 =? i) = true \/ (i2 =? i) = false).
        case (i2 =? i). auto. auto.
      destruct Hi2 as [Hi2 | Hi2].
      * (* Hi2: (i2 =? i) = true *)
        right. apply Nat.eqb_eq. assumption.
      * (* Hi2: (i2 =? i) = false *)
        assert (Hi1: (i1 =? i) = true \/ (i1 =? i) = false).
          case (i1 =? i). auto. auto.
        destruct Hi1 as [Hi1 | Hi1].
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
        apply Nat.eqb_neq in Hi1.
        apply Hi1 in Hi1'. case Hi1'.
    + (* Hi0: (i0 =? i) = false *)
      unfold after.
      rewrite Hi0.
      assert (Hi2: (i2 =? i) = true \/ (i2 =? i) = false).
        case (i2 =? i). auto. auto.
      destruct Hi2 as [Hi2 | Hi2].
      * (* Hi2: (i2 =? i) = true *)
        rewrite Hi2.
        unfold after in Haxy.
        rewrite Hi0 in Haxy.
        assert (Hi1: (i1 =? i) = true \/ (i1 =? i) = false).
          case (i1 =? i). auto. auto.
        destruct Hi1 as [Hi1 | Hi1].
          rewrite Hi1 in Haxy. assumption.
        unfold after in Hayz.
        rewrite Hi1 in Haxy.
        rewrite Hi1 in Hayz.
        rewrite Hi2 in Hayz.
        apply gamma_b in Hayz.
        destruct gamma_equiv as [_ [gsym _]].
        apply gsym in Haxy.
        apply Hayz in Haxy.
        assumption.
      * (* Hi2: (i2 =? i) = false *)
        rewrite Hi2.
        unfold after in Haxy.
        rewrite Hi0 in Haxy.
        assert (Hi1: (i1 =? i) = true \/ (i1 =? i) = false).
          case (i1 =? i). auto. auto.
        destruct Hi1 as [Hi1 | Hi1].
          rewrite Hi1 in Haxy.
          apply gamma_b.
            assumption.
          unfold after in Hayz.
          rewrite Hi1 in Hayz.
          destruct Hayz as [bi2 | Hi2'].
            assumption.
          apply Nat.eqb_neq in Hi2.
          apply Hi2 in Hi2'. case Hi2'.
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

End AfterIsEquivRel.


Section TypeGuaranteesApplicability.

Variable theta : assignment.
Variable gamma : Rel.
Hypothesis gamma_equiv : is_equiv_rel gamma.

(* assumptions *)
(* note: b_is_empty_or_not can be proved under the classical logic. *)
Definition b_is_empty_or_not := (forall i, ~ b i) \/ exists i, b i.
Definition outside_data_exists := exists d : D, forall i, theta i <> d.

Lemma type_guarantees_applicability :
  b_is_empty_or_not -> outside_data_exists ->
  theta |= gamma -> gamma |= b <-> exists d, (theta , d) |= b.
Proof.
  intros B_is_empty_or_not Outside_data_exists theta_gamma.
  destruct gamma_equiv as [gref [gsym gtran]].
  split; intros gamma_b.
  - destruct B_is_empty_or_not as [b_empty | [i1 bi1]].
    + destruct Outside_data_exists as [dd dd_neq].
      exists dd.
      unfold models. unfold assignmentD_models_guard.
      intros i0.
      split; intros H'.
      * apply dd_neq in H'. case H'.
      * apply b_empty in H'. case H'.
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

Lemma after_is_simpl_rel :
  forall i, is_simpl_rel (after gamma b i).
Proof.
  intros i.
  unfold is_simpl_rel.
  intros xi xj.
  case xi, xj.
  - auto.
  - unfold after. reflexivity.
  - unfold after. reflexivity.
  - unfold after. reflexivity.
Qed.

Lemma updated_assignment_models_after :
  forall d, forall i,
    theta |= gamma /\ (theta, d) |= b -> update theta i d |= after gamma b i.
Proof.
  intros d i [theta_gamma theta_d_b].
  unfold models. unfold assignment_models_rel.
  split.
    apply after_is_simpl_rel.
  intros i0 j.
  split; intros H.
  - (* H: update theta i d i0 = update theta i d j *)
    unfold after.
    assert (Hi0: (i0 =? i) = true \/ (i0 =? i) = false).
      case (i0 =? i). auto. auto.
    destruct Hi0 as [Hi0 | Hi0].
    + (* Hi0: (i0 =? i) = true *)
      rewrite Hi0.
      unfold update in H.
      rewrite Hi0 in H.
      assert (Hj: (j =? i) = true \/ (j =? i) = false).
        case (j =? i). auto. auto.
      destruct Hj as [Hj | Hj].
      * (* Hj: (j =? i) = true *)
        rewrite Nat.eqb_eq in Hj. auto.
      * (* Hj: (j =? i) = false *)
        left. apply theta_d_b.
        rewrite Hj in H.
        auto.
    + (* Hi0: (i0 =? i) = false *)
      rewrite Hi0.
      unfold update in H.
      rewrite Hi0 in H.
      assert (Hj: (j =? i) = true \/ (j =? i) = false).
        case (j =? i). auto. auto.
      destruct Hj as [Hj | Hj].
      * (* Hj: (j =? i) = true *)
        rewrite Hj.
        rewrite Hj in H.
        apply theta_d_b. assumption.
      * (* Hj: (j =? i) = false *)
        rewrite Hj.
        rewrite Hj in H.
        apply theta_gamma. assumption.
  - (* H: after gamma b i (X i0) (X j) *)
    unfold update.    
    assert (Hi0: (i0 =? i) = true \/ (i0 =? i) = false).
      case (i0 =? i). auto. auto.
    destruct Hi0 as [Hi0 | Hi0].
    + (* Hi0: (i0 =? i) = true *)
      rewrite Hi0.
      unfold after in H.
      rewrite Hi0 in H.
      destruct H as [bj | ji].
        apply theta_d_b in bj.
        rewrite bj.
        case (j =? i). reflexivity. reflexivity.
      rewrite ji.
      rewrite Nat.eqb_refl.
      reflexivity.
    + (* Hi0: (i0 =? i) = false *)
      rewrite Hi0.
      unfold after in H.
      rewrite Hi0 in H.
      assert (Hj: (j =? i) = true \/ (j =? i) = false).
        case (j =? i). auto. auto.
      destruct Hj as [Hj | Hj].
      * (* Hj: (j =? i) = true *)
        rewrite Hj.
        rewrite Hj in H.
        apply theta_d_b. assumption.
      * (* Hj: (j =? i) = false *)      
        rewrite Hj.
        rewrite Hj in H.
        apply theta_gamma. assumption.
Qed.

End TypeGuaranteesApplicability.

Section Uniqueness.

Variable theta : assignment.
Variables gamma gamma' : Rel.
Hypothesis gamma_equiv  : is_equiv_rel gamma.
Hypothesis gamma'_equiv : is_equiv_rel gamma'.

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

End Uniqueness.


Section AfterRWellDefined.

Variable j : nat.
Variable phi : Rel.
Hypothesis phi_equiv : is_equiv_rel phi.
Hypothesis lat_phi_models_b : lat phi |= b.

Lemma afterR_well_defined :
  ~((exists l1, phi (X j) (X' l1) /\ b l1) /\
     exists l2, ~(phi (X j) (X' l2) <-> b l2)).
Proof.
  destruct phi_equiv as [eqref [eqsym eqtran]].
  intros [[l1 [pjl1 bl1]] [l2 H2]].
  apply lat_phi_models_b in bl1.
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
  (exists l1, phi (X j) (X' l1) /\ b l1) ->
   forall l2, phi (X j) (X' l2) <-> b l2.
Proof.
  intros el1 l2.
  destruct phi_equiv as [_ [eqsym eqtran]].
  destruct el1 as [l1 [pjl1 bl1]].
  apply lat_phi_models_b in bl1.
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
  (exists l1, ~ (phi (X j) (X' l1) <-> b l1)) ->
   forall l2, ~ (phi (X j) (X' l2) /\ b l2).
Proof.
  intros el1 l2 [pjl2 bl2].
  destruct phi_equiv as [_ [eqsym eqtran]].
  apply lat_phi_models_b in bl2.
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

End AfterRWellDefined.

End EquivRel.
