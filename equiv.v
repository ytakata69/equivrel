(* sketch on equivalence relation *)

Require Import Nat Arith.EqNat.

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

Definition lat (phi : Rel) : Rel :=
  fun xi xj : register =>
    match xi, xj with
    | (X i), (X j) => phi (X' i) (X' j)
    | x, y => x = y
    end.

Definition former (phi : Rel) : Rel :=
  fun xi xj : register =>
    match xi, xj with
    | (X i), (X j) => phi (X i) (X j)
    | x, y => x = y
    end.

Definition inv (phi : Rel) (i : nat) : guard :=
  fun l : nat => phi (X l) (X' i).

Definition after (gamma : Rel) (b : guard) (i : nat) : Rel :=
  fun xj xl : register =>
    match xj, xl with
    | (X j), (X l) => if j =? i then b l \/ l = i else
                      if l =? i then b j          else gamma (X j) (X l)
    | x, y => x = y
    end.

Definition afterR (phi : Rel) (b : guard) (i : nat) : Rel -> Prop :=
  fun phi' : Rel =>
    former phi' = former phi /\
    lat phi' = after (lat phi) b i /\
    (forall j l, (phi (X j) (X' l) /\ b l -> phi' (X j) (X' i)) /\
              (~ (phi (X j) (X' l) <-> b l) -> ~ phi' (X j) (X' i))) /\
    forall j l, l <> i -> (phi (X j) (X' l) <-> phi' (X j) (X' l)).

Definition afterL (phi : Rel) (i : nat) : Rel :=
  fun xl xj : register =>
    match xl, xj with
    | (X  l), (X  j) => (after (former phi) (inv phi i) i) xl xj
    | (X' l), (X' j) => phi xl xj
    | (X  l), (X' j) => if l =? i then phi (X' i) (X' j) else phi xl xj
    | (X' l), (X  j) => if j =? i then phi (X' i) (X' l) else phi xl xj
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
    (forall x y, phi x y <-> phi' x y) -> phi = phi'.

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
Instance two_assignments_model_rel : Models (assignment * assignment) Rel :=
  { models pair phi :=
      match pair with
      | (theta, theta') =>
          forall i j, (theta  i = theta  j <-> phi (X  i) (X  j)) /\
                      (theta' i = theta' j <-> phi (X' i) (X' j)) /\
                      (theta  i = theta' j <-> phi (X  i) (X' j)) /\
                      (theta' i = theta  j <-> phi (X' i) (X  j))
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

Section AfterRExists.

Variable  d : D.
Variables theta theta' : assignment.
Variables phi phi' : Rel.
Hypothesis phi_equiv  : is_equiv_rel phi.
Hypothesis phi'_equiv : is_equiv_rel phi'.

Lemma afterR_exists_core' :
  (theta, d) |= b ->
    forall j l, (theta' j = theta l /\ b l -> theta' j = d) /\
                ( ~ (theta' j = theta l <-> b l) -> theta' j <> d).
Proof.
  intros theta_d_b.
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

Lemma afterR_exists_core :
  forall i : nat,
    (theta', theta) |= phi ->
    (theta', update theta i d) |= phi' ->
    (theta, d) |= b ->
      forall j l, (phi (X j) (X' l) /\ b l -> phi' (X j) (X' i)) /\
                  ( ~ (phi (X j) (X' l) <-> b l) -> ~ phi' (X j) (X' i)).
Proof.
  intros i.
  intros theta_phi theta_phi' theta_d_b.
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

Lemma afterR_exists :
  forall i : nat,
    (theta', theta) |= phi ->
    (theta', update theta i d) |= phi' ->
    (theta, d) |= b ->
      afterR phi b i phi'.
Proof.
  intros i theta_phi theta_phi' theta_d_b.
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
  { apply (afterR_exists_core _ theta_phi theta_phi' theta_d_b). }
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

End AfterRExists.

Section AfterLExists.

Variable  d : D.
Variables theta theta' : assignment.
Variables phi : Rel.
Hypothesis phi_equiv : is_equiv_rel phi.

Lemma afterL_exists :
  forall j : nat,
    theta j = d ->
    (theta', theta) |= phi ->
      (theta', d) |= inv phi j /\
      ((update theta' j d), theta) |= afterL phi j.
Proof.
  intros j theta_j_d theta_phi.
  split.
  - (* (theta', d) |= inv phi j *)
    unfold models. unfold assignmentD_models_guard.
    intros i.
    split; intros H.
    { unfold inv.
      apply theta_phi.
      rewrite H. auto. }
    rewrite <- theta_j_d.
    apply theta_phi.
    apply H.
  - (* ((update theta' j d), theta) |= afterL phi j *)
    unfold models. unfold two_assignments_model_rel.
    split. (* 4 cases *)
    { (* update theta' j d i = update theta' j d j0
         <-> afterL phi j (X i) (X j0) *)
      split; intros H.
      * (* -> *)
        unfold afterL. unfold after.
        case_eq (i =? j); intros ij.
        -- (* ij: (i =? j) = true *)
           unfold inv.
           unfold update in H.
           rewrite ij in H.
           case_eq (j0 =? j); intros j0j.
             right. apply beq_nat_eq. auto.
           rewrite j0j in H.
           left.
           apply theta_phi.
           rewrite theta_j_d. auto.
        -- (* ij: (i =? j) = false *)
           unfold update in H.
           rewrite ij in H.
           case_eq (j0 =? j); intros j0j.
           { (* j0j: (j0 =? j) = true *)
             rewrite j0j in H.
             unfold inv.
             apply theta_phi.
             rewrite theta_j_d. auto. }
           { (* j0j: (j0 =? j) = false *)
             rewrite j0j in H.
             unfold former.
             apply theta_phi. assumption. }
      * (* <- *)
        unfold update.
        unfold afterL in H.
        unfold after in H.
        case_eq (i =? j); intros ij.
        -- (* ij: (i =? j) = true *)
           rewrite ij in H.
           destruct H as [H | H].
           { unfold inv in H.
             apply theta_phi in H.
             rewrite H.
             rewrite theta_j_d.
             case (j0 =? j). trivial. trivial. }
           { rewrite H.
             rewrite <- beq_nat_refl. trivial. }
        -- (* ij: (i =? j) = false *)
           rewrite ij in H.
           case_eq (j0 =? j); intros j0j.
           { (* j0j: (j0 =? j) = true *)
             rewrite j0j in H.
             unfold inv in H.
             apply theta_phi in H.
             rewrite theta_j_d in H. assumption. }
           { (* j0j: (j0 =? j) = false *)
             rewrite j0j in H.
             unfold former in H.
             apply theta_phi in H. assumption. }
    }
    split. (* last 3 cases *)
    { (* theta i = theta j0 <-> afterL phi j (X' i) (X' j0) *)
      split; intros H.
      * (* -> *)
        unfold afterL.
        apply theta_phi in H.
        assumption.
      * (* <- *)
        unfold afterL in H.
        apply theta_phi.
        assumption.
    }
    split. (* last 2 cases *)
    { (* update theta' j d i = theta j0 <-> afterL phi j (X i) (X' j0) *)
      split; intros H.
      * (* -> *)
        unfold afterL.
        case_eq (i =? j); intros ij.
        { apply theta_phi.
          rewrite theta_j_d.
          unfold update in H.
          rewrite ij in H.
          assumption. }
        { apply theta_phi.
          unfold update in H.
          rewrite ij in H.
          assumption. }
      * (* <- *)
        unfold afterL in H.
        unfold update.
        case_eq (i =? j); intros ij.
        { rewrite ij in H.
          apply theta_phi in H.
          rewrite theta_j_d in H.
          assumption. }
        { rewrite ij in H.
          apply theta_phi in H.
          assumption. }
    }
    { (* theta i = update theta' j d j0 <-> afterL phi j (X' i) (X j0) *)
      split; intros H.
      * (* -> *)
        unfold afterL.
        case_eq (j0 =? j); intros j0j.
        { apply theta_phi.
          rewrite theta_j_d.
          unfold update in H.
          rewrite j0j in H. auto. }
        { apply theta_phi.
          unfold update in H.
          rewrite j0j in H.
          assumption. }
      * (* <- *)
        unfold afterL in H.
        unfold update.
        case_eq (j0 =? j); intros j0j.
        { rewrite j0j in H.
          apply theta_phi in H.
          rewrite theta_j_d in H. auto. }
        { rewrite j0j in H.
          apply theta_phi in H.
          assumption. }
    }
Qed.

End AfterLExists.

End EquivRel.
