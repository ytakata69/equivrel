Require Import Nat Arith.

(* data words *)

Definition Sigma := nat.
Parameter D : Set.  (* a data domain *)
Definition data_word := nat -> (Sigma * D)%type.

(* LTL syntax *)

Definition register := nat.

Inductive ltl_atom :=
  | tt : ltl_atom
  | MATCH : register -> ltl_atom
  | p : Sigma -> ltl_atom  (* an atomic proposition *)
  .

Inductive ltl :=
  | pos : ltl_atom -> ltl  (* a positive literal *)
  | neg : ltl_atom -> ltl  (* a negative literal *)
  | X : ltl -> ltl
  | F : ltl -> ltl
  | STORE : register -> ltl -> ltl
  | OR : ltl -> ltl -> ltl
  .

Notation "'↓' r , phi" := (STORE r phi) (at level 200).
Notation "'↑' r" := (MATCH r) (at level 75).
Notation "a '.\/' b" := (OR a b) (at level 85, right associativity).
Notation  "'[' a ']'" := (pos a).
Notation "'~[' a ']'" := (neg a).

(* example formulas *)
(*
Check (STORE 1 (X (OR (neg (p 1)) (OR (pos (p 2)) (pos (↑ 1)))))).
Check ( ↓1, X (~[p 1] .\/   [p 2] .\/ [↑1])).
Check ((↓1, X (~[p 1] .\/ F [p 2]) .\/ F [↑1]) .\/ F (X [p 1])).
*)

(* semantics *)

Definition valuation := register -> D.

Definition update
  (v : valuation) (i : register) (d : D) : valuation :=
  fun (r : register) => if r =? i then d else v r.

Definition models_atom
  (sigma : data_word) (i : nat) (v : valuation) (atom : ltl_atom)
  : Prop :=
  match atom with
  | tt  => True
  | p a => fst (sigma i) = a
  | ↑ r => snd (sigma i) = v r
  end.

Fixpoint models
  (sigma : data_word) (i : nat) (v : valuation) (phi : ltl)
  : Prop :=
  match phi with
  | pos atom =>   models_atom sigma i v atom
  | neg atom => ~ models_atom sigma i v atom
  | X phi' => models sigma (S i) v phi'
  | F phi' => exists j : nat, i <= j /\ models sigma j v phi'
  | (↓ r, phi') => models sigma i (update v r (snd (sigma i))) phi'
  | phi1 .\/ phi2 => models sigma i v phi1 \/ models sigma i v phi2
  end.

Notation "'(' sigma ',' i '|=' v ',' phi ')'"
  := (models sigma i v phi).

(* definition of equality of two ltl formulas *)
Axiom ltl_extensionality :
  forall phi1 phi2 : ltl,
    (forall sigma i v, (sigma, i |= v, phi1) <-> (sigma, i |= v, phi2))
    -> phi1 = phi2.

Axiom valuation_extensionality :
  forall v1 v2 : valuation,
    (forall r, v1 r = v2 r) -> v1 = v2.

(* an auxiliary predicate *)

Fixpoint contains_match
  (r : register) (phi : ltl) : Prop
  :=
  match phi with
  | pos (↑ r') => r' = r
  | neg (↑ r') => r' = r
  | pos _  | neg _ => False
  | X phi'         => contains_match r phi'
  | F phi'         => contains_match r phi'
  | (↓ r', phi')   => contains_match r phi'
  | phi1 .\/ phi2  => contains_match r phi1 \/ contains_match r phi2
  end.

(* equivalent transformations *)

Lemma store_match_equals_tt :
  forall r : nat, (↓ r, [↑ r]) = [tt].
Proof.
  intros r.
  apply ltl_extensionality.
  intros sigma i v.
  unfold models; unfold models_atom.
  unfold update.
  rewrite <- beq_nat_refl.
  split; intros H; trivial.
Qed.

Lemma store_neg_match_equals_ff :
  forall r : nat, (↓ r, ~[↑ r]) = ~[tt].
Proof.
  intros r.
  apply ltl_extensionality.
  intros sigma i v.
  unfold models; unfold models_atom.
  unfold update.
  rewrite <- beq_nat_refl.
  split; intros H; contradiction.
Qed.


Lemma distr_X_over_OR :
  forall phi1 phi2,
    (X (phi1 .\/ phi2)) = (X phi1 .\/ X phi2).
Proof.
  intros phi1 phi2.
  apply ltl_extensionality.
  intros sigma i v.
  split; intros H.
- destruct H as [H | H].
+ left; assumption.
+ right; assumption.
- destruct H as [H | H].
+ left; assumption.
+ right; assumption.
Qed.

Lemma distr_F_over_OR :
  forall phi1 phi2,
    (F (phi1 .\/ phi2)) = (F phi1 .\/ F phi2).
Proof.
  intros phi1 phi2.
  apply ltl_extensionality.
  intros sigma i v.
  split; intros H.
- destruct H as [j [ij [H | H]]].
+ left.
  exists j.
  split; assumption.
+ right.
  exists j.
  split; assumption.
- destruct H as [H | H];
  destruct H as [j [ij H]].
+ unfold models.
  exists j.
  split; auto.
+ unfold models.
  exists j.
  split; auto.
Qed.

Lemma distr_STORE_over_OR :
  forall phi1 phi2 r,
    (↓ r, (phi1 .\/ phi2)) = ((↓ r, phi1) .\/ (↓ r, phi2)).
Proof.
  intros phi1 phi2 r.
  apply ltl_extensionality.
  intros sigma i v.
  split; intros H.
- destruct H as [H | H];
  unfold models; auto.
- destruct H as [H | H];
  unfold models; auto.
Qed.


Lemma FX_equals_XF :
  forall phi, (F (X phi)) = (X (F phi)).
Proof.
  intros phi.
  apply ltl_extensionality.
  intros sigma i v.
  split; intros H.
- destruct H as [j [ij H]].
  exists (S j).
  split.
    apply le_n_S; assumption.
  assumption.
- destruct H as [j [sij H]].
  exists (pred j).
  split.
    apply Nat.le_succ_le_pred; assumption.
  unfold models.
  rewrite <- (S_pred j i).
    assumption.
  auto. (* i < j *)
Qed.


Lemma F_is_idempotent :
  forall phi, (F (F phi)) = (F phi).
Proof.
  intros phi.
  apply ltl_extensionality.
  intros sigma i v.
  split; intros H.
- destruct H as [j [ij [j0 [jj0 H]]]].
  exists j0.
  split.
+ apply (Nat.le_trans _ j _); assumption.
+ assumption.
- destruct H as [j [ij H]].
  exists i.
  split.
    trivial. (* i <= i *)
  exists j.
  split; assumption.
Qed.

Lemma update_is_idempotent :
  forall v r d,
    update (update v r d) r d = update v r d.
Proof.
  intros v r d.
  apply valuation_extensionality.
  intros r0.
  unfold update.
  case (r0 =? r); trivial.
Qed.

Lemma STORE_is_idempotent :
  forall phi r, (↓ r, (↓ r, phi)) = (↓ r, phi).
Proof.
  intros phi r.
  apply ltl_extensionality.
  intros sigma i v.
  unfold models.
  rewrite update_is_idempotent.
  reflexivity.
Qed.


Lemma redundant_STORE_core :
  forall r phi,
  ~ contains_match r phi ->
    forall sigma i v d,
      (sigma, i |= v, phi)
      <-> (sigma, i |= update v r d, phi).
Proof.
  intros r phi;
  intros Hcon.
  induction phi.
- intros sigma i v d.
  destruct l.
+ reflexivity.
+ unfold models; unfold models_atom.
  unfold update.
  apply Nat.eqb_neq in Hcon.
  rewrite Hcon.
  reflexivity.
+ reflexivity.
- intros sigma i v d.
  destruct l.
+ reflexivity.
+ unfold models; unfold models_atom.
  unfold update.
  apply Nat.eqb_neq in Hcon.
  rewrite Hcon.
  reflexivity.
+ reflexivity.

- assert (Hcon': ~ contains_match r phi).
  { intros H; apply Hcon; apply H. }
  intros sigma i v d.
  assert (IH := (IHphi Hcon' sigma (S i) v d));
  clear IHphi Hcon.
  split; intros H;
  apply IH; apply H.

- assert (Hcon': ~ contains_match r phi).
  { intros H; apply Hcon; apply H. }
  intros sigma i v d.
  split; intros H.
+ destruct H as [j [ij H]].
  assert (IH := (IHphi Hcon' sigma j v d));
  clear IHphi Hcon.
  exists j.
  split.
    assumption.
  apply IH; assumption.
+ destruct H as [j [ij H]].
  assert (IH := (IHphi Hcon' sigma j v d));
  clear IHphi Hcon.
  exists j.
  split.
    assumption.
  apply IH; assumption.

- assert (Hcon': ~ contains_match r phi).
  { intros H; apply Hcon; apply H. }
  intros sigma i v d.
  case_eq (r0 =? r); intros r0r.
+ assert (Hup: forall d', update (update v r d') r d' = update (update v r d) r d').
  {
    intros d'.
    apply valuation_extensionality.
    intros r1.
    unfold update.
    case (r1 =? r); reflexivity.
  }
  apply beq_nat_true in r0r.
  rewrite r0r.
  assert (IH := (IHphi Hcon' sigma i (update v r (snd (sigma i))) (snd (sigma i))));
  clear IHphi Hcon.
  rewrite (Hup (snd (sigma i))) in IH.
  split; intros H;
  apply IH; apply H.
+ assert (Hup: r0 <> r -> forall d', update (update v r0 d') r d = update (update v r d) r0 d').
  {
    intros H d'.
    apply valuation_extensionality.
    intros r1.
    unfold update.
    case_eq (r1 =? r); case_eq (r1 =? r0); intros r1r0 r1r.
  - apply beq_nat_true in r1r0.
    apply beq_nat_true in r1r.
    rewrite r1r0 in r1r.
    elim H; assumption.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  }
  apply beq_nat_false in r0r.
  assert (IH := (IHphi Hcon' sigma i (update v r0 (snd (sigma i))) d));
  clear IHphi Hcon.
  rewrite (Hup r0r (snd (sigma i))) in IH.
  split; intros H;
  apply IH; apply H.

- assert (Hcon': ~ (contains_match r phi1 \/ contains_match r phi2)).
  { intros H; apply Hcon; apply H. }
  apply Decidable.not_or_iff in Hcon'.
  destruct Hcon' as [Hcon1 Hcon2].
  intros sigma i v d.
  assert (IH1 := (IHphi1 Hcon1 sigma i v d));
  assert (IH2 := (IHphi2 Hcon2 sigma i v d));
  clear IHphi1 IHphi2 Hcon.
  split; intros H.
+ destruct H as [H | H].
* left; apply IH1; apply H.
* right; apply IH2; apply H.
+ destruct H as [H | H].
* left; apply IH1; apply H.
* right; apply IH2; apply H.
Qed.

Lemma redundant_STORE :
  forall phi r,
    ~ contains_match r phi -> (↓ r, phi) = phi.
Proof.
  intros phi r Hcon.
  apply ltl_extensionality.
  intros sigma i v.
  induction phi.

- destruct l.
+ reflexivity.
+ unfold contains_match in Hcon.
  apply Nat.eqb_neq in Hcon.
  unfold models; unfold models_atom.
  unfold update.
  rewrite Hcon.
  reflexivity.
+ reflexivity.

- destruct l.
+ reflexivity.
+ unfold contains_match in Hcon.
  apply Nat.eqb_neq in Hcon.
  unfold models; unfold models_atom.
  unfold update.
  rewrite Hcon.
  reflexivity.
+ reflexivity.

- split; intros H.
+ apply (redundant_STORE_core _ _ Hcon _ _ v _) in H.
  assumption.
+ apply (redundant_STORE_core _ _ Hcon _ _ v _).
  assumption.
- split; intros H.
+ apply (redundant_STORE_core _ _ Hcon _ _ v _) in H.
  assumption.
+ apply (redundant_STORE_core _ _ Hcon _ _ v _).
  assumption.
- split; intros H.
+ apply (redundant_STORE_core _ _ Hcon _ _ v _) in H.
  assumption.
+ apply (redundant_STORE_core _ _ Hcon _ _ v _).
  assumption.
- split; intros H.
+ apply (redundant_STORE_core _ _ Hcon _ _ v _) in H.
  assumption.
+ apply (redundant_STORE_core _ _ Hcon _ _ v _).
  assumption.
Qed.
